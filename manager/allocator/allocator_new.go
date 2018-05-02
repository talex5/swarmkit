package allocator

import (
	"context"
	"sync"
	"time"

	"github.com/docker/docker/pkg/plugingetter"

	"github.com/docker/swarmkit/manager/allocator/network"
	"github.com/docker/swarmkit/manager/allocator/network/errors"

	"github.com/docker/swarmkit/api"
	"github.com/docker/swarmkit/log"
	"github.com/docker/swarmkit/manager/state/store"
	"github.com/docker/swarmkit/protobuf/ptypes"
)

const (
	AllocatedStatusMessage = "pending task scheduling"

	maxBatchInterval = 500 * time.Millisecond
)

type NewAllocator struct {
	store   *store.MemoryStore
	network network.Allocator

	pendingMu       sync.Mutex
	pendingNetworks map[string]struct{}
	pendingTasks    map[string]struct{}
	pendingNodes    map[string]struct{}
	// no need for a pending services map. we will allocate services lazily
	// before we allocate a task
}

func NewNew(store *store.MemoryStore, pg plugingetter.PluginGetter) *NewAllocator {
	a := &NewAllocator{
		store:           store,
		network:         network.NewAllocator(pg),
		pendingNetworks: map[string]struct{}{},
		pendingTasks:    map[string]struct{}{},
		pendingNodes:    map[string]struct{}{},
	}
	return a
}

func (a *NewAllocator) Run(ctx context.Context) error {
	// General overview of how this function works:
	//
	// Run is a shim between the asynchronous store interface, and the
	// synchronous allocator interface. It uses a map to keep track of which
	// objects have outstanding allocations to perform, and uses a goroutine to
	// synchronize reads and writes with this map and allow it to function as a
	// a source of work.
	//
	// The first thing it does is read the object store and pass all of the
	// objects currently available to the network allocator. The network
	// allocator's restore function will add all allocated objects to the local
	// state so we can proceed with new allocations.
	//
	// It thens adds all objects in the store to the working set, so that any
	// objects currently in the store that aren't allocated can be.
	//
	// Then, it starts up two major goroutines:
	//
	// The first is the goroutine that gets object ids out of the work pile and
	// performs allocation on them. If the allocation succeeds, it writes that
	// allocation to raft. If it doesn't succeed, the object is added back to
	// the work pile to be serviced later
	//
	// The second is the goroutine that services events off the event queue. It
	// reads incoming store events and grabs just the ID and object type, and
	// adds that to the work pile. We only deal with the ID, not the full
	// object because the full object may have changed since the event came in
	// The exception in this event loop is for deallocations. When an object is
	// deleted, the event we recieve is our last chance to deal with that
	// object. In that case, we immediately call into Deallocate.

	ctx, c := context.WithCancel(ctx)
	// defer canceling the context, so that anything waiting on it will exit
	// when this routine exits.
	defer c()
	ctx = log.WithModule(ctx, "allocator")
	ctx = log.WithField(ctx, "method", "(*NewAllocator).Run")
	log.G(ctx).Info("starting network allocator")

	// we want to spend as little time as possible in transactions, because
	// transactions stop the whole cluster, so we're going to grab the lists
	// and then get out
	var (
		networks []*api.Network
		services []*api.Service
		tasks    []*api.Task
		nodes    []*api.Node
	)
	watch, cancel, err := store.ViewAndWatch(a.store,
		func(tx store.ReadTx) error {
			var err error
			networks, err = store.FindNetworks(tx, store.All)
			if err != nil {
				// TODO(dperny): handle errors
			}
			services, err = store.FindServices(tx, store.All)
			if err != nil {
				// TODO(dperny): handle errors
			}
			tasks, err = store.FindTasks(tx, store.All)
			if err != nil {
				// TODO(dperny): handle errors
			}
			nodes, err = store.FindNodes(tx, store.All)
			if err != nil {
				// TODO
			}

			return nil
		},
		api.EventCreateNetwork{},
		api.EventUpdateNetwork{},
		api.EventDeleteNetwork{},
		api.EventCreateService{},
		api.EventUpdateService{},
		api.EventDeleteService{},
		api.EventCreateTask{},
		api.EventUpdateTask{},
		api.EventDeleteTask{},
		api.EventCreateNode{},
		api.EventUpdateNode{},
		api.EventDeleteNode{},
	)
	if err != nil {
		// TODO(dperny): error handling
		return err
	}

	// set up a routine to cancel the event stream when the context is canceled
	go func() {
		select {
		case <-ctx.Done():
			log.G(ctx).Info("context done, canceling the event stream")
			cancel()
		}
	}()

	// now restore the local state
	log.G(ctx).Info("restoring local network allocator state")
	if err := a.network.Restore(networks, services, tasks, nodes); err != nil {
		// TODO(dperny): handle errors
		log.G(ctx).WithError(err).Error("error restoring local network allocator state")
	}

	// allocate all of the store in its current state. don't bother with locks
	// because right now we're the only game in town
	for _, network := range networks {
		a.pendingNetworks[network.ID] = struct{}{}
	}
	for _, node := range nodes {
		a.pendingNodes[node.ID] = struct{}{}
	}
	for _, task := range tasks {
		a.pendingTasks[task.ID] = struct{}{}
	}

	log.G(ctx).Info("processing all outstanding allocations in the store")

	a.processPendingAllocations(ctx)
	var wg sync.WaitGroup
	wg.Add(2)

	log.G(ctx).Info("starting event watch loop")
	// this goroutine handles incoming store events. all we need from the
	// events is the ID of what has been updated. by the time we service the
	// allocation, the object may have changed, so we don't save any other
	// information. we'll get to it later.
	go func() {
		defer wg.Done()
		// TODO(dperny): there is an outstanding issue with a deadlock that can
		// result from closing the store at the same time the callback watch is
		// canceled. This can cause the tests to deadlock
		for {
			select {
			case <-ctx.Done():
				return
			case event := <-watch:
				switch ev := event.(type) {
				case api.EventCreateNetwork, api.EventUpdateNetwork:
					// get the network
					var n *api.Network
					if e, ok := ev.(api.EventCreateNetwork); ok {
						n = e.Network
					} else {
						n = ev.(api.EventUpdateNetwork).Network
					}
					if n != nil {
						a.pendingMu.Lock()
						a.pendingNetworks[n.ID] = struct{}{}
						a.pendingMu.Unlock()
					}
				case api.EventDeleteNetwork:
					// if the user deletes  the network, we don't have to do any
					// store actions, and we can't return any errors. The network
					// is already gone, deal with it
					if ev.Network != nil {
						a.pendingMu.Lock()
						// when a network is deallocated, deallocate all nodes
						// TODO(dperny): don't access the store in this event
						// loop
						a.store.Update(func(tx store.Tx) error {
							nodes, err := store.FindNodes(tx, store.All)
							if err != nil {
								// TODO(dperny): better error handling
								return err
							}
							for _, node := range nodes {
								nwids := map[string]struct{}{}
								for _, attachment := range node.Attachments {
									if attachment.Network.ID != ev.Network.ID {
										nwids[attachment.Network.ID] = struct{}{}
									}
								}
								if err := a.network.AllocateNode(node, nwids); err != nil {
									if !errors.IsErrAlreadyAllocated(err) {
										// TODO(dperny): better error handling
										return err
									}
								}
								if err := store.UpdateNode(tx, node); err != nil {
									return err
								}
							}
							return nil
						})
						a.network.DeallocateNetwork(ev.Network)
						delete(a.pendingNetworks, ev.Network.ID)
						a.pendingMu.Unlock()
					}
				// case api.EventCreateService, api.EventUpdateService:
				//     the case for create and update services is not needed.
				//     we will lazy-allocate services. the reason for this is
				//     to guarantee that the latest version of the service is
				//     always allocated, and the task is always using the
				//     latest version of the service for allocation.
				case api.EventDeleteService:
					if ev.Service != nil {
						a.pendingMu.Lock()
						a.network.DeallocateService(ev.Service)
						a.pendingMu.Unlock()
					}
				case api.EventCreateTask, api.EventUpdateTask:
					var t *api.Task
					if e, ok := ev.(api.EventCreateTask); ok {
						t = e.Task
					} else {
						t = ev.(api.EventUpdateTask).Task
					}
					if t != nil {
						// updating a task may mean the task has entered a
						// terminal state. if it has, we will free its network
						// resources just as if we had deleted it.
						a.pendingMu.Lock()
						if t.Status.State >= api.TaskStateCompleted {
							a.network.DeallocateTask(t)
							// if the task was pending before now, remove it
							// because it no loger is
							delete(a.pendingTasks, t.ID)
						} else {
							a.pendingTasks[t.ID] = struct{}{}
						}
						a.pendingMu.Unlock()
					}
				case api.EventDeleteTask:
					if ev.Task != nil {
						a.pendingMu.Lock()
						a.network.DeallocateTask(ev.Task)
						delete(a.pendingTasks, ev.Task.ID)
						a.pendingMu.Unlock()
					}
				case api.EventCreateNode:
					if ev.Node != nil {
						a.pendingMu.Lock()
						a.pendingNodes[ev.Node.ID] = struct{}{}
						a.pendingMu.Unlock()
					}
				// case api.EventUpdateNode:
				//     we don't need the update node case because nothing about
				//     a node update will require reallocation.
				case api.EventDeleteNode:
					if ev.Node != nil {
						a.pendingMu.Lock()
						a.network.DeallocateNode(ev.Node)
						delete(a.pendingNodes, ev.Node.ID)
						a.pendingMu.Unlock()
					}
				}
			}
		}
	}()

	log.G(ctx).Info("starting batch processing loop")
	// allocations every 500 milliseconds
	batchTimer := time.NewTimer(maxBatchInterval)
	go func() {
		defer wg.Done()
		for {
			select {
			case <-ctx.Done():
				return
			case <-batchTimer.C:
				// TODO(dperny): probably not safe to check len without a lock
				// but whatever.
				if len(a.pendingNetworks)+len(a.pendingNodes)+len(a.pendingTasks) > 0 {
					// every batch interval, do all allocations and then reset the
					// timer to ready for the next batch
					a.processPendingAllocations(ctx)
				}
				batchTimer.Reset(maxBatchInterval)
			}
		}
	}()

	log.G(ctx).Info("allocator is up!")
	wg.Wait()
	log.G(ctx).Info("allocator is finished")
	defer log.G(ctx).Info("all defers exited")

	return nil
}

func (a *NewAllocator) processPendingAllocations(ctx context.Context) {
	ctx = log.WithField(ctx, "method", "(*NewAllocator).processPendingAllocations")
	a.pendingMu.Lock()
	defer a.pendingMu.Unlock()
	if err := a.store.Batch(func(batch *store.Batch) error {
		if len(a.pendingNetworks) > 0 {
			log.G(ctx).Infof("allocating %v networks", len(a.pendingNetworks))
		}
		for nwid := range a.pendingNetworks {
			ctx := log.WithField(ctx, "network.id", nwid)
			// don't actually return any errors from this function unless we
			// want to abort the batch
			if err := batch.Update(func(tx store.Tx) error {
				// get the most up-to-date information about the network
				network := store.GetNetwork(tx, nwid)
				// if we get back nil, the network may have been deleted, and
				// there's nothing to do
				if network == nil {
					log.G(ctx).Debug("network not found, probably deleted")
					return nil
				}
				if err := a.network.AllocateNetwork(network); err != nil {
					if errors.IsErrAlreadyAllocated(err) {
						log.G(ctx).Debug("network already allocated")
						delete(a.pendingNetworks, nwid)
						return nil
					}
					log.G(ctx).WithError(err).Error("network allocation failed")
					// if the error isn't a retryable error, we're going to
					// delete this from the pending allocations, because it
					// will never succeed
					if !errors.IsErrRetryable(err) {
						log.G(ctx).Error("network allocation error is fatal and this network will never succeed")
						delete(a.pendingNetworks, nwid)
					}
				}
				// log.G(ctx).Debug("network allocation succeeded")
				if err := store.UpdateNetwork(tx, network); err != nil {
					// TODO(dperny) better error handling here?
					return err
				}
				// if this is an overlay network, reallocate all of the nodes
				// (to attach them to this overlay)
				if network.DriverState != nil && network.DriverState.Name == "overlay" {
					log.G(ctx).Info("added an overlay network, reallocating all nodes")
					nodes, err := store.FindNodes(tx, store.All)
					if err != nil {
						// TODO(dperny): again, can we handle errors better?
						return err
					}
					for _, node := range nodes {
						a.pendingNodes[node.ID] = struct{}{}
					}
				}
				return nil
			}); err != nil {
				log.G(ctx).WithError(err).Error("batch update of network allocation failed")
			}
		}
		log.G(ctx).Info("finished allocating networks")

		if len(a.pendingTasks) > 0 {
			log.G(ctx).Infof("allocating %v tasks", len(a.pendingTasks))
		}
		for taskid := range a.pendingTasks {
			ctx := log.WithField(ctx, "task.id", taskid)
			if err := batch.Update(func(tx store.Tx) error {
				err := a.allocateTask(tx, taskid)
				if err != nil && !errors.IsErrAlreadyAllocated(err) {
					log.G(ctx).WithError(err).Error("task allocation failed")
				}
				// if the error is not a retriable error (or not an error at
				// all), or it is ErrAlreadyAllocated, then delete from pending
				// tasks.
				if !errors.IsErrRetryable(err) || errors.IsErrAlreadyAllocated(err) {
					delete(a.pendingTasks, taskid)
				}
				return nil
			}); err != nil {
				log.G(ctx).WithError(err).Error("error in batch update")
			}
		}
		log.G(ctx).Info("finished allocating tasks")

		if len(a.pendingNodes) > 0 {
			log.G(ctx).Infof("allocating %v nodes", len(a.pendingNodes))
		}
		// TODO(dperny): this is a really sloppy way of logging this once.
		var logged bool
		for nodeid := range a.pendingNodes {
			ctx := log.WithField(ctx, "node.id", nodeid)
			if err := batch.Update(func(tx store.Tx) error {
				networks, err := store.FindNetworks(tx, store.All)
				if err != nil {
					// TODO(dperny): better error handling
					return err
				}
				nwids := map[string]struct{}{}
				// add all overlay networks to the node
				for _, network := range networks {
					// using the driver state instead of the spec here means
					// we'll only request attachments for fully-allocated
					// networks
					if network.DriverState != nil && network.DriverState.Name == "overlay" {
						nwids[network.ID] = struct{}{}
					}
				}

				if !logged {
					log.G(ctx).Infof("allocating %v networks for nodes", len(nwids))
					logged = true
				}

				node := store.GetNode(tx, nodeid)
				err = a.network.AllocateNode(node, nwids)
				// if there is any error case other than already allocated, log
				// it
				if err != nil && !errors.IsErrAlreadyAllocated(err) {
					log.G(ctx).WithError(err).Error("error allocating node")
				}
				if !errors.IsErrRetryable(err) || errors.IsErrAlreadyAllocated(err) {
					delete(a.pendingNodes, nodeid)
				}
				// TODO(dperny): this is too verbose logging
				if errors.IsErrAlreadyAllocated(err) {
					log.G(ctx).Info("node is already fully allocated")
				}
				if err == nil {
					return store.UpdateNode(tx, node)
				}
				return nil
			}); err != nil {
				log.G(ctx).WithError(err).Error("error in batch update")
			}
		}
		log.G(ctx).Info("finished allocating nodes")
		log.G(ctx).Info("finished all allocations")
		return nil
	}); err != nil {
		log.G(ctx).WithError(err).Error("error processing pending allocations batch")
	}
}

func (a *NewAllocator) allocateTask(tx store.Tx, taskid string) error {
	task := store.GetTask(tx, taskid)
	if task == nil {
		return nil
	}
	if task.ServiceID != "" {
		service := store.GetService(tx, task.ServiceID)
		// nothing to do, task will be deleted soon
		if service == nil {
			return nil
		}
		err := a.network.AllocateService(service)
		if err != nil && !errors.IsErrAlreadyAllocated(err) {
			return err
		}
		if err == nil {
			if err := store.UpdateService(tx, service); err != nil {
				return err
			}
		}
	}
	err := a.network.AllocateTask(task)
	if errors.IsErrAlreadyAllocated(err) {
		return nil
	}
	if err != nil {
		return err
	}
	task.Status = api.TaskStatus{
		State:     api.TaskStatePending,
		Message:   AllocatedStatusMessage,
		Timestamp: ptypes.MustTimestampProto(time.Now()),
	}
	return store.UpdateTask(tx, task)
}

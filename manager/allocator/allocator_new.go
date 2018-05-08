package allocator

import (
	"context"
	"sync"
	"time"

	"github.com/docker/docker/pkg/plugingetter"
	metrics "github.com/docker/go-metrics"

	"github.com/docker/swarmkit/manager/allocator/network"
	"github.com/docker/swarmkit/manager/allocator/network/errors"

	"github.com/docker/swarmkit/api"
	"github.com/docker/swarmkit/log"
	"github.com/docker/swarmkit/manager/state/store"
	"github.com/docker/swarmkit/protobuf/ptypes"
)

const (
	// AllocatedStatusMessage is the message added to a task status after the
	// task is successfully allocated
	AllocatedStatusMessage = "pending task scheduling"

	maxBatchInterval = 500 * time.Millisecond
)

var (
	batchProcessingDuration metrics.Timer

	storeLockHeld    metrics.LabeledTimer
	allocatorActions metrics.LabeledTimer
)

func init() {
	ns := metrics.NewNamespace("swarmkit", "allocator", nil)

	allocatorActions = ns.NewLabeledTimer(
		"allocator_actions",
		"The number of seconds it takes the allocator to perform some action",
		"object", "action",
	)

	storeLockHeld = ns.NewLabeledTimer(
		"store_lock_held",
		"The number of seconds the allocator holds open store transactions",
		"object", "action",
	)

	batchProcessingDuration = ns.NewTimer(
		"batch_duration",
		"The number of seconds it takes to process a full batch of allocations",
	)

	metrics.Register(ns)
}

// NewAllocator is the top-level component controlling resource allocation for
// swarm objects
type NewAllocator struct {
	store   *store.MemoryStore
	network network.Allocator

	// fields that make running the allocator thread-safe.
	runOnce sync.Once

	// fields to make stopping the allocator possible and safe through the stop
	// method
	stop     chan struct{}
	stopped  chan struct{}
	stopOnce sync.Once

	pendingMu       sync.Mutex
	pendingNetworks map[string]struct{}
	pendingTasks    map[string]struct{}
	pendingNodes    map[string]struct{}
	// no need for a pending services map. we will allocate services lazily
	// before we allocate a task
}

// NewNew creates a NewAllocator object
func NewNew(store *store.MemoryStore, pg plugingetter.PluginGetter) *NewAllocator {
	a := &NewAllocator{
		store:           store,
		stop:            make(chan struct{}),
		stopped:         make(chan struct{}),
		network:         network.NewAllocator(pg),
		pendingNetworks: map[string]struct{}{},
		pendingTasks:    map[string]struct{}{},
		pendingNodes:    map[string]struct{}{},
	}
	return a
}

// Run starts this allocator, if it has not yet been started. The Allocator can
// only be run once.
func (a *NewAllocator) Run(ctx context.Context) error {
	// TODO(dperny): probably should not use the network allocator's
	// ErrBadState here but TBH it's more convenient then also importing, say,
	// fmt

	// initialize the variable err to be already started. this will get set to
	// some other value (or even nil) when the allocator's run function exits,
	// but any subsequent calls will not pass through the Once, and will return
	// this error
	err := errors.ErrBadState("allocator already started")
	a.runOnce.Do(func() {
		err = a.run(ctx)
		// close the stopped channel to indicate that the allocator has fully
		// exited.
		close(a.stopped)
	})
	return err
}

func (a *NewAllocator) run(ctx context.Context) error {
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
	// deleted, the event we receive is our last chance to deal with that
	// object. In that case, we immediately call into Deallocate.

	ctx, c := context.WithCancel(ctx)
	// defer canceling the context, so that anything waiting on it will exit
	// when this routine exits.
	defer c()
	ctx = log.WithModule(ctx, "allocator")
	ctx = log.WithField(ctx, "method", "(*NewAllocator).Run")
	log.G(ctx).Info("starting network allocator")

	// set up a goroutine for stopping the allocator from the Stop method. this
	// just cancels the context if that channel is closed.
	go func() {
		select {
		case <-ctx.Done():
		case <-a.stop:
			c()
		}
	}()

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
			log.G(ctx).Debug("context done, canceling the event stream")
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
	log.G(ctx).Info("finished processing all pending allocations")

	var wg sync.WaitGroup
	wg.Add(2)

	log.G(ctx).Debug("starting event watch loop")
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
						// when a network is deallocated, if it's an overlay
						// network, before we can deallocate it we have to
						// deallocate all of the attachments for its nodes.
						if ev.Network.DriverState != nil && ev.Network.DriverState.Name == "overlay" {
							// TODO(dperny): doing a store update in this event
							// loop is probably pretty much the worst thing I
							// can imagine doing for performance.
							a.store.Update(func(tx store.Tx) error {
								storeDone := metrics.StartTimer(storeLockHeld.WithValues("network", "deallocate"))
								defer storeDone()

								nodes, err := store.FindNodes(tx, store.All)
								if err != nil {
									// TODO(dperny): better error handling
									return err
								}
								for _, node := range nodes {
									a.pendingNodes[node.ID] = struct{}{}
									nwids := map[string]struct{}{}
									for _, attachment := range node.Attachments {
										if attachment.Network.ID != ev.Network.ID {
											nwids[attachment.Network.ID] = struct{}{}
										}
									}
									allocDone := metrics.StartTimer(allocatorActions.WithValues("network", "allocate"))
									err := a.network.AllocateNode(node, nwids)
									allocDone()
									if err != nil {
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
						}
						allocDone := metrics.StartTimer(allocatorActions.WithValues("network", "deallocate"))
						err := a.network.DeallocateNetwork(ev.Network)
						allocDone()
						if err != nil {
							log.G(ctx).WithError(err).WithField("network.id", ev.Network.ID).Error("error deallocating network")
						}
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
						allocDone := metrics.StartTimer(allocatorActions.WithValues("service", "deallocate"))
						err := a.network.DeallocateService(ev.Service)
						allocDone()
						if err != nil {
							log.G(ctx).WithField("service.id", ev.Service.ID).WithError(err).Error("error deallocating service")
						}
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
							allocDone := metrics.StartTimer(allocatorActions.WithValues("task", "deallocate"))
							err := a.network.DeallocateTask(t)
							allocDone()
							if err != nil {
								log.G(ctx).WithField("task.id", t.ID).WithError(err).Error("error deallocating task")
							}
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
						allocDone := metrics.StartTimer(allocatorActions.WithValues("task", "deallocate"))
						err := a.network.DeallocateTask(ev.Task)
						allocDone()
						if err != nil {
							log.G(ctx).WithField("task.id", ev.Task.ID).WithError(err).Error("error deallocating task")
						}
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

	log.G(ctx).Debug("starting batch processing loop")
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

	log.G(ctx).Info("allocator is started")
	wg.Wait()
	log.G(ctx).Info("allocator is finished")
	defer log.G(ctx).Debug("all defers exited")
	return nil
}

// Stop is a method that stops the running allocator, blocking until it has
// fully stopped
func (a *NewAllocator) Stop() {
	a.stopOnce.Do(func() {
		close(a.stop)
	})
	// NOTE(dperny) an un-selected channel read is inescapable and can result
	// in deadlocks, however, being able to escape this channel read with, say,
	// a context cancelation, would just lead to resource leaks of an already
	// deadlocked allocator, so the risk of a deadlock isn't that important
	<-a.stopped
}

func (a *NewAllocator) processPendingAllocations(ctx context.Context) {
	ctx = log.WithField(ctx, "method", "(*NewAllocator).processPendingAllocations")

	// we need to hold the lock the whole time we're allocating.
	a.pendingMu.Lock()
	defer a.pendingMu.Unlock()

	// collect metrics on how long each batch takes. start at timer after we
	// acquire the lock, and then defer the done call
	done := metrics.StartTimer(batchProcessingDuration)
	defer done()

	if err := a.store.Batch(func(batch *store.Batch) error {
		if len(a.pendingNetworks) > 0 {
			log.G(ctx).Debugf("allocating %v networks", len(a.pendingNetworks))
		}
		for nwid := range a.pendingNetworks {
			ctx := log.WithField(ctx, "network.id", nwid)
			// don't actually return any errors from this function unless we
			// want to abort the batch
			if err := batch.Update(func(tx store.Tx) error {
				// keep a timer of how long network allocation transactions
				// take
				batchDone := metrics.StartTimer(storeLockHeld.WithValues("network", "allocate"))
				defer batchDone()

				// get the most up-to-date information about the network
				network := store.GetNetwork(tx, nwid)
				// if we get back nil, the network may have been deleted, and
				// there's nothing to do
				if network == nil {
					log.G(ctx).Debug("network not found, probably deleted")
					return nil
				}
				// metrics on how long it takes to allocate a network
				allocDone := metrics.StartTimer(allocatorActions.WithValues("network", "allocate"))
				err := a.network.AllocateNetwork(network)
				allocDone()
				if err != nil {
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
					log.G(ctx).Debug("added an overlay network, reallocating all nodes")
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
		log.G(ctx).Debug("finished allocating networks")

		if len(a.pendingTasks) > 0 {
			log.G(ctx).Debugf("allocating %v tasks", len(a.pendingTasks))
		}
		for taskid := range a.pendingTasks {
			ctx := log.WithField(ctx, "task.id", taskid)
			if err := batch.Update(func(tx store.Tx) error {
				batchDone := metrics.StartTimer(storeLockHeld.WithValues("task", "allocate"))
				defer batchDone()

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
		log.G(ctx).Debug("finished allocating tasks")

		if len(a.pendingNodes) > 0 {
			log.G(ctx).Debugf("allocating %v nodes", len(a.pendingNodes))
		}
		// TODO(dperny): this is a really sloppy way of logging this once.
		var logged bool
		for nodeid := range a.pendingNodes {
			ctx := log.WithField(ctx, "node.id", nodeid)
			if err := batch.Update(func(tx store.Tx) error {
				batchDone := metrics.StartTimer(storeLockHeld.WithValues("node", "allocate"))
				defer batchDone()
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
					log.G(ctx).Debugf("allocating %v networks for nodes", len(nwids))
					logged = true
				}

				node := store.GetNode(tx, nodeid)
				// TODO(dperny): this block is part of docker/swarmkit#2621 and
				// should be uncommented when this code is rebased and includes
				// the test changes from that
				// we only allocate all overlay networks for windows nodes. if
				// a node is not a windows node, set the nwids map to "nil",
				// which will cause the allocator to only allocate the ingress
				// network.
				// if node.Description == nil || node.Description.Platform == nil || node.Description.Platform.OS != "windows" {
				//     nwids = nil
				// }
				allocDone := metrics.StartTimer(allocatorActions.WithValues("node", "allocate"))
				err = a.network.AllocateNode(node, nwids)
				allocDone()
				// there are a lot of if statements, but this is mostly complex
				// just to make logging behave a certain way

				// first, if there is an error that isn't ErrAlreadyAllocated,
				// then we log that; those errors are important
				if err != nil && !errors.IsErrAlreadyAllocated(err) {
					log.G(ctx).WithError(err).Error("error allocating node")
				}
				// next, if the error isn't retryable (which includes both no
				// error and ErrAlreadyAllocated), then we should remove the
				// node from the map so as not to try allocating it next batch
				if !errors.IsErrRetryable(err) {
					delete(a.pendingNodes, nodeid)
				}
				// next, if this is ErrAlreadyAllocated, log it at a debug
				// level. it's a mildly noteworthy event if we try to allocate
				// a node that is already fully allocated.
				if errors.IsErrAlreadyAllocated(err) {
					log.G(ctx).Debug("node is already fully allocated")
				}
				// finally, if there was no error at all, then we should update
				// the node object in the store.
				if err == nil {
					return store.UpdateNode(tx, node)
				}
				return nil
			}); err != nil {
				log.G(ctx).WithError(err).Error("error in batch update")
			}
		}
		log.G(ctx).Debug("finished allocating nodes")
		log.G(ctx).Debug("finished all allocations")
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
		allocDone := metrics.StartTimer(allocatorActions.WithValues("service", "allocate"))
		err := a.network.AllocateService(service)
		allocDone()
		if err != nil && !errors.IsErrAlreadyAllocated(err) {
			return err
		}
		if err == nil {
			if err := store.UpdateService(tx, service); err != nil {
				return err
			}
		}
	}

	allocDone := metrics.StartTimer(allocatorActions.WithValues("task", "allocate"))
	err := a.network.AllocateTask(task)
	allocDone()

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

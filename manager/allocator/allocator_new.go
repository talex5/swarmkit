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
		"object", "action", "lock_type",
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

	// pending objects are those which have not yet passed through the
	// allocator.
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
	ctx = log.WithModule(ctx, "newallocator")
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
							log.G(ctx).WithField("network.id", ev.Network.ID).Debug(
								"an overlay network was removed, deallocating it from nodes",
							)
							a.store.Update(func(tx store.Tx) error {
								storeDone := metrics.StartTimer(storeLockHeld.WithValues("network", "deallocate", "write"))
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
				a.pendingMu.Lock()
				total := len(a.pendingNetworks) + len(a.pendingNodes) + len(a.pendingTasks)
				a.pendingMu.Unlock()
				// we release the lock before checking the total, which is fine
				// because the worst case is something gets deleted and the
				// processPendingAllocations just jumps straight through
				if total > 0 {
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

	log.G(ctx).Debugf(
		"processing pending allocations. %v networks, %v nodes, %v tasks",
		len(a.pendingNetworks), len(a.pendingNodes), len(a.pendingTasks),
	)

	defer func() {
		log.G(ctx).Debugf(
			"finished processing pending allocations. retrying: %v networks, %v nodes, %v tasks",
			len(a.pendingNetworks), len(a.pendingNodes), len(a.pendingTasks),
		)
	}()

	// collect metrics on how long each batch of pending allocations takes.
	// start at timer after we acquire the lock, and then defer the done call.
	done := metrics.StartTimer(batchProcessingDuration)
	defer done()

	// overlayAllocated is a variable that tracks whether a new overlay network
	// has been allocated. If it is true, then regardless of which nodes are
	// currently pending, all nodes will need to be reallocated with the new
	// network. we will do this after network allocation, but before task
	// allocation, to avoid a case where
	overlayAllocated := false

	// capture the pending maps and reinitialize them, so they'll be clean
	// after this runs
	pendingNetworks := a.pendingNetworks
	a.pendingNetworks = map[string]struct{}{}
	pendingNodes := a.pendingNodes
	a.pendingNodes = map[string]struct{}{}
	pendingTasks := a.pendingTasks
	a.pendingTasks = map[string]struct{}{}
	// first, pending networks. open the store and grab all of the pending
	// networks. networks can't be updated, so we don't need to worry about a
	// race condition.

	// if no networks are pending, skip this block. this saves us the time it
	// takes to acquire the store lock
	if len(pendingNetworks) > 0 {
		// we'll need two slices. the first is to hold all of the networks we get
		// from the store. the second holds all of the successfully allocated
		// networks
		networks := make([]*api.Network, 0, len(pendingNetworks))
		allocatedNetworks := make([]*api.Network, 0, len(pendingNetworks))

		batchDone := metrics.StartTimer(storeLockHeld.WithValues("networks", "allocate", "read"))
		a.store.View(func(tx store.ReadTx) {
			for id := range pendingNetworks {
				// remove the network from the pending allocations. if something
				// fails and we need to retry, we'll add it back.
				nw := store.GetNetwork(tx, id)
				if nw == nil {
					log.G(ctx).WithField("network.id", id).Debug("network not found, probably deleted")
					continue
				}
				networks = append(networks, nw)
			}
		})
		batchDone()

		// now, allocate each network
		for _, network := range networks {
			ctx := log.WithField(ctx, "network.id", network.ID)
			allocDone := metrics.StartTimer(allocatorActions.WithValues("network", "allocate"))
			err := a.network.AllocateNetwork(network)
			allocDone()

			// error conditions from the allocator are numerous, but are
			// constrained to a few specific types, which we can completely cover.
			switch {
			case err == nil:
				// first, if no error occurred, then we can add this to the list of
				// networks we will commit
				allocatedNetworks = append(allocatedNetworks, network)
			case errors.IsErrAlreadyAllocated(err):
				// if the network is already allocated, there is nothing to do. log
				// that and do not add this network to the batch
				log.G(ctx).Debug("network already fully allocated")
			case errors.IsErrRetryable(err):
				// if the error is retryable, then we should log that error and
				// re-add this network to our pending networks
				log.G(ctx).WithError(err).Error("network could not be allocated, but will be retried")
				a.pendingNetworks[network.ID] = struct{}{}
			default:
				// default covers any other error case. specifically, error that
				// are not retryable. for these, we should fail and not re-add them
				// to the pending map. they will never succeed
				log.G(ctx).WithError(err).Error("network cannot be allocated")
			}
		}

		// again, if we haven't actually successfully allocated any networks,
		// we should skip this part to avoid holding the lock
		if len(allocatedNetworks) > 0 {
			batchDone = metrics.StartTimer(storeLockHeld.WithValues("network", "allocate", "write"))
			// now, batch update the networks we just allocated
			if err := a.store.Batch(func(batch *store.Batch) error {
				for _, network := range allocatedNetworks {
					if err := batch.Update(func(tx store.Tx) error {
						ctx := log.WithField(ctx, "network.id", network.ID)
						// first, get the network and make sure it still exists
						currentNetwork := store.GetNetwork(tx, network.ID)
						if currentNetwork == nil {
							log.G(ctx).WithField("network.id", network.ID).Debugf("network was deleted after allocation but before commit")
							// if the current network is nil, then the network was
							// deleted and we should deallocate it.
							a.network.DeallocateNetwork(network)
						}
						if err := store.UpdateNetwork(tx, network); err != nil {
							return err
						}
						// if the network is successfully updated, check if
						// it's an overlay network. if so, set the
						// overlayAllocated flag so we reallocate nodes
						if network.DriverState != nil && network.DriverState.Name == "overlay" {
							log.G(ctx).Info("an overlay network was allocated, reallocating nodes")
							overlayAllocated = true
						}
						return nil
					}); err != nil {
						log.G(ctx).WithError(err).Error("error writing network to store")
					}
				}
				return nil
			}); err != nil {
				log.G(ctx).WithError(err).Error("error committing allocated networks")
			}
			batchDone()
		}
	}

	// next, allocate pending nodes, if there are any, or if an overlay network
	// has been allocated
	if overlayAllocated || len(pendingNodes) > 0 {
		// nodes is the set of node objects we'll allocate
		var nodes []*api.Node

		// networks is a set of all overlay networks currently in use
		overlayNetworks := map[string]struct{}{}

		readTxDone := metrics.StartTimer(storeLockHeld.WithValues("node", "allocate", "read"))
		a.store.View(func(tx store.ReadTx) {
			if overlayAllocated {
				var err error
				nodes, err = store.FindNodes(tx, store.All)
				if err != nil {
					// i don't know what to do here
				}
			} else {
				nodes = make([]*api.Node, 0, len(pendingNodes))
				for id := range pendingNodes {
					node := store.GetNode(tx, id)
					if node == nil {
						log.G(ctx).WithField("node.id", id).Debug("pending node not in store, probably deleted")
						continue
					}
					nodes = append(nodes, node)
				}
			}

			// now, get all overlay network IDs that are in use, so we can
			// allocate them to the nodes
			networks, err := store.FindNetworks(tx, store.All)
			if err != nil {
				// TODO(dperny): we can't actually proceed if there is an error,
				// because then we might deallocate all nodes' attachments
			}
			for _, network := range networks {
				if network.DriverState != nil && network.DriverState.Name == "overlay" {
					overlayNetworks[network.ID] = struct{}{}
				}
			}
		})
		readTxDone()

		// make space for the successfully allocated nodes
		allocatedNodes := make([]*api.Node, 0, len(nodes))

		for _, node := range nodes {
			ctx := log.WithField(ctx, "node.id", node.ID)
			allocDone := metrics.StartTimer(allocatorActions.WithValues("node", "allocate"))
			err := a.network.AllocateNode(node, overlayNetworks)
			allocDone()

			switch {
			case err == nil:
				// first, if no error occurred, then we can add this to the list of
				// networks we will commit
				allocatedNodes = append(allocatedNodes, node)
			case errors.IsErrAlreadyAllocated(err):
				// if the network is already allocated, there is nothing to do. log
				// that and do not add this network to the batch
				log.G(ctx).Debug("node already fully allocated")
			case errors.IsErrRetryable(err):
				// if the error is retryable, then we should log that error and
				// re-add this network to our pending networks
				log.G(ctx).WithError(err).Error("node could not be allocated, but will be retried")
				a.pendingNodes[node.ID] = struct{}{}
			default:
				// default covers any other error case. specifically, error that
				// are not retryable. for these, we should fail and not re-add them
				// to the pending map. they will never succeed
				log.G(ctx).WithError(err).Error("node cannot be allocated")
			}
		}

		// if any nodes successfully allocated, commit them
		if len(allocatedNodes) > 0 {
			if err := a.store.Batch(func(batch *store.Batch) error {
				for _, node := range allocatedNodes {
					writeTxDone := metrics.StartTimer(storeLockHeld.WithValues("node", "allocate", "write"))
					if err := batch.Update(func(tx store.Tx) error {
						currentNode := store.GetNode(tx, node.ID)
						if currentNode == nil {
							// if there is no node, then it must have been
							// deleted. deallocate our changes.

							// TODO(dperny): IMPORTANT! there is a race
							// condition here which is very dangerous! calls to
							// deallocate are not idempotent! this means that
							// we can't be sure that we won't inadvertently
							// free some state when we deallocate a second
							// time! a classic double-free case!
							log.G(ctx).WithField("node.id", node.ID).Debug("node was deleted after allocation but before committing")
							a.network.DeallocateNode(node)
							return nil
						}

						// the node may have changed in the meantime since we
						// read it before allocation. but since we're the only
						// one who changes the attachments, we can just plop
						// our new attachments into that slice with no danger
						currentNode.Attachments = node.Attachments

						return store.UpdateNode(tx, currentNode)
					}); err != nil {
						log.G(ctx).WithError(err).WithField("node.id", node.ID).Error("error in committing allocated node")
					}
					writeTxDone()
				}
				return nil
			}); err != nil {
				log.G(ctx).WithError(err).Error("error in batch update of allocated nodes")
			}
		}
	}

	// finally, allocate all tasks.
	if len(pendingTasks) > 0 {
		// this might seem a bit nonobvious. basically, what we're doing is
		// allocating services as needed by tasks. and we're going to optimize
		// on allocating many tasks belonging to a service at the same time.
		// So, in our View transaction, we're going to go through each pending
		// task ID. if it's still ready for allocation, we're going to get its
		// service and stash the service in a slice. then, we're going to stash
		// the task in a slice in a map.

		// services is a slice of services with tasks pending allocation
		services := []*api.Service{}

		// tasks is a map from service id to a slice of task objects belonging
		// to that service
		tasks := map[string][]*api.Task{}
		storeDone := metrics.StartTimer(storeLockHeld.WithValues("service", "allocate", "read"))
		a.store.View(func(tx store.ReadTx) {
			for taskid := range pendingTasks {
				t := store.GetTask(tx, taskid)
				// if the task is not nil, is in state NEW, and is desired to
				// be running, then it still needs allocation
				if t != nil && t.Status.State == api.TaskStateNew && t.DesiredState == api.TaskStateRunning {
					// if the task has an empty service, then we don't need to
					// allocate the service. however, we'll keep those
					// serviceless tasks (network attachment tasks) under the
					// emptystring key in the map and specialcase that key
					// later.
					service := store.GetService(tx, t.ServiceID)
					if service != nil {
						services = append(services, service)
					}
					// thus, if t.ServiceID == "", this will still work
					// this is safe without initializing each slice, because
					// appending to a nil slice is valid
					tasks[t.ServiceID] = append(tasks[t.ServiceID], t)
				}
			}
		})
		storeDone()

		// allocatedServices will store the services we have actually
		// allocated, not including the services that didn't need allocation
		allocatedServices := make([]*api.Service, 0, len(services))
		// allocatedTasks, likewise, stores the tasks we've successfully
		// allocated and should commit. we don't initialize it with a fixed
		// length because it's trickier for tasks
		allocatedTasks := []*api.Task{}

		// now, allocate the services and all of their tasks
		for _, service := range services {
			ctx := log.WithField(ctx, "service.id", service.ID)
			allocDone := metrics.StartTimer(allocatorActions.WithValues("service", "allocate"))
			err := a.network.AllocateService(service)
			allocDone()
			switch {
			case err == nil:
				// first, if no error occurred, then we can add this to the list of
				// networks we will commit
				allocatedServices = append(allocatedServices, service)
			case errors.IsErrAlreadyAllocated(err):
				// if the network is already allocated, there is nothing to do. log
				// that and do not add this network to the batch
				log.G(ctx).Debug("service already fully allocated")
			case errors.IsErrRetryable(err):
				// if the error is retryable, then we should log that error,
				// and then re-add every pending task belonging to this service
				// to our pending tasks, and remove their entry from the tasks
				// map.
				log.G(ctx).WithError(err).Error("service could not be allocated, but will be retried")
				for _, task := range tasks[service.ID] {
					a.pendingTasks[task.ID] = struct{}{}
				}
				delete(tasks, service.ID)
			default:
				// default covers any other error case. specifically, error that
				// are not retryable. for these, we should fail and not re-add them
				// to the pending map. they will never succeed. additionally,
				// remove these tasks from the map
				log.G(ctx).WithError(err).Error("service cannot be allocated")
				delete(tasks, service.ID)
			}

			// now, we should allocate all of the tasks for this service
			for _, task := range tasks[service.ID] {
				ctx := log.WithField(ctx, "task.id", task.ID)
				allocTaskDone := metrics.StartTimer(allocatorActions.WithValues("task", "allocate"))
				err := a.network.AllocateTask(task)
				allocTaskDone()
				switch {
				case err == nil:
					// first, if no error occurred, then we can add this to the
					// list of tasks we will commit
					allocatedTasks = append(allocatedTasks, task)
				case errors.IsErrAlreadyAllocated(err):
					// if the task is already allocated, there is nothing to do. log
					// that and do not add this network to the batch
					log.G(ctx).Debug("task already fully allocated")
				case errors.IsErrRetryable(err):
					// if the error is retryable, then we should log that error
					// and readd the task to the pending tasks map
					log.G(ctx).WithError(err).Error("task could not be allocated, but will be retried")
					a.pendingTasks[task.ID] = struct{}{}
				default:
					// default covers any other error case. specifically, error that
					// are not retryable. for these, we should fail and not re-add them
					// to the pending map. they will never succeed. additionally,
					// remove these tasks from the map
					log.G(ctx).WithError(err).Error("task cannot be allocated")
				}
			}
		}

		// now handle all of the tasks belonging to no service
		for _, task := range tasks[""] {
			ctx := log.WithField(ctx, "task.id", task.ID)
			allocTaskDone := metrics.StartTimer(allocatorActions.WithValues("task", "allocate"))
			err := a.network.AllocateTask(task)
			allocTaskDone()
			switch {
			case err == nil:
				// first, if no error occurred, then we can add this to the
				// list of tasks we will commit
				allocatedTasks = append(allocatedTasks, task)
			case errors.IsErrAlreadyAllocated(err):
				// if the task is already allocated, there is nothing to do. log
				// that and do not add this network to the batch
				log.G(ctx).Debug("task already fully allocated")
			case errors.IsErrRetryable(err):
				// if the error is retryable, then we should log that error
				// and readd the task to the pending tasks map
				log.G(ctx).WithError(err).Error("task could not be allocated, but will be retried")
				a.pendingTasks[task.ID] = struct{}{}
			default:
				// default covers any other error case. specifically, error that
				// are not retryable. for these, we should fail and not re-add them
				// to the pending map. they will never succeed. additionally,
				// remove these tasks from the map
				log.G(ctx).WithError(err).Error("task cannot be allocated")
			}
		}

		// finally, if we have any services or tasks to commit, open a
		// batch and commit them
		if len(allocatedServices)+len(allocatedTasks) > 0 {
			taskWriteTxDone := metrics.StartTimer(storeLockHeld.WithValues("allocate", "task", "write"))
			if err := a.store.Batch(func(batch *store.Batch) error {
				for _, service := range allocatedServices {
					if err := batch.Update(func(tx store.Tx) error {
						currentService := store.GetService(tx, service.ID)
						if currentService == nil {
							// TODO(dperny): see explanation in node
							log.G(ctx).WithField("service.id", service.ID).Debug("service was delete after allocation but before commit")
							a.network.DeallocateService(service)
							return nil
						}
						// the service may have changed in the meantime, so
						// only update the fields we just altered in it.
						// in this case, only the endpoint
						currentService.Endpoint = service.Endpoint
						// then commit the service
						return store.UpdateService(tx, currentService)
					}); err != nil {
						// TODO(dperny)
					}
				}

				for _, task := range allocatedTasks {
					if err := batch.Update(func(tx store.Tx) error {
						currentTask := store.GetTask(tx, task.ID)
						if currentTask == nil ||
							currentTask.Status.State != api.TaskStateNew ||
							currentTask.DesiredState != api.TaskStateRunning {
							log.G(ctx).WithField("task.id", task.ID).Debug("task removed after allocation but before commit")
							a.network.DeallocateTask(task)
							return nil
						}

						currentTask.Endpoint = task.Endpoint
						currentTask.Networks = task.Networks
						// update the task status as well
						currentTask.Status = api.TaskStatus{
							State:     api.TaskStatePending,
							Message:   AllocatedStatusMessage,
							Timestamp: ptypes.MustTimestampProto(time.Now()),
						}
						return store.UpdateTask(tx, currentTask)
					}); err != nil {
						// TODO(dperny)
					}
				}
				return nil
			}); err != nil {
				// TODO(dperny)
			}
			taskWriteTxDone()
		}
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

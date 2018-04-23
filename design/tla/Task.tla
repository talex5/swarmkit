This is a TLA+ model of SwarmKit. Even if you don't know TLA+, you should be able to
get the general idea. Here is a very brief overview of the syntax:

Declare `x' to be something that changes as the system runs:
VARIABLE x

Define `Init' to be a state predicate:
Init ==
  x = 0

`Init' is true for states in which `x = 0'. This can be used to define
the possible initial states of the system. For example, the state
[ x |-> 0, y |-> 2, ... ] satisfies this.

Define `Next' to be an action:
Next ==
   /\ x' \in Nat
   /\ x' > x

An action takes a pair of states, representing an atomic step of the system.
Unprimed expressions (e.g. `x') refer to the old state, and primed ones to
the new state. This example says that a step is a `Next' step iff the new
value of `x' is a natural number and greater than the previous value.
For example, [ x |-> 3, ... ] -> [x |-> 10, ... ] is a `Next' step.

/\ is logical ``and''. This example uses TLA's ``bulleted-list'' syntax, which makes
writing these easier. It is indentation-sensitive. TLA also has \/ lists (``or'').

See `.http://lamport.azurewebsites.net/tla/summary.pdf.' for a more complete summary
of the syntax.

This specification can be read as documentation, but it can also be executed by the TLC
model checker. See the model checking section below for details about that.

-------------------------------- MODULE Task --------------------------------

(* A description of the task model in SwarmKit.
   Currently, this is mostly based on `design/task_model.md'.

   Note: I am not yet familiar with the SwarmKit code, and this document is likely to
   be incorrect. It is my current guess about the design. I hope that SwarmKit
   developers will point out the errors.
 *)

EXTENDS Integers, TLC, FiniteSets   \* Some libraries we use

(* A generic operator to get the range of a function (the set of values in a map): *)
Range(S) == { S[i] : i \in DOMAIN S }

(* The set of worker nodes.

   Note: a CONSTANT is an input to the model. It should work with any set of nodes you provide.

   TODO: should cope with this changing at runtime, and with draining nodes. *)
CONSTANT Node

(* A special value indicating that a task is not yet assigned to a node.

   Note: this TLA+ CHOOSE idiom just says to pick some value that isn't a Node (e.g. `null'). *)
unassigned == CHOOSE n : n \notin Node

(* The type (set) of service IDs (e.g. `Int' or `String').
   When model checking, this will be some small set (e.g. {"s1", "s2"}). *)
CONSTANT ServiceId

(* The type of task IDs. *)
CONSTANT TaskId

\* The maximum number of terminated tasks to keep for each slot:
CONSTANT maxTerminated
ASSUME maxTerminated \in Nat

\* The maximum possible value for `replicas' in ServiceSpec:
CONSTANT maxReplicas
ASSUME maxReplicas \in Nat
Slot == 1..maxReplicas  \* Possible slot numbers

(* A special value (e.g. `-1') indicating that we want one replica running on each node: *)
global == CHOOSE x : x \notin Slot

(* The type of a description of a service (a struct/record).
   This is provided by, and only changed by, the user. *)
ServiceSpec == [
  replicas : 0..maxReplicas \union {global} \* A count, or `global'
]

(* The possible states for a task: *)
new == "new"
pending == "pending"
assigned == "assigned"
accepted == "accepted"
preparing == "preparing"
ready == "ready"
starting == "starting"
running == "running"
complete == "complete"
shutdown == "shutdown"
failed == "failed"
rejected == "rejected"
remove == "remove"
orphaned == "orphaned"

(* Every state has a rank. It is only possible for a task to change
   state to a state with a higher rank (later in this sequence). *)
order == << new, pending, assigned, accepted,
             preparing, ready, starting,
             running,
             complete, shutdown, failed, rejected,
             remove, orphaned >>

(* Maps a state to its position in `order' (e.g. StateRank(new) = 1): *)
StateRank(s) == CHOOSE i \in DOMAIN order : order[i] = s

(* Convenient notation for comparing states: *)
s1 \prec s2   == StateRank(s1) <  StateRank(s2)
s1 \preceq s2 == StateRank(s1) <= StateRank(s2)

(* The set of possible states ({new, pending, ...}): *)
TaskState == Range(order)

(* Possibly this doesn't need to be a record, but we might want to add extra fields later. *)
TaskStatus == [
  state : TaskState
]

(* This has every field mentioned in `task_model.md' except for `spec', which
   it doesn't seem to use for anything.

   `desired_state' can be any state, although currently we only ever set it to one of
    {ready, running, shutdown, remove}. *)
Task == [
  id : TaskId,                      \* To uniquely identify this task
  service : ServiceId,              \* The service that owns the task
  status : TaskStatus,              \* The current state
  desired_state : TaskState,        \* The state requested by the orchestrator
  node : Node \union {unassigned},  \* The node on which the task should be run
  slot : Slot \union {global}       \* A way of tracking related tasks
]

nodeUp   == "up"
nodeDown == "down"
NodeState == { nodeUp, nodeDown }

VARIABLE tasks          \* The set of currently-allocated tasks
VARIABLE services       \* A map of currently-allocated services, indexed by ServiceId
VARIABLE nodes          \* Maps nodes to SwarmKit's view of their NodeState

(* The current state of task `t'. *)
State(t) == t.status.state

(* A task is runnable if it is running or could become running in the future. *)
Runnable(t) == State(t) \preceq running

(* The expected type of each variable. TLA+ is an untyped language, but the model checker
   can check that TypeOK is true for every reachable state. *)
TypeOK ==
  \* `tasks' is a subset of the set of all possible tasks
  /\ tasks \in SUBSET Task
  \* `services' is a mapping from service IDs to ServiceSpecs:
  /\ DOMAIN services \subseteq ServiceId
  /\ services \in [ DOMAIN services -> ServiceSpec ]
  \* Nodes are up or down
  /\ nodes \in [ Node -> NodeState ]

-------------------------------------------------------------------------------
\* Model checking

(* You can test this specification using the TLC model checker.
   This section describes how to do that. If you don't want to run TLC,
   you can skip this section.

   To use TLC, load this specification file in the TLA+ toolbox (``Open Spec'')
   and create a new model using the menu.

   You will be prompted to enter values for the various CONSTANTS.
   A suitable set of initial values is:

   `.
   Node          <- [ model value ] {n1}
   ServiceId     <- [ model value ] {s1}
   TaskId        <- [ model value ] {t1, t2}
   maxReplicas   <- 1
   maxTerminated <- 1
   .'

   For the [ model value ] ones, select `Set of model values'.

   This says that we have one node, `n1', and at most one service and two tasks.
   TLC can explore all possible behaviours of this system in a couple of seconds
   on my laptop.

   You should also specify some things to check (under ``What to check?''):

   - Add `TypeOK' and `Inv' under ``Invariants''
   - Add `TransitionsOK' and `EventuallyAsDesired' under ``Properties''

   Running the model should report ``No errors''.

   Increasing the number of nodes, services, replicas or terminated tasks
   will check more of the system, but will be MUCH slower. It may also fail because
   there aren't enough task IDs - if the final state it shows has all tasks used,
   try adding more.

   To make it go faster, you should configure any model sets (e.g. `TaskId') as `symmetry sets'.
   It will warn that checking temporal properties may not work correctly,
   but it's much faster and I haven't had any problems with it.

   Another way to speed it up is to reduce the number of failures it must consider.
   By default, it checks every possible combination of failures at every point, which
   is very expensive.
   In the `Advanced Options' panel of the model, add a ``Definition Override'' of e.g.
   `maxEvents = 2'. Actions that represent unnecessary extra work (such as the user
   changing the configuration or a worker node going down) are tagged with `CountEvent'.
   Any run of the system cannot have more than `maxEvents' such events.

   If the model fails, TLC will show you an example sequence of actions that lead to
   the failure and you can inspect the state at each step. You can try this out by
   commenting out any important-looking condition in the model (e.g. the requirement
   in UpdateService that you can't change the mode of an existing service).
*)

\* The number of ``events'' that have occurred (always 0 if we're not keeping track).
VARIABLE nEvents

\* The maximum number of events to allow, or ``-1'' for unlimited.
maxEvents == -1

InitEvents ==
  nEvents = 0       \* Start with the counter at zero

(* If we're counting events, increment the event counter.
   We don't increment the counter when we don't have a maximum because that
   would make the model infinite.
   Actions tagged with CountEvent cannot happen once nEvents = maxEvents. *)
CountEvent ==
  IF maxEvents = -1 THEN
    UNCHANGED nEvents
  ELSE
    /\ nEvents < maxEvents
    /\ nEvents' = nEvents + 1

-------------------------------------------------------------------------------
\* Actions performed by users

(* Create a new service with any ServiceSpec.

   This says that a single atomic step of the system from an old state
   to a new one is a CreateService step iff `tasks' and `nEvents' don't change
   and the new value of `services' is the same as before except that some
   service ID that wasn't used in the old state is now mapped to some
   ServiceSpec.

   Note: A \ B means { x \in A : x \notin B } --
         i.e. the set A with all elements in B removed.
   *)
CreateService ==
  /\ UNCHANGED << tasks, nodes, nEvents >>
  /\ \E sid \in ServiceId \ DOMAIN services,  \* `sid' is an unused ServiceId
       spec \in ServiceSpec :                 \* `spec' is any ServiceSpec
          services' = services @@ sid :> spec \* Add `sid |-> spec' to `services'

(* Update an existing service's spec. *)
UpdateService ==
  /\ UNCHANGED << tasks, nodes >>
  /\ CountEvent \* Flag as an event for model-checking purposes
  /\ \E sid     \in DOMAIN services,        \* `sid' is an existing ServiceId
        newSpec \in ServiceSpec :           \* `newSpec' is any `ServiceSpec'
      \* You can't change a service's mode:
      /\ (services[sid].replicas = global) <=> (newSpec.replicas = global)
      /\ services' = [ services EXCEPT ![sid] = newSpec ]

(* A user action is one of these. *)
User ==
  \/ CreateService
  \/ UpdateService

(* Removing a service is not currently modelled, as the SwarmKit developers are currently
   ``working on a change to the service object to flag it for removal, instead of removing it outright''

   TODO: update the model once the new design is available *)

-------------------------------------------------------------------------------
\* Actions performed the orchestrator

(* Note: This is by far the most complicated component in the model. You might want to read this section last... *)

(* A replicated service specifies the number of replicas it wants. *)
IsReplicated(sid) ==
  services[sid].replicas \in Nat

(* A global service wants one task running on each node. *)
IsGlobal(sid) ==
  services[sid].replicas = global

(* TasksOf(sid) is the set of tasks for service `sid'. *)
TasksOf(sid) ==
  { t \in tasks : t.service = sid }

(* A task's ``virtual slot'' is its actual slot for replicated services,
   but its node for global ones. *)
VSlot(t) ==
  IF IsReplicated(t.service)
    THEN t.slot
    ELSE t.node

(* All tasks of service `sid' in `vslot'. *)
TasksOfVSlot(sid, vslot) ==
  { t \in TasksOf(sid) : VSlot(t) = vslot }

(* All vslots of service `sid'. *)
VSlotsOf(sid) ==
  { VSlot(t) : t \in TasksOf(sid) }

(* The set of tasks for service `sid' that should be considered as active.
   This is any task that is running or on its way to running. *)
RunnableTasks(sid) ==
  { t \in TasksOf(sid) : Runnable(t) }

(* Candidates for shutting down when we have too many. We don't want to count tasks that are shutting down
   towards the total count when deciding whether we need to kill anything. *)
RunnableWantedTasks(sid) ==
  { t \in RunnableTasks(sid) : t.desired_state \preceq running  }

(* A `new' task belonging to service `sid' with the given slot, id, and desired state. *)
NewTask(sid, vslot, id, desired_state) ==
  [
    id            |-> id,
    service       |-> sid,
    status        |-> [ state |-> new ],
    desired_state |-> desired_state,
    node          |-> IF IsReplicated(sid) THEN unassigned ELSE vslot,
    slot          |-> IF IsGlobal(sid)     THEN global     ELSE vslot
  ]

(* Update tasks by performing each update in `f', which is a function
   mapping old tasks to new ones. *)
UpdateTasks(f) ==
  /\ Assert(\A t \in DOMAIN f : t \in tasks, "An old task does not exist!")
  /\ Assert(\A t \in DOMAIN f :
                LET t2 == f[t] IN
                /\ t.id      = t2.id
                /\ t.service = t2.service
                /\ VSlot(t)  = VSlot(t2),
            "An update changes a task's identity!")
  /\ tasks' = (tasks \ DOMAIN f) \union Range(f)

(* The set of possible new vslots for `sid'. *)
UnusedVSlot(sid) ==
  IF IsReplicated(sid) THEN Slot \ VSlotsOf(sid)
                       ELSE Node \ VSlotsOf(sid)

(* The set of possible IDs for a new task in a vslot.

   This is just the set of unallocated IDs globally -- we don't care
   about `sid' and `vslot'.
   However, for modelling purposes it may be useful to override this.
 *)
UnusedId(sid, vslot) ==
  LET usedIds == { t.id : t \in tasks }
  IN  TaskId \ usedIds

(* Create a new task/slot if the number of runnable tasks is less than the number requested. *)
CreateSlot ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E sid \in DOMAIN services :          \* `sid' is an existing service
     (* For replicated tasks, only create as many slots as we need.
        For global tasks, we want all possible vslots (nodes). *)
     /\ IsReplicated(sid) =>
          services[sid].replicas > Cardinality(VSlotsOf(sid))  \* Desired > actual
     /\ \E slot \in UnusedVSlot(sid) :
        \E id   \in UnusedId(sid, slot) :
           tasks' = tasks \union { NewTask(sid, slot, id, running) }

(* Add a task if a slot exists, contains no runnable tasks, and we weren't trying to remove it.
   Note: if we are trying to remove it, the slot will eventually disappear and CreateSlot will
   then make a new one if we later need it again.

   Currently in SwarmKit, slots do not actually exist as objects in the store.
   Instead, we just infer that a slot exists because there exists a task with that slot ID.
   This has the odd effect that if `maxTerminated = 0' then we may create new slots rather than reusing
   existing ones, depending on exactly when the reaper runs.
   *)
ReplaceTask ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E sid  \in DOMAIN services :
     \E slot \in VSlotsOf(sid) :
     /\ \A task \in TasksOfVSlot(sid, slot) :    \* If all tasks in `slot' are
           ~Runnable(task)                       \* dead (not runnable) and
     /\ \E task \in TasksOfVSlot(sid, slot) :    \* there is some task that
           task.desired_state # remove           \* we're not trying to remove,
     /\ \E id \in UnusedId(sid, slot) :          \* then create a replacement task:
        tasks' = tasks \union { NewTask(sid, slot, id, running) }

(* If we have more replicas than the spec asks for, remove one of them. *)
RequestRemoval ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E sid \in DOMAIN services :
       LET current == RunnableWantedTasks(sid)
       IN \* Note: `current' excludes tasks we're already trying to kill
       /\ IsReplicated(sid)
       /\ services[sid].replicas < Cardinality(current)   \* We have too many replicas
       /\ \E slot \in { t.slot : t \in current } :        \* Choose an allocated slot
            \* Mark all tasks for that slot for removal:
            UpdateTasks( [ t \in TasksOfVSlot(sid, slot) |->
                            [t EXCEPT !.desired_state = remove] ] )

(* Mark a terminated task for removal if we already have `maxTerminated' terminated tasks for this slot. *)
CleanupTerminated ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E sid  \in DOMAIN services :
     \E slot \in VSlotsOf(sid) :
     LET termTasksInSlot == { t \in TasksOfVSlot(sid, slot) :
                              State(t) \in { complete, shutdown, failed, rejected } }
     IN
     /\ Cardinality(termTasksInSlot) > maxTerminated    \* Too many tasks for slot
     /\ \E t \in termTasksInSlot :                      \* Pick a victim to remove
        UpdateTasks(t :> [t EXCEPT !.desired_state = remove])

(* We don't model the updater explicitly, but we allow any task to be restarted (perhaps with
   a different image) at any time, which should cover the behaviours of the restart supervisor. *)
RestartTask ==
  /\ UNCHANGED << services, nodes >>
  /\ CountEvent
  /\ \E oldT \in tasks :
     \E newId \in UnusedId(oldT.service, VSlot(oldT)) :
        /\ Runnable(oldT)                           \* Victim must be runnable
        /\ oldT.desired_state \prec shutdown        \* and we're not trying to kill it
        \* Create the new task in the `ready' state (see ReleaseReady below):
        /\ LET replacement == NewTask(oldT.service, VSlot(oldT), newId, ready)
           IN  tasks' =
                (tasks \ {oldT}) \union {
                  [oldT EXCEPT !.desired_state = shutdown],
                  replacement
                }

(* A task is set to wait at `ready' and the previous task for that slot has now finished.
   Allow it to proceed to `running'.

   TODO: ``However, there are also cases where a slot may have multiple tasks with the
   desired state of RUNNING. This can happen during rolling updates when the updates
   are configured to start the new task before stopping the old one.'' - need to implement this *)
ReleaseReady ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E t \in tasks :
       /\ t.desired_state = ready         \* (and not e.g. `remove')
       /\ State(t) = ready
       /\ \A other \in TasksOfVSlot(t.service, VSlot(t)) \ {t} :
             ~Runnable(other)             \* All other tasks have finished
       /\ UpdateTasks(t :> [t EXCEPT !.desired_state = running])

(* Tasks that the orchestrator must always do eventually if it can: *)
OrchestratorProgress ==
  \/ CreateSlot
  \/ ReplaceTask
  \/ RequestRemoval
  \/ CleanupTerminated
  \/ ReleaseReady

(* All actions that the orchestrator can perform *)
Orchestrator ==
  \/ OrchestratorProgress
  \/ RestartTask

-------------------------------------------------------------------------------
\*  Actions performed the allocator

(* Pick a `new' task and move it to `pending'.

   The spec says the allocator will ``allocate resources such as network attachments
   which are necessary for the tasks to run''. However, we don't model any resources here. *)
AllocateTask ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E t \in tasks :
     /\ State(t) = new
     /\ UpdateTasks(t :> [t EXCEPT !.status.state = pending])

(* The allocator rejects the task because there aren't enough resources.

   XXX: Not clear whether SwarmKit actually does this. *)
RejectAllocation ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E t \in tasks :
     /\ State(t) = new
     /\ UpdateTasks(t :> [t EXCEPT !.status.state = rejected])  \* XXX: Is this the right state?

AllocatorProgress ==
  \/ AllocateTask

Allocator ==
  \/ AllocatorProgress
  \/ RejectAllocation

-------------------------------------------------------------------------------
\*  Actions performed the scheduler

(* The scheduler assigns a node to a `pending' task and moves it to `assigned'
   once sufficient resources are available (we don't model resources here). *)
Scheduler ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E t \in tasks :
     /\ State(t) = pending
     /\ LET candidateNodes == IF t.node = unassigned
                                THEN Node  \* (all nodes)
                                ELSE { t.node }
        IN
        \E node \in candidateNodes :
           UpdateTasks(t :> [t EXCEPT !.status.state = assigned,
                                      !.node = node ])

-------------------------------------------------------------------------------
\*  Actions performed by worker nodes (actually, by the dispatcher on their behalf)

(* SwarmKit thinks the node is up. i.e. the agent is connected to a manager. *)
IsUp(n) == nodes[n] = nodeUp

(* Try to advance containers towards `desired_state' if we're not there yet. *)
ProgressTask ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E t  \in tasks,
        s2 \in TaskState :   \* The state we want to move to
        LET t2 == [t EXCEPT !.status.state = s2]
        IN
        /\ s2 \preceq t.desired_state       \* Can't be after the desired state
        /\ << State(t), State(t2) >> \in {  \* Possible ``progress'' (desirable) transitions
             << assigned, accepted >>,
             << accepted, preparing >>,
             << preparing, ready >>,
             << ready, starting >>,
             << starting, running >>
           }
        /\ IsUp(t.node)                     \* Node must be connected to SwarmKit
        /\ UpdateTasks(t :> t2)

(* A running container finishes because we stopped it. *)
ShutdownComplete ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E t \in tasks :
     /\ t.desired_state \in {shutdown, remove}                  \* We are trying to stop it
     /\ State(t) = running                                      \* It is currently running
     /\ IsUp(t.node)
     /\ UpdateTasks(t :> [t EXCEPT !.status.state = shutdown])  \* It becomes shutdown

(* A node can reject a task once it's responsible for it (it has reached `assigned')
   until it reaches the `running' state.
   Note that an ``accepted'' task can still be rejected. *)
RejectTask ==
  /\ UNCHANGED << services, nodes >>
  /\ CountEvent
  /\ \E t \in tasks :
       /\ State(t) \in { assigned, accepted, preparing, ready, starting }
       /\ IsUp(t.node)
       /\ UpdateTasks(t :> [t EXCEPT !.status.state = rejected])

(* A running container finishes running on its own.

   TODO: we should model the actual state of containers separately from
   the SwarmKit manager's record of their states. *)
ContainerExit ==
  /\ UNCHANGED << services, nodes >>
  /\ CountEvent
  /\ \E t  \in tasks,
        s2 \in {failed, complete} :      \* Either a successful or failed exit status
        /\ State(t) = running
        /\ IsUp(t.node)
        /\ UpdateTasks(t :> [t EXCEPT !.status.state = s2])

(* Tasks assigned to a node and for which the node is responsible. *)
TasksOwnedByNode(n) == { t \in tasks :
  /\ t.node = n
  /\ assigned \preceq State(t)
  /\ State(t) \prec remove
}

(* The dispatcher notices that the worker is down (the connection is lost). *)
WorkerDown ==
  /\ UNCHANGED << tasks, services >>
  /\ CountEvent
  /\ \E n \in Node :
       /\ IsUp(n)
       /\ nodes' = [nodes EXCEPT ![n] = nodeDown]

(* When the node reconnects to the cluster, it gets an assignment set from the dispatcher
   which does not include any tasks that have been marked orphaned and then deleted.
   Any time an agent gets an assignment set that does not include some task it has running,
   it shuts down those tasks.

   Currently, we don't model the state of the tasks on the node separately from the SwarmKit
   state. *)
WorkerUp ==
  /\ UNCHANGED << tasks, services, nEvents >>
  /\ \E n \in Node :
       /\ ~IsUp(n)
       /\ nodes' = [nodes EXCEPT ![n] = nodeUp]

(* If SwarmKit sees a node as down for a long time (48 hours or so) then
   it marks all the node's tasks as orphaned.

   ``Moving a task to the Orphaned state is not desirable,
   because it's the one case where we break the otherwise invariant
   that the agent sets all states past ASSIGNED.''
*)
OrphanTasks ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E n \in Node :
       LET affected == { t \in TasksOwnedByNode(n) : Runnable(t) }
       IN
       /\ ~IsUp(n)    \* Node `n' is still detected as down
       /\ UpdateTasks([ t \in affected |->
                         [t EXCEPT !.status.state = orphaned] ])

(* Actions we require to happen eventually when possible. *)
AgentProgress ==
  \/ ProgressTask
  \/ ShutdownComplete
  \/ OrphanTasks
  \/ WorkerUp

(* All actions of the agent/worker. *)
Agent ==
  \/ AgentProgress
  \/ RejectTask
  \/ ContainerExit
  \/ WorkerDown

-------------------------------------------------------------------------------
\*  Actions performed by the reaper

(* Forget about tasks in remove or orphan states.

   Orphaned tasks belong to nodes that we are assuming are lost forever.
   Or, at the very least, it's likely that a node outage lasting longer than the timeout
   has crashed and will come up with nothing running (which is an equally fine outcome).

   TODO: model worker nodes crashing
*)
Reaper ==
  /\ UNCHANGED << services, nodes, nEvents >>
  /\ \E t \in tasks :
      /\ \/ (~Runnable(t) /\ t.desired_state = remove)
         \/ State(t) = orphaned
      /\ tasks' = tasks \ {t}

-------------------------------------------------------------------------------
\*  The complete system

\* All the variables
vars == << tasks, services, nodes, nEvents >>

\* Initially there are no tasks and no services, and all nodes are up.
Init ==
  /\ tasks = {}
  /\ services = << >>
  /\ nodes = [ n \in Node |-> nodeUp ]
  /\ InitEvents

(* A next step is one in which any of these sub-components takes a step: *)
Next ==
  \/ User
  \/ Orchestrator
  \/ Allocator
  \/ Scheduler
  \/ Agent
  \/ Reaper
  \* For model checking: don't report deadlock if we're limiting events
  \/ (nEvents = maxEvents /\ UNCHANGED vars)

(* This is a ``temporal formula''. It takes a sequence of states representing the
   changing state of the world and evaluates to TRUE if that sequences of states is
   a possible behaviour of SwarmKit. *)
Spec ==
  \* The first state in the behaviour must satisfy Init:
  /\ Init
  \* All consecutive pairs of states must satisfy Next or leave `vars' unchanged:
  /\ [][Next]_vars
  (* Some actions are required to happen eventually. For example, a behaviour in
     which SwarmKit stops doing anything forever, even though it could advance some task
     from the `new' state, isn't a valid behaviour of the system.
     This property is called ``weak fairness''. *)
  /\ WF_vars(OrchestratorProgress)
  /\ WF_vars(AllocatorProgress)
  /\ WF_vars(Scheduler)
  /\ WF_vars(AgentProgress)
  /\ WF_vars(Reaper)
  /\ WF_vars(WorkerUp)
     (* We don't require fairness of:
        - User (we don't control them),
        - RestartTask (services aren't required to be updated),
        - RejectTask (tasks aren't required to be rejected),
        - ContainerExit (we don't specify image behaviour) or
        - WorkerDown (workers aren't required to fail). *)

-------------------------------------------------------------------------------
\* Properties to verify

(* These are properties that should follow automatically if the system behaves as
   described by `Spec' in the previous section. *)

\* A state invariant (things that should be true in every state).
Inv ==
  \A t \in tasks :
    (* Every task has a service:

       XXX: The spec says: ``In some cases, there are tasks that exist independent of any service.
            These do not have a value set in service_id.''. Need an example of one. *)
    /\ t.service \in DOMAIN services
    \* Tasks have nodes once they reach `assigned', except maybe if rejected:
    /\ assigned \preceq State(t) => t.node \in Node \/ State(t) = rejected
    \* `remove' is only used as a desired state, not an actual one:
    /\ State(t) # remove
    \* Task IDs are unique
    /\ \A t2 \in tasks : t.id = t2.id => t = t2

\* A special ``state'' used when a task doesn't exist.
null == "null"

(* All the possible transitions, grouped by the component that performs them. *)
Transitions == [
  orchestrator |-> {
    << null, new >>
  },

  allocator |-> {
    << new, pending >>,
    << new, rejected >>
  },

  scheduler |-> {
    << pending, assigned >>
  },

  agent |-> {
    << assigned, accepted >>,
    << accepted, preparing >>,
    << preparing, ready >>,
    << ready, starting >>,
    << starting, running >>,

    << assigned, rejected >>,
    << accepted, rejected >>,
    << preparing, rejected >>,
    << ready, rejected >>,
    << starting, rejected >>,

    << running, complete >>,
    << running, failed >>,

    << running, shutdown >>,

    << assigned, orphaned >>,
    << accepted, orphaned >>,
    << preparing, orphaned >>,
    << ready, orphaned >>,
    << starting, orphaned >>,
    << running, orphaned >>
  },

  reaper |-> {
    << rejected, null >>,
    << complete, null >>,
    << failed, null >>,
    << shutdown, null >>,
    << orphaned, null >>
  }
]

(* Check that `Transitions' itself is OK. *)
TransitionTableOK ==
  \* No transition moves to a lower-ranked state:
  /\ \A actor \in DOMAIN Transitions :
     \A << s1, s2 >> \in Transitions[actor] :
        \/ s1 = null
        \/ s2 = null
        \/ s1 \preceq s2
  \* Every source state has exactly one component which handles transitions out of that state:
  /\ \A a1, a2 \in DOMAIN Transitions :
     LET Source(a) == { s[1] : s \in Transitions[a] }
     IN  a1 # a2 =>
           Source(a1) \intersect Source(a2) = {}

ASSUME TransitionTableOK  \* Note: ASSUME means ``check'' to TLC

IdSet(S) == { x.id : x \in S }

(* The state of task `i' in `S', or `null' if it doesn't exist *)
Get(S, i) ==
  LET cand == { x \in S : x.id = i }
  IN  IF cand = {} THEN null
                   ELSE State(CHOOSE x \in cand : TRUE)

(* An action in which all transitions were valid. *)
TransitionOK ==
  LET permitted == { << x, x >> : x \in TaskState } \union  \* No change is always OK
    CASE Orchestrator -> Transitions.orchestrator
      [] Allocator    -> Transitions.allocator
      [] Scheduler    -> Transitions.scheduler
      [] Agent        -> Transitions.agent
      [] Reaper       -> Transitions.reaper
      [] OTHER        -> {}
    oldIds == IdSet(tasks)
    newIds == IdSet(tasks')
  IN
  \A id \in newIds \union oldIds :
     << Get(tasks, id), Get(tasks', id) >> \in permitted

(* Some of the expressions below are ``temporal formulas''. Unlike state expressions and actions,
   these look at a complete behaviour (sequence of states). Summary of notation:

   [] means ``always''. e.g. []x=3 means that `x = 3' in all states.

   <> means ``eventually''. e.g. <>x=3 means that `x = 3' in some state.

   `x=3' on its own means that `x=3' in the initial state.
*)

\* A temporal formula that checks transitions
TransitionsOK ==
  /\ [][TransitionOK]_vars      \* Every step satisfies TransitionOK (or leaves `vars' unchanged)

(* Every service has the right number of running tasks (the system is in the desired state). *)
InDesiredState ==
  \A sid \in DOMAIN services :
    \* The service has the correct set of running replicas:
    /\ LET runningTasks  == { t \in TasksOf(sid) : State(t) = running }
           nRunning      == Cardinality(runningTasks)
       IN
       CASE IsReplicated(sid) -> nRunning = services[sid].replicas
         [] IsGlobal(sid) ->
              \* We have as many tasks as nodes:
              /\ nRunning = Cardinality(Node)
              \* We have a task for every node:
              /\ { t.node : t \in runningTasks } = Node
    \* The service does not have too many terminated tasks
    /\ \A slot \in VSlotsOf(sid) :
       LET terminated == { t \in TasksOfVSlot(sid, slot) : ~Runnable(t) }
       IN  Cardinality(terminated) <= maxTerminated

(* The main property we want to check.

   []<> means ``always eventually'' (``infinitely-often'')

   <>[] means ``eventually always'' (always true after some point)

   This temporal formula says that if we only experience a finite number of
   problems then the system will eventually settle on InDesiredState.
*)
EventuallyAsDesired ==
  \/ []<> <<User>>_vars              \* Either the user keeps changing the configuration,
  \/ []<> <<RestartTask>>_vars       \* or restarting/updating tasks,
  \/ []<> <<RejectAllocation>>_vars  \* or the allocator keeps rejecting tasks,
  \/ []<> <<WorkerDown>>_vars        \* or workers keep failing,
  \/ []<> <<RejectTask>>_vars        \* or workers keep rejecting tasks,
  \/ []<> <<ContainerExit>>_vars     \* or the containers keep exiting,
  \/ <>[] InDesiredState             \* or we eventually get to the desired state and stay there.

=============================================================================

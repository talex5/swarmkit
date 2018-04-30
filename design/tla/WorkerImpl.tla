---------------------------- MODULE WorkerImpl ----------------------------------
\* Actions performed by the engine running on a worker node

EXTENDS TLC, Types, Tasks, EventCounter

\* This worker's node ID
CONSTANT node
ASSUME node \in Node

VARIABLES nodes
VARIABLE containers     \* The actual container state on the node, indexed by task ID

(* The high-level specification of worker nodes.
   This module should be a refinement of `WS'. *)
WS == INSTANCE WorkerSpec

terminating == "terminating"        \* A container which we're trying to stop

(* The state of an actual container on a worker node. *)
ContainerState == { running, terminating, complete, failed }

(* A running container finishes running on its own. *)
ContainerExit ==
  /\ UNCHANGED << nodes, tasks >>
  /\ CountEvent
  /\ \E id \in DOMAIN containers,
        s2 \in {failed, complete} :      \* Either a successful or failed exit status
        /\ containers[id] = running
        /\ containers' = [containers EXCEPT ![id] = s2]

(* A running container finishes because we stopped it. *)
ShutdownComplete ==
  /\ UNCHANGED << nodes, tasks, nEvents >>
  /\ \E id \in DOMAIN containers :
        /\ containers[id] = terminating
        /\ containers' = [containers EXCEPT ![id] = failed]

EngineProgress ==
  \/ ShutdownComplete

Engine ==
  \/ EngineProgress
  \/ ContainerExit

\*  Actions performed by worker nodes (actually, by the dispatcher on their behalf)

(* SwarmKit thinks the node is up. i.e. the agent is connected to a manager. *)
IsUp(n) == WS!IsUp(n)

DesiredContainers ==
  LET (* Start shutting down containers if their task no longer exists or it says
         they should be shut down. *)
      WantShutdown(id) ==
        \/ id \notin IdSet(tasks)
        \/ running \prec (CHOOSE t \in tasks : Id(t) = id).desired_state
      (* Remove containers that no longer have tasks, once they've stopped. *)
      rm == { id \in DOMAIN containers :
                  /\ containers[id] \in { complete, failed }
                  /\ id \notin IdSet(tasks) }
  IN [ id \in DOMAIN containers \ rm |->
           IF containers[id] = running /\ WantShutdown(id) THEN terminating
           ELSE containers[id]
     ]

RequiredTaskUpdates ==
  LET (* Start shutting down containers if their task no longer exists or it says
         they should be shut down. *)
      WantShutdown(id) ==
        \/ id \notin IdSet(tasks)
        \/ running \prec (CHOOSE t \in tasks : Id(t) = id).desired_state
      (* Remove containers that no longer have tasks, once they've stopped. *)
      rm == { id \in DOMAIN containers :
                  /\ containers[id] \in { complete, failed }
                  /\ id \notin IdSet(tasks) }
      newCs == [ id \in DOMAIN containers \ rm |->
                    IF containers[id] = running /\ WantShutdown(id) THEN terminating
                    ELSE containers[id]
               ]
      \* Tasks the manager is expecting news about:
      oldTasks == { t \in tasks : t.node = node /\ State(t) = running }
      \* The state to report for task `t':
      ReportFor(t) ==
        IF Id(t) \notin DOMAIN containers THEN \* We were asked to forget about this container.
          shutdown \* SwarmKit doesn't care which terminal state we finish in.
        ELSE IF /\ containers[Id(t)]       = failed         \* It's terminated and
                /\ t.desired_state = shutdown THEN  \* we wanted to shut it down,
          shutdown \* Report a successful shutdown
        ELSE IF containers[Id(t)] = terminating THEN
          running
        ELSE
          containers[Id(t)]  \* Report the actual state
  IN [ t \in oldTasks |-> [ t EXCEPT !.status.state = ReportFor(t) ]]

(* Our node synchronises its state with a manager. *)
DoSync ==
   /\ containers' = DesiredContainers
   /\ UpdateTasks(RequiredTaskUpdates)

InSync ==
  /\ containers = DesiredContainers
  /\ LET f == RequiredTaskUpdates
     IN  \A t \in DOMAIN f : f[t] = t

(* Try to advance containers towards `desired_state' if we're not there yet.

   XXX: do we need a connection to the manager to do this, or can we make progress
   while disconnected and just report the final state? 
*)
ProgressTask ==
  /\ UNCHANGED << nodes, nEvents >>
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
        /\ IF s2 = running THEN
              containers' = Id(t) :> running @@ containers
           ELSE
              UNCHANGED containers
        /\ UpdateTasks(t :> t2)

(* The agent on the node synchronises with a manager. *)
SyncWithManager ==
  /\ UNCHANGED << nodes, nEvents >>
  /\ IsUp(node)
  /\ DoSync

(* We can reject a task once we're responsible for it (it has reached `assigned')
   until it reaches the `running' state.
   Note that an ``accepted'' task can still be rejected. *)
RejectTask ==
  /\ UNCHANGED << nodes, containers >>
  /\ CountEvent
  /\ \E t \in tasks :
       /\ State(t) \in { assigned, accepted, preparing, ready, starting }
       /\ t.node = node
       /\ IsUp(node)
       /\ UpdateTasks(t :> [t EXCEPT !.status.state = rejected])

(* The dispatcher notices that the worker is down (the connection is lost). *)
WorkerDown ==
  /\ UNCHANGED << tasks, containers >>
  /\ CountEvent
  /\ \E n \in Node :
       /\ IsUp(n)
       /\ nodes' = [nodes EXCEPT ![n] = WS!nodeDown]

(* When the node reconnects to the cluster, it gets an assignment set from the dispatcher
   which does not include any tasks that have been marked orphaned and then deleted.
   Any time an agent gets an assignment set that does not include some task it has running,
   it shuts down those tasks. *)
WorkerUp ==
  /\ UNCHANGED << nEvents >>
  /\ \E n \in Node :
       /\ ~IsUp(n)
       /\ nodes' = [nodes EXCEPT ![n] = WS!nodeUp]
       /\ IF n = node THEN DoSync
                      ELSE UNCHANGED << tasks, containers >>

(* Tasks assigned to a node and for which the node is responsible. *)
TasksOwnedByNode(n) == { t \in tasks :
  /\ t.node = n
  /\ assigned \preceq State(t)
  /\ State(t) \prec remove
}

(* If SwarmKit sees a node as down for a long time (48 hours or so) then
   it marks all the node's tasks as orphaned.

   ``Moving a task to the Orphaned state is not desirable,
   because it's the one case where we break the otherwise invariant
   that the agent sets all states past ASSIGNED.''
*)
OrphanTasks ==
  /\ UNCHANGED << nodes, containers, nEvents >>
  /\ LET affected == { t \in TasksOwnedByNode(node) : Runnable(t) }
     IN
     /\ ~IsUp(node)    \* Our connection to the agent is down
     /\ UpdateTasks([ t \in affected |->
                         [t EXCEPT !.status.state = orphaned] ])

(* Actions we require to happen eventually when possible. *)
AgentProgress ==
  \/ ProgressTask
  \/ OrphanTasks
  \/ WorkerUp
  \/ SyncWithManager

(* All actions of the agent/worker. *)
Agent ==
  \/ AgentProgress
  \/ RejectTask
  \/ WorkerDown

-------------------------------------------------------------------------------

CreateTask ==
  /\ UNCHANGED << containers, nEvents, nodes >>
  /\ \E t \in Task :
      /\ Id(t) \notin IdSet(tasks)
      /\ State(t) = new
      /\ t.desired_state \in { ready, running }
      /\ \/ /\ t.node = unassigned
            /\ t.slot \in Slot
         \/ /\ t.node \in Node
            /\ t.slot = global
      /\ tasks' = tasks \union {t}

UpdateTask ==
  /\ UNCHANGED << containers, nEvents, nodes >>
  /\ \E t \in tasks, actor \in DOMAIN Transitions :
      /\ actor = "agent" => t.node # node      \* Any component except ourself
      /\ \E t2 \in Task :
          /\ Id(t) = Id(t2)
          /\ << State(t), State(t2) >> \in Transitions[actor]
          /\ IF State(t2) = assigned /\ t.node = unassigned THEN t2.node \in Node
                                                            ELSE t2.node = t.node
          /\ t2.desired_state \in { ready, running, shutdown, remove }
          /\ t.desired_state \preceq t2.desired_state 
          /\ UpdateTasks(t :> t2)
          
RemoveTask ==
  /\ UNCHANGED << containers, nEvents, nodes >>
  /\ \E t \in tasks :
      /\ << State(t), null >> \in Transitions.reaper
      /\ tasks' = tasks \ {t}

OtherComponent ==
  \/ CreateTask
  \/ UpdateTask
  \/ RemoveTask

-------------------------------------------------------------------------------

vars == << tasks, nEvents, nodes, containers >>

Init ==
  /\ tasks = {}
  /\ containers = << >>
  /\ nodes = [ n \in Node |-> WS!nodeUp ]
  /\ InitEvents

Next ==
  \/ OtherComponent
  \/ Agent

Spec == Init /\ [][Next]_vars /\ WF_vars(AgentProgress)

-------------------------------------------------------------------------------

TypeOK ==
  /\ TasksTypeOK
  \* The node's container map maps IDs to states
  /\ DOMAIN containers \in SUBSET ModelTaskId
  /\ containers \in [ DOMAIN containers -> ContainerState ]

(* Every action the implementation of the agent takes is a valid action in high-level the spec. *)
Refinement ==
  [][Agent => [WS!Agent]_<< tasks, nEvents, nodes >>]_vars

=============================================================================

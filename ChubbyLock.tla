--------------------- MODULE ChubbyLock ---------------------

EXTENDS TLC 

CONSTANT ChubbyCell, Client

ServerRoles == {"master", "replica"}
ClientStatus == {"connected", "idle", "waiting"}

VARIABLES
  servers,
  clients,
  serverState,       \* The state of the transaction manager.
  masterState,    \* The set of RMs from which the TM has received "Prepared"


\* DatabaseData ==		\* available data to add to the database 
\* [“data1”, “data2”, “data3”, “data4”, “data5”] 
   
TypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ servers \in [ServerRoles -> SUBSET ChubbyCell]
  /\ clients \in [ClientStatus -> SUBSET Client]
  /\ serverState \in [ChubbyCell -> {"online", "offline"}]
  /\ masterState \in {"locked", "unlocked"}

Init ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ servers  = [master |-> {r1}, replica |-> ChubbyCell \ {r1}] \* r1 server is initial Master server
  /\ clients \in [connected |-> {}, waiting |-> {}, idle |-> Client]   \* no client connected initially
  /\ serverState = [r \in ChubbyCell |-> "online"]  \* All servers online
  /\ masterState = "unlocked"   \* master initally unlocked

\* Master states
MasterFail(r) == FALSE \* TODO: Define me!
GiveLeasetoClient(r) == FALSE \* TODO: Define me! \* can generate key to give client like Rooms.tla
SyncDatabaseToReplicas(r) == FALSE \* TODO: Define me!

\* Replica states
ReplicaFail(r) == FALSE \* TODO: Define me!
RestartFailServer(r) == FALSE \* TODO: Define me!

ElectNewMaster == FALSE \* TODO: Define me!

\* Client states
SendKeepAliveCall(c) == FALSE \* TODO: Define me!
WriteToDatabase(c) == FALSE \* TODO: Define me!

Next ==
  \/ \E r \in servers["master"] :
       MasterFail(r) \/ GiveLeasetoClient(r) \/ SyncDatabaseToReplicas(r)
  \/ \E r \in servers["replica"] :
       ReplicaFail(r) \/ RestartFailServer(r)
  \/ ElectNewMaster
  \/ \E c \in clients["idle"] :
       SendKeepAliveCall(c)
  \/ \E c \in clients["connected"] :
       WriteToDatabase(c) 
\* how to end lease between client and master?

=============================================================================
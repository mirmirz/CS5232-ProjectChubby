--------------------- MODULE ChubbyLock ---------------------
(***************************************************************************)
(* This specification describes the Chubby Lock Service, in which its      *)
(* general architecture consists of a chubby cell (5 servers) and the      *)
(* clients application (2 clients).  In this specification, we depict      *)
(* the core behaviours of a Chubby Lock Service (i.e. the synchronisation  *)
(* of databases between master-replica) and its loosely coupled behaviour  *)
(* when the master dies.                                                   *)
(***************************************************************************)
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANT 
    Server, \* A set of servers {r1, r2, r3, r4, r5}
    Client, \* A set of clients {c1, c2}
    Data    \* A set of data {d1, d2, d3}

VARIABLES 
    chubbyCell,     \* Variable to store the roles of each server
    clients,        \* Variable to set the state of client 
    databases,      \* Variable to store the database of each server
    masterConnected \* Variable to set the lock/unlock state of the master

ServerRole == {"master", "replica"}     \* Possible roles of each server 
ClientStatus == {"connected", "idle", "waiting"}    \* Possible status of each client 

TypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
    /\ chubbyCell \in [ServerRole -> SUBSET Server]
    /\ clients \in [ClientStatus -> SUBSET Client]
    /\ \A s \in Server: \A d \in databases[s]: d \in Data
    /\ masterConnected \in BOOLEAN

Init ==
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
    LET m == CHOOSE s \in Server : TRUE IN
    /\ chubbyCell = [master |-> {m}, replica |-> Server \ {m}]
    /\ clients = [connected |-> {}, waiting |-> {}, idle |-> Client]
    /\ databases = [s \in Server |-> {}]
    /\ masterConnected = FALSE
-----------------------------------------------------------------------------
(***************************************************************************)
(* States / actions in a Chubby Lock Service                               *)
(***************************************************************************)

HandleMasterFail ==
  (*************************************************************************)
  (* Actions performed when the master fails:                              *)
  (*    - If client still "connected" --> send back client to waiting queue*)
  (*    - The failed master is then added back to the set of replica server*)
  (*************************************************************************)
    /\ \/ /\ masterConnected = TRUE
          /\ \E c \in clients["connected"] : clients' = [clients EXCEPT !["connected"] = {}, !["waiting"] = @ \cup {c}]
       \/ /\ masterConnected = FALSE
          /\ UNCHANGED clients
    /\ \E r \in chubbyCell["replica"] : chubbyCell' = [chubbyCell EXCEPT !["master"] = {r}, !["replica"] = @ \ {r}]
    /\ masterConnected' = FALSE
    /\ UNCHANGED databases

SyncMasterDatabaseToReplicas ==
  (*************************************************************************)
  (* Actions performed when master database is synced to replicas:         *)
  (*    - Only happens when master is not connected to the client          *)
  (*    - After sync, Replica server database == master Database           *)
  (*************************************************************************)
    /\ masterConnected = FALSE
    /\ \E m \in chubbyCell["master"] : databases' = [s \in Server |-> databases[m]]
    /\ UNCHANGED <<chubbyCell, clients, masterConnected>>

SendRequestToConnect(c) ==
  (*************************************************************************)
  (* Actions performed by client attempting to connect to master:          *)
  (*    - clients from Idle will be placed in a waiting queue              *)
  (*************************************************************************)
    /\ c \in clients["idle"]
    /\ clients' = [clients EXCEPT !["waiting"] = @ \cup {c}, !["idle"] = @ \ {c}]
    /\ UNCHANGED <<chubbyCell, databases, masterConnected>>

SendKeepAliveCall(c) ==
  (*************************************************************************)
  (* Actions performed by client sending a keepAlive call to master:       *)
  (*    - client from waiting will be connected master                     *)
  (*************************************************************************)
    /\ masterConnected = FALSE
    /\ c \in clients["waiting"]
    /\ clients' = [clients EXCEPT !["connected"] = {c}, !["waiting"] = @ \ {c}]
    /\ masterConnected' = TRUE
    /\ UNCHANGED <<chubbyCell, databases>>

WriteToDatabase(c) ==
  (*************************************************************************)
  (* Actions performed by client writing to database of master:            *)
  (*    - Client to select random data from Data constant to write in db   *)
  (*    - Master database will include client's changes                    *)
  (*************************************************************************)
    /\ masterConnected = TRUE
    /\ c \in clients["connected"]
    /\ LET d == CHOOSE d \in Data : TRUE IN
       \E m \in chubbyCell["master"]: databases' = [databases EXCEPT ![m] = databases[m] \cup {d}]
    /\ UNCHANGED <<chubbyCell, clients, masterConnected>>

EndLeaseToClient ==
  (*************************************************************************)
  (* Actions performed by master to end connection with client:            *)
  (*    - Client to be sent back to idle                                   *)
  (*    - Master will then be unlocked, open to new connections            *)
  (*************************************************************************)
    /\ masterConnected = TRUE
    /\ \E c \in clients["connected"] : clients' = [clients EXCEPT !["connected"] = {}, !["idle"] = @ \cup {c}]
    /\ masterConnected' = FALSE
    /\ UNCHANGED <<chubbyCell, databases>>

GiveLeaseToClient ==
  (*************************************************************************)
  (* Actions performed by master to establish connection with client:      *)
  (*    - Client in waiting state to be set to connected                   *)
  (*    - Master server will then be locked                                *)
  (*************************************************************************)
    /\ masterConnected = FALSE
    /\ \E c \in clients["waiting"] : clients' = [clients EXCEPT !["connected"] = {c}, !["waiting"] = @ \ {c}]
    /\ masterConnected' = TRUE
    /\ UNCHANGED <<chubbyCell, databases>>

Next ==
    \/ HandleMasterFail
    \/ SyncMasterDatabaseToReplicas
    \/ \E c \in Client: SendRequestToConnect(c) \/ SendKeepAliveCall(c) \/ WriteToDatabase(c)
    \/ EndLeaseToClient
    \/ GiveLeaseToClient

OnlyOneConnection ==
  (*************************************************************************)
  (* Invariant that ensure only 1 connection between master-client can     *)
  (* be established at a time                                              *)
  (*************************************************************************)
    /\ Cardinality(chubbyCell["master"]) <= 1
    /\ chubbyCell["master"] \intersect chubbyCell["replica"] = {}
    /\ Cardinality(clients["connected"]) <= 1
    /\ clients["connected"] \intersect clients["waiting"] \intersect clients["idle"] = {}

-----------------------------------------------------------------------------

databaseSize ==
  (*************************************************************************)
  (* Constraint to ensure the database sizes is max 3                      *)
  (*************************************************************************)
    \A s \in Server : Cardinality(databases[s]) <= 3

CONSTANTS
r1, r2, r3, r4, r5, c1, c2, d1, d2, d3
symm == Permutations({r1, r2, r3, r4, r5}) \cup Permutations({c1, c2}) \cup Permutations({d1, d2, d3})
=============================================================================
--------------------- MODULE ChubbyLock ---------------------
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANT Server, Client, Data

VARIABLES chubbyCell, clients, databases, masterConnected

ServerRole == {"master", "replica"}
ClientStatus == {"connected", "idle", "waiting"}

TypeOK ==
  /\ chubbyCell \in [ServerRole -> SUBSET Server]
  /\ clients \in [ClientStatus -> SUBSET Client]
  /\ \A s \in Server: \A d \in databases[s]: d \in Data
  /\ masterConnected \in BOOLEAN

Init ==
  LET m == CHOOSE s \in Server : TRUE IN
  /\ chubbyCell = [master |-> {m}, replica |-> Server \ {m}]
  /\ clients = [connected |-> {}, waiting |-> {}, idle |-> Client]
  /\ databases = [s \in Server |-> {}]
  /\ masterConnected = FALSE

HandleMasterFail ==
    /\ \/ /\ masterConnected = TRUE
          /\ \E c \in clients["connected"] : clients' = [connected |-> {},
                                                         waiting |-> clients["waiting"] \union {c},
                                                         idle |-> clients["idle"]]
       \/ /\ masterConnected = FALSE
          /\ UNCHANGED clients
    /\ \E r \in chubbyCell["replica"] : chubbyCell' = [master |-> {r}, replica |-> Server \ {r}] \* TODO: just remove server
    /\ masterConnected' = FALSE
    /\ UNCHANGED databases

SyncMasterDatabaseToReplicas ==
    /\ masterConnected = FALSE
    /\ \E m \in chubbyCell["master"] : databases' = [s \in Server |-> databases[m]]
    /\ UNCHANGED <<chubbyCell, clients, masterConnected>>

SendKeepAliveCall(c) ==
    /\ \/ /\ masterConnected = TRUE
          /\ UNCHANGED <<clients, masterConnected>>
       \/ /\ masterConnected = FALSE
          /\ c \in clients["waiting"]
          /\ clients' = [connected |-> {c}, waiting |-> clients["waiting"] \ {c}, idle |-> clients["idle"]]
          /\ masterConnected' = TRUE
    /\ UNCHANGED <<chubbyCell, databases>>

WriteToDatabase(c) ==
    /\ masterConnected = TRUE
    /\ c \in clients["connected"]
    /\ LET d == CHOOSE d \in Data : TRUE IN
       \E m \in chubbyCell["master"]: databases' = [databases EXCEPT ![m] = databases[m] \union {d}]
    /\ UNCHANGED <<chubbyCell, clients, masterConnected>>

EndLeaseToClient ==
    /\ masterConnected = TRUE
    /\ \E c \in clients["connected"] : clients' = [connected |-> {},
                                                   waiting |-> clients["waiting"],
                                                   idle |-> clients["idle"] \union {c}]
    /\ masterConnected' = FALSE
    /\ UNCHANGED <<chubbyCell, databases>>

GiveLeaseToClient ==
    /\ masterConnected = FALSE
    /\ \E c \in clients["waiting"] : clients' = [connected |-> {c},
                                                 waiting |-> clients["waiting"] \ {c},
                                                 idle |-> clients["idle"]]
    /\ masterConnected' = TRUE
    /\ UNCHANGED <<chubbyCell, databases>>

Next ==
  \/ HandleMasterFail
  \/ SyncMasterDatabaseToReplicas
  \/ \E c \in Client: SendKeepAliveCall(c) \/ WriteToDatabase(c)
  \/ EndLeaseToClient
  \/ GiveLeaseToClient

OnlyOneConnection ==
    /\ Cardinality(chubbyCell["master"]) <= 1
    /\ chubbyCell["master"] \intersect chubbyCell["replica"] = {}
    /\ Cardinality(clients["connected"]) <= 1
    /\ clients["connected"] \intersect clients["waiting"] \intersect clients["idle"] = {}

-----------------------------------------------------------------------------

databaseSize ==
    \A s \in Server : Cardinality(databases[s]) <= 3

=============================================================================
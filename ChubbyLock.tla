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
          /\ \E c \in clients["connected"] : clients' = [clients EXCEPT !["connected"] = {}, !["waiting"] = @ \cup {c}]
       \/ /\ masterConnected = FALSE
          /\ UNCHANGED clients
    /\ \E r \in chubbyCell["replica"] : chubbyCell' = [chubbyCell EXCEPT !["master"] = {r}, !["replica"] = @ \ {r}]
    /\ masterConnected' = FALSE
    /\ UNCHANGED databases

SyncMasterDatabaseToReplicas ==
    /\ masterConnected = FALSE
    /\ \E m \in chubbyCell["master"] : databases' = [s \in Server |-> databases[m]]
    /\ UNCHANGED <<chubbyCell, clients, masterConnected>>

SendRequestToConnect(c) ==
    /\ c \in clients["idle"]
    /\ clients' = [clients EXCEPT !["waiting"] = @ \cup {c}, !["idle"] = @ \ {c}]
    /\ UNCHANGED <<chubbyCell, databases, masterConnected>>

SendKeepAliveCall(c) ==
    /\ masterConnected = FALSE
    /\ c \in clients["waiting"]
    /\ clients' = [clients EXCEPT !["connected"] = {c}, !["waiting"] = @ \ {c}]
    /\ masterConnected' = TRUE
    /\ UNCHANGED <<chubbyCell, databases>>

WriteToDatabase(c) ==
    /\ masterConnected = TRUE
    /\ c \in clients["connected"]
    /\ LET d == CHOOSE d \in Data : TRUE IN
       \E m \in chubbyCell["master"]: databases' = [databases EXCEPT ![m] = databases[m] \cup {d}]
    /\ UNCHANGED <<chubbyCell, clients, masterConnected>>

EndLeaseToClient ==
    /\ masterConnected = TRUE
    /\ \E c \in clients["connected"] : clients' = [clients EXCEPT !["connected"] = {}, !["idle"] = @ \cup {c}]
    /\ masterConnected' = FALSE
    /\ UNCHANGED <<chubbyCell, databases>>

GiveLeaseToClient ==
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
    /\ Cardinality(chubbyCell["master"]) <= 1
    /\ chubbyCell["master"] \intersect chubbyCell["replica"] = {}
    /\ Cardinality(clients["connected"]) <= 1
    /\ clients["connected"] \intersect clients["waiting"] \intersect clients["idle"] = {}

-----------------------------------------------------------------------------

databaseSize ==
    \A s \in Server : Cardinality(databases[s]) <= 3

CONSTANTS
r1, r2, r3, r4, r5, c1, c2, d1, d2, d3
symm == Permutations({r1, r2, r3, r4, r5}) \cup Permutations({c1, c2}) \cup Permutations({d1, d2, d3})
=============================================================================
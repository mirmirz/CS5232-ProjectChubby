--------------------- MODULE ChubbyLock_Test ---------------------

EXTENDS TLC 

CONSTANT Client, Resources

VARIABLES
  currentClient,
  requestQueue, //clients who want to connect to server
  lockState, //lock / unlock database of server      
  master,             
  replicas        

Init ==
  /\ currentClient = NULL
  /\ requestQueue = <<>>
  /\ lockState = [r \in Resources |-> "unlocked"]
  /\ master \in replicas
  /\ replicas # {}
  /\ \A node \in replicas: node # master

ClientAcquire(client, resource) ==
  /\ currentClient = client
  /\ resource \in Resources
  /\ <<update lockState to reflect lock acquisition>>
  /\ UNCHANGED <<other state variables>>

ClientRelease(client, resource) ==
  /\ currentClient = client
  /\ resource \in Resources
  /\ <<update lockState to reflect lock release>>
  /\ UNCHANGED <<other state variables>>

MasterUpdateReplicaMap(replicaMap) ==
  /\ master \in replicas
  /\ <<update replica map to replicaMap>>
  /\ UNCHANGED <<other state variables>>

MasterDie ==
  /\ master \in replicas
  /\ replicas' = replicas \ {master}
  /\ \A node \in replicas': node # master
  /\ <<update master to a new node in replicas' or NULL>>
  /\ UNCHANGED <<other state variables>>

MasterStartSync ==
  /\ master \in replicas
  /\ <<start syncing master database with replicas>>
  /\ UNCHANGED <<other state variables>>

MasterFinishSync ==
  /\ master \in replicas
  /\ <<finish syncing master database with replicas>>
  /\ UNCHANGED <<other state variables>>

Next ==
  \/ <<process next client request>>
  \/ <<process next master request>>
  \/ <<handle master death>>
  \/ <<handle master database syncing>>

HandleMasterDeath ==
  /\ master \in replicas
  /\ replicas' = replicas \ {master}
  /\ \A node \in replicas': node # master
  /\ <<update master to a new node in replicas' or NULL>>
  /\ UNCHANGED <<other state variables>>

HandleMasterSyncing ==
  /\ master \in replicas
\*   /\ <<continue handling client requests, but do not process any new master requests>>
  /\ UNCHANGED <<other state variables>>

=============================================================================
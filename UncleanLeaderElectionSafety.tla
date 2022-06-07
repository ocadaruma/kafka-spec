---- MODULE UncleanLeaderElectionSafety ----
EXTENDS Integers, Sequences, FiniteSets, Util

(***** Constants *****)
\* The reason why not CONSTANT here is just for ease of prototyping
Replicas == {1,2,3}
UnstableReplica == 1
MinIsr == 2
MaxLogLen == 3
Producers == {1,2}

(***** Variables that represents system's state *****)
VARIABLES
    \* Logs that acked by all ISRs. i.e. Logs that successful response is returned to producer
    \* Expected to be never lost.
    committedLogs,
    \* Tracks partition's state persisted in ZK.
    \* This is a record in the form of:
    \*    [leaderEpoch |-> Int,
    \*     leader |-> Int,
    \*     isrs |-> Set(Int),
    \*     aliveReplicas |-> Set(Int),
    \*     preferredLeader |-> Int]
    zkState,
    \* Tracks replica's local logs and its states.
    \* Each replica is a record in the form of:
    \*    [localLogs |-> <<[offset |-> Int, leaderEpoch |-> Int, producer |-> Int]>>,
    \*     isShutdown |-> Boolean,
    \*     readyToFetch |-> Boolean]
    replicaStates,
    \* Tracks the set of producers that produced message is in-flight (i.e. not committed).
    \* Used to simulate max.in.flight.requests.per.connection = 1
    inflightProducers

(***** Helpers *****)

\* Shorthand to access local logs of the replica
LocalLogs(replica) == replicaStates[replica].localLogs

\* Log end offset of the replica.
\* Slightly different definition from Kafka's actual leo (i.e. "next offset" of the last appended message)
\* for simplicity. Should be fine as it doesn't affect the verification
Leo(replica) == Last(LocalLogs(replica)).offset

NoLeader == zkState.leader = -1

HighWatermark == Last(committedLogs).offset

\* Partition#isFollowerInSync
IsFollowerInSync(replica) ==
    LET currentEpochLogs == SelectSeq(LocalLogs(zkState.leader), LAMBDA m : m.leaderEpoch = zkState.leaderEpoch)
     IN IF Len(currentEpochLogs) > 0 THEN
            /\ Leo(replica) >= Head(currentEpochLogs).offset
            /\ Leo(replica) >= HighWatermark
        ELSE FALSE

\* The logs that not existed in the replica yet so need to be replicated from leader.
UnreplicatedLogs(replica) ==
    LET leaderLogLen == Len(LocalLogs(zkState.leader))
        i == CHOOSE j \in 1..leaderLogLen : SubSeq(LocalLogs(zkState.leader), 1, j) = LocalLogs(replica)
     IN IF i = leaderLogLen THEN
            \* fully caught up
            <<>>
        ELSE
            SubSeq(LocalLogs(zkState.leader), i + 1, leaderLogLen)

\* Returns truncated log for the replica assuming the newLeader has been elected.
TruncatedLog(replica, newLeader) ==
    LET minLogLen == Min({Len(LocalLogs(replica)), Len(LocalLogs(newLeader))})
        commonPrefixIdx == {i \in 1..minLogLen: SubSeq(LocalLogs(replica), 1, i) = SubSeq(LocalLogs(newLeader), 1, i)}
     IN SubSeq(LocalLogs(replica), 1, Max(commonPrefixIdx))

AppendToLog(replica, log) ==
    Append(LocalLogs(replica), log)

NextOffset(replica) ==
    Last(LocalLogs(replica)).offset + 1

NewReplicaState(localLogs, isShutdown, readyToFetch) ==
    [localLogs |-> localLogs, isShutdown |-> isShutdown, readyToFetch |-> readyToFetch]

(***** Initial state *****)

\* Supply one log at initial just for simplicity so that
\* we can access the element of any logs without considering empty case
Init ==
    /\ committedLogs = <<[offset |-> 1, leaderEpoch |-> 1, producer |-> 1]>>
    /\ zkState = [leaderEpoch |-> 1,
                  leader |-> UnstableReplica,
                  isrs |-> Replicas,
                  aliveReplicas |-> Replicas,
                  preferredLeader |-> UnstableReplica]
    /\ replicaStates = [[replica \in Replicas |-> NewReplicaState(
                                                    <<[offset |-> 1, leaderEpoch |-> 1, producer |-> 1]>>, FALSE, TRUE)]
                            EXCEPT![UnstableReplica] = [@ EXCEPT!.readyToFetch = FALSE]]
    /\ inflightProducers = {}

(***** Actions *****)

ProduceMessage(replica) ==
    \* Assumes producers always have latest leader info
    /\ replica = zkState.leader
    /\ LET readyProducers == Producers \ inflightProducers
        \* further produce not sent until corrent one is committed (max.inflight.requests.per.connection = 1)
        IN /\ Cardinality(readyProducers) > 0
           /\ \E producer \in readyProducers:
                  /\ inflightProducers' = inflightProducers \cup {producer}
                  /\ replicaStates' = [replicaStates EXCEPT![replica] =
                                        [@ EXCEPT!.localLogs = Append(@, [offset |-> NextOffset(replica),
                                                                          leaderEpoch |-> zkState.leaderEpoch,
                                                                          producer |-> producer])]]
                  /\ UNCHANGED <<committedLogs, zkState>>

\* Assumes producers always have latest leader info.
Replicate(replica) ==
    /\ ~NoLeader
    /\ replica /= zkState.leader
    /\ replicaStates[replica].readyToFetch
    /\ LET unreplicatedLogs == UnreplicatedLogs(replica)
        IN /\ Len(unreplicatedLogs) > 0
           /\ \E i \in 1..Len(unreplicatedLogs):
                LET newReplicaStates == [replicaStates EXCEPT![replica] =
                                            [@ EXCEPT!.localLogs = @ \o SubSeq(unreplicatedLogs, 1, i)]]
                    newCommittedLogs ==
                        IF Cardinality(zkState.isrs) >= MinIsr THEN
                            LET minLogLen == Min({Len(newReplicaStates[r].localLogs) : r \in zkState.isrs})
                                committed == {k \in 1..minLogLen: \A r \in zkState.isrs \ {zkState.leader}:
                                                SubSeq(newReplicaStates[r].localLogs, 1, k) =
                                                    SubSeq(newReplicaStates[zkState.leader].localLogs, 1, k)}
                             IN SubSeq(newReplicaStates[zkState.leader].localLogs, 1, Max(committed))
                        ELSE committedLogs
                     IN /\ replicaStates' = newReplicaStates
                        /\ committedLogs' = newCommittedLogs
                        /\ inflightProducers' = inflightProducers \ {newCommittedLogs[r].producer:
                                                                        r \in DOMAIN newCommittedLogs \ DOMAIN committedLogs}
    /\ UNCHANGED <<zkState>>

BecomeOutOfSync(replica) ==
    /\ ~NoLeader
    /\ \/ zkState.leader = UnstableReplica
       \/ replica = UnstableReplica
    /\ replica /= zkState.leader
    /\ replica \in zkState.isrs
    /\ Leo(replica) < Leo(zkState.leader)
    /\ zkState' = [zkState EXCEPT!.isrs = @ \ {replica}]
    /\ LET newIsrs == zkState.isrs \ {replica}
           newCommittedLogs ==
               IF Cardinality(newIsrs) >= MinIsr THEN
                   LET minLogLen == Min({Len(LocalLogs(r)) : r \in newIsrs})
                       committed == {k \in 1..minLogLen: \A r \in newIsrs \ {zkState.leader}:
                                       SubSeq(LocalLogs(r), 1, k) = SubSeq(LocalLogs(zkState.leader), 1, k)}
                    IN SubSeq(LocalLogs(zkState.leader), 1, Max(committed))
               ELSE
                      committedLogs
        IN /\ committedLogs' = newCommittedLogs
           /\ inflightProducers' = inflightProducers \ {newCommittedLogs[r].producer:
                                                           r \in DOMAIN newCommittedLogs \ DOMAIN committedLogs}
    /\ UNCHANGED <<replicaStates>>

BecomeInSync(replica) ==
    /\ ~NoLeader
    /\ replica /= zkState.leader
    /\ replica \notin zkState.isrs
    /\ replica \in zkState.aliveReplicas
    /\ replicaStates[replica].readyToFetch
    /\ IsFollowerInSync(replica)
    /\ zkState' = [zkState EXCEPT!.isrs = @ \cup {replica}]
    /\ UNCHANGED <<committedLogs, replicaStates, inflightProducers>>

PreferredLeaderElection ==
    /\ ~NoLeader
    /\ zkState.preferredLeader /= zkState.leader
    /\ zkState.preferredLeader \in zkState.isrs
    /\ zkState.preferredLeader \in zkState.aliveReplicas
    /\ zkState' = [zkState EXCEPT!.leaderEpoch = zkState.leaderEpoch + 1,
                                 !.leader = zkState.preferredLeader]
    /\ replicaStates' = [r \in Replicas |-> [replicaStates[r] EXCEPT!.readyToFetch = FALSE]]
    /\ UNCHANGED <<committedLogs, inflightProducers>>

SwapPreferredLeader(replica) ==
    /\ replica /= zkState.preferredLeader
    /\ zkState' = [zkState EXCEPT!.preferredLeader = replica]
    /\ UNCHANGED <<committedLogs, replicaStates, inflightProducers>>

LeaderFailure(replica) ==
    /\ replica = UnstableReplica
    /\ zkState.leader = replica
    /\ replica \in zkState.aliveReplicas
    \* https://github.com/apache/kafka/blob/2.4.1/core/src/main/scala/kafka/controller/ReplicaStateMachine.scala#L327
    /\ zkState' = [zkState EXCEPT!.isrs = IF @ = {replica} THEN @ ELSE @ \ {replica},
                                 !.leader = -1,
                                 !.aliveReplicas = @ \ {replica}]
    /\ UNCHANGED <<committedLogs, replicaStates, inflightProducers>>

FailedReplicaBack(replica) ==
    /\ replica \notin zkState.aliveReplicas
    /\ zkState' = [zkState EXCEPT!.aliveReplicas = @ \cup {replica}]
    /\ UNCHANGED <<committedLogs, replicaStates, inflightProducers>>

ShutdownUnstableReplicaWhenLeader ==
    /\ ~replicaStates[UnstableReplica].isShutdown
    /\ zkState.leader = UnstableReplica
    \* https://github.com/apache/kafka/blob/2.4.1/core/src/main/scala/kafka/controller/ReplicaStateMachine.scala#L327
    /\ zkState' = [zkState EXCEPT!.isrs = IF @ = {UnstableReplica} THEN @ ELSE @ \ {UnstableReplica},
                                 !.leader = -1,
                                 !.aliveReplicas = @ \ {UnstableReplica}]
    /\ replicaStates' = [replicaStates EXCEPT![UnstableReplica] = [@ EXCEPT!.isShutdown = TRUE]]
    /\ UNCHANGED <<committedLogs, inflightProducers>>

ShutdownUnstableReplicaWhenFollower ==
    /\ ~replicaStates[UnstableReplica].isShutdown
    /\ zkState.leader /= UnstableReplica
    /\ zkState' = [zkState EXCEPT!.isrs = @ \ {UnstableReplica},
                                 !.aliveReplicas = @ \ {UnstableReplica}]
    /\ replicaStates' = [replicaStates EXCEPT![UnstableReplica] = [@ EXCEPT!.isShutdown = TRUE,
                                                                           !.readyToFetch = FALSE]]
    /\ UNCHANGED <<committedLogs, inflightProducers>>

ElectNewLeader(replica) ==
    /\ NoLeader
    /\ replica \in zkState.isrs
    /\ replica \in zkState.aliveReplicas
    \* On leadership change, left-most isr in replica list will be elected
    /\ replica = Min(zkState.isrs)
    /\ zkState' = [zkState EXCEPT!.leaderEpoch = @ + 1,
                                 !.leader = replica]
    /\ replicaStates' = [r \in Replicas |-> [replicaStates[r] EXCEPT!.readyToFetch = FALSE]]
    /\ UNCHANGED <<committedLogs, inflightProducers>>

BecomeFollower(replica) ==
    /\ ~NoLeader
    /\ replica \in zkState.aliveReplicas
    /\ replica /= zkState.leader
    /\ replicaStates' = [replicaStates EXCEPT![replica] = [@ EXCEPT!.localLogs = TruncatedLog(replica, zkState.leader),
                                                                   !.readyToFetch = TRUE]]
    /\ UNCHANGED <<committedLogs, zkState, inflightProducers>>

UncleanLeaderElectionChooseLargetEpoch ==
    /\ NoLeader
    /\ (zkState.aliveReplicas \cap zkState.isrs) = {}
    /\ replicaStates[UnstableReplica].isShutdown
    /\ LET largestEpochReplicas ==
            {replica \in zkState.aliveReplicas:
                \A other \in zkState.aliveReplicas \ {replica}: Last(LocalLogs(replica)).leaderEpoch >=
                                                                Last(LocalLogs(other)).leaderEpoch}
           longestLogReplicas ==
            {replica \in largestEpochReplicas:
                \A other \in largestEpochReplicas \ {replica}: Last(LocalLogs(replica)).offset >=
                                                                Last(LocalLogs(other)).offset}
        IN \E replica \in longestLogReplicas:
            /\ zkState' = [zkState EXCEPT!.leaderEpoch = @ + 1,
                                         !.leader = replica,
                                         !.isrs = {replica}]
            /\ replicaStates' = [r \in Replicas |-> [replicaStates[r] EXCEPT!.readyToFetch = FALSE]]
            /\ UNCHANGED <<committedLogs, inflightProducers>>

(***** Define all possible transistions *****)

Next ==
    \/ \E replica \in Replicas:
        \/ ProduceMessage(replica)
        \/ Replicate(replica)
        \/ BecomeOutOfSync(replica)
        \/ BecomeInSync(replica)
        \/ LeaderFailure(replica)
        \/ ElectNewLeader(replica)
        \/ FailedReplicaBack(replica)
        \/ SwapPreferredLeader(replica)
        \/ BecomeFollower(replica)
    \/ ShutdownUnstableReplicaWhenLeader
    \/ ShutdownUnstableReplicaWhenFollower
    \/ PreferredLeaderElection
    \/ UncleanLeaderElectionChooseLargetEpoch

(***** Invariants *****)

CommittedLogNotLost == NoLeader \/ ContainsSeq(LocalLogs(zkState.leader), committedLogs)
====

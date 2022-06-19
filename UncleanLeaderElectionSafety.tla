---- MODULE UncleanLeaderElectionSafety ----
EXTENDS Integers, Sequences, FiniteSets, Util

CONSTANTS
    Replicas,
    UnstableReplica,
    MinIsr,
    Producers

VARIABLES
    committedMessages,
    zkState,
    replicaStates,
    inflightProducers

\* Shorthand to access local logs of the replica
LocalLog(replica) == replicaStates[replica].localLog

\* Log end offset of the replica.
\* Slightly different definition from Kafka's actual leo (i.e. "next offset" of the last appended message)
\* for simplicity. Should be fine as it doesn't affect the verification
Leo(replica) == Last(LocalLog(replica)).offset

NoLeader == zkState.leader = -1

HighWatermark == Last(committedMessages).offset

\* Partition#isFollowerInSync
IsFollowerInSync(replica) ==
    LET currentEpochLogs == SelectSeq(LocalLog(zkState.leader), LAMBDA m : m.leaderEpoch = zkState.leaderEpoch)
     IN IF Len(currentEpochLogs) > 0 THEN
            /\ Leo(replica) >= Head(currentEpochLogs).offset
            /\ Leo(replica) >= HighWatermark
        ELSE FALSE

\* The logs that not existed in the replica yet so need to be replicated from leader.
UnreplicatedLogs(replica) ==
    LET leaderLogLen == Len(LocalLog(zkState.leader))
        i == CHOOSE j \in 1..leaderLogLen : SubSeq(LocalLog(zkState.leader), 1, j) = LocalLog(replica)
     IN IF i = leaderLogLen THEN
            \* fully caught up
            <<>>
        ELSE
            SubSeq(LocalLog(zkState.leader), i + 1, leaderLogLen)

\* Returns truncated log for the replica assuming the newLeader has been elected.
TruncatedLog(replica, newLeader) ==
    LET minLogLen == Min({Len(LocalLog(replica)), Len(LocalLog(newLeader))})
        commonPrefixIdx == {i \in 1..minLogLen: SubSeq(LocalLog(replica), 1, i) = SubSeq(LocalLog(newLeader), 1, i)}
     IN SubSeq(LocalLog(replica), 1, Max(commonPrefixIdx))

AppendToLog(replica, log) ==
    Append(LocalLog(replica), log)

NextOffset(replica) ==
    Last(LocalLog(replica)).offset + 1

NewReplicaState(localLog, isShutdown, readyToFetch) ==
    [localLog |-> localLog, isShutdown |-> isShutdown, readyToFetch |-> readyToFetch]

(***** Initial state *****)

\* Supply one log at initial just for simplicity so that
\* we can access the element of any logs without considering empty case
Init ==
    /\ committedMessages = <<[offset |-> 1, leaderEpoch |-> 1, producer |-> 1]>>
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
                                        [@ EXCEPT!.localLog = Append(@, [offset |-> NextOffset(replica),
                                                                         leaderEpoch |-> zkState.leaderEpoch,
                                                                         producer |-> producer])]]
                  /\ UNCHANGED <<committedMessages, zkState>>

\* Assumes producers always have latest leader info.
Replicate(replica) ==
    /\ ~NoLeader
    /\ replica /= zkState.leader
    /\ replicaStates[replica].readyToFetch
    /\ LET unreplicatedLogs == UnreplicatedLogs(replica)
        IN /\ Len(unreplicatedLogs) > 0
           /\ \E i \in 1..Len(unreplicatedLogs):
                LET newReplicaStates == [replicaStates EXCEPT![replica] =
                                            [@ EXCEPT!.localLog = @ \o SubSeq(unreplicatedLogs, 1, i)]]
                    newCommittedMessages ==
                        IF Cardinality(zkState.isrs) >= MinIsr THEN
                            LET minLogLen == Min({Len(newReplicaStates[r].localLog) : r \in zkState.isrs})
                                committed == {k \in 1..minLogLen: \A r \in zkState.isrs \ {zkState.leader}:
                                                SubSeq(newReplicaStates[r].localLog, 1, k) =
                                                    SubSeq(newReplicaStates[zkState.leader].localLog, 1, k)}
                             IN SubSeq(newReplicaStates[zkState.leader].localLog, 1, Max(committed))
                        ELSE committedMessages
                     IN /\ replicaStates' = newReplicaStates
                        /\ committedMessages' = newCommittedMessages
                        /\ inflightProducers' = inflightProducers \ {newCommittedMessages[r].producer:
                                                                        r \in DOMAIN newCommittedMessages \ DOMAIN committedMessages}
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
           newCommittedMessages ==
               IF Cardinality(newIsrs) >= MinIsr THEN
                   LET minLogLen == Min({Len(LocalLog(r)) : r \in newIsrs})
                       committed == {k \in 1..minLogLen: \A r \in newIsrs \ {zkState.leader}:
                                       SubSeq(LocalLog(r), 1, k) = SubSeq(LocalLog(zkState.leader), 1, k)}
                    IN SubSeq(LocalLog(zkState.leader), 1, Max(committed))
               ELSE
                      committedMessages
        IN /\ committedMessages' = newCommittedMessages
           /\ inflightProducers' = inflightProducers \ {newCommittedMessages[r].producer:
                                                           r \in DOMAIN newCommittedMessages \ DOMAIN committedMessages}
    /\ UNCHANGED <<replicaStates>>

BecomeInSync(replica) ==
    /\ ~NoLeader
    /\ replica /= zkState.leader
    /\ replica \notin zkState.isrs
    /\ replica \in zkState.aliveReplicas
    /\ replicaStates[replica].readyToFetch
    /\ IsFollowerInSync(replica)
    /\ zkState' = [zkState EXCEPT!.isrs = @ \cup {replica}]
    /\ UNCHANGED <<committedMessages, replicaStates, inflightProducers>>

PreferredLeaderElection ==
    /\ ~NoLeader
    /\ zkState.preferredLeader /= zkState.leader
    /\ zkState.preferredLeader \in zkState.isrs
    /\ zkState.preferredLeader \in zkState.aliveReplicas
    /\ zkState' = [zkState EXCEPT!.leaderEpoch = zkState.leaderEpoch + 1,
                                 !.leader = zkState.preferredLeader]
    /\ replicaStates' = [r \in Replicas |-> [replicaStates[r] EXCEPT!.readyToFetch = FALSE]]
    /\ UNCHANGED <<committedMessages, inflightProducers>>

SwapPreferredLeader(replica) ==
    /\ replica /= zkState.preferredLeader
    /\ zkState' = [zkState EXCEPT!.preferredLeader = replica]
    /\ UNCHANGED <<committedMessages, replicaStates, inflightProducers>>

LeaderFailure(replica) ==
    /\ replica = UnstableReplica
    /\ zkState.leader = replica
    /\ replica \in zkState.aliveReplicas
    \* https://github.com/apache/kafka/blob/2.4.1/core/src/main/scala/kafka/controller/ReplicaStateMachine.scala#L327
    /\ zkState' = [zkState EXCEPT!.isrs = IF @ = {replica} THEN @ ELSE @ \ {replica},
                                 !.leader = -1,
                                 !.aliveReplicas = @ \ {replica}]
    /\ UNCHANGED <<committedMessages, replicaStates, inflightProducers>>

FailedReplicaBack(replica) ==
    /\ replica \notin zkState.aliveReplicas
    /\ zkState' = [zkState EXCEPT!.aliveReplicas = @ \cup {replica}]
    /\ UNCHANGED <<committedMessages, replicaStates, inflightProducers>>

UnstableReplicaDiesWhenLeader ==
    /\ ~replicaStates[UnstableReplica].isShutdown
    /\ zkState.leader = UnstableReplica
    \* https://github.com/apache/kafka/blob/2.4.1/core/src/main/scala/kafka/controller/ReplicaStateMachine.scala#L327
    /\ zkState' = [zkState EXCEPT!.isrs = IF @ = {UnstableReplica} THEN @ ELSE @ \ {UnstableReplica},
                                 !.leader = -1,
                                 !.aliveReplicas = @ \ {UnstableReplica}]
    /\ replicaStates' = [replicaStates EXCEPT![UnstableReplica] = [@ EXCEPT!.isShutdown = TRUE]]
    /\ UNCHANGED <<committedMessages, inflightProducers>>

UnstableReplicaDiesWhenFollower ==
    /\ ~replicaStates[UnstableReplica].isShutdown
    /\ zkState.leader /= UnstableReplica
    /\ zkState' = [zkState EXCEPT!.isrs = @ \ {UnstableReplica},
                                 !.aliveReplicas = @ \ {UnstableReplica}]
    /\ replicaStates' = [replicaStates EXCEPT![UnstableReplica] = [@ EXCEPT!.isShutdown = TRUE,
                                                                           !.readyToFetch = FALSE]]
    /\ UNCHANGED <<committedMessages, inflightProducers>>

ElectNewLeader(replica) ==
    /\ NoLeader
    /\ replica \in zkState.isrs
    /\ replica \in zkState.aliveReplicas
    \* On leadership change, left-most isr in replica list will be elected
    /\ replica = Min(zkState.isrs)
    /\ zkState' = [zkState EXCEPT!.leaderEpoch = @ + 1,
                                 !.leader = replica]
    /\ replicaStates' = [r \in Replicas |-> [replicaStates[r] EXCEPT!.readyToFetch = FALSE]]
    /\ UNCHANGED <<committedMessages, inflightProducers>>

BecomeFollower(replica) ==
    /\ ~NoLeader
    /\ replica \in zkState.aliveReplicas
    /\ replica /= zkState.leader
    /\ replicaStates' = [replicaStates EXCEPT![replica] = [@ EXCEPT!.localLog = TruncatedLog(replica, zkState.leader),
                                                                   !.readyToFetch = TRUE]]
    /\ UNCHANGED <<committedMessages, zkState, inflightProducers>>

UncleanLeaderElectionChooseLatestOffset ==
    /\ NoLeader
    /\ (zkState.aliveReplicas \cap zkState.isrs) = {}
    /\ replicaStates[UnstableReplica].isShutdown
    /\ LET largestEpochReplicas ==
            {replica \in zkState.aliveReplicas:
                \A other \in zkState.aliveReplicas \ {replica}: Last(LocalLog(replica)).leaderEpoch >=
                                                                Last(LocalLog(other)).leaderEpoch}
           longestLogReplicas ==
            {replica \in largestEpochReplicas:
                \A other \in largestEpochReplicas \ {replica}: Last(LocalLog(replica)).offset >=
                                                                Last(LocalLog(other)).offset}
        IN \E replica \in longestLogReplicas:
            /\ zkState' = [zkState EXCEPT!.leaderEpoch = @ + 1,
                                         !.leader = replica,
                                         !.isrs = {replica}]
            /\ replicaStates' = [r \in Replicas |-> [replicaStates[r] EXCEPT!.readyToFetch = FALSE]]
            /\ UNCHANGED <<committedMessages, inflightProducers>>

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
    \/ UnstableReplicaDiesWhenLeader
    \/ UnstableReplicaDiesWhenFollower
    \/ PreferredLeaderElection
    \/ UncleanLeaderElectionChooseLatestOffset

(***** Invariants *****)
CommittedMessagesNeverLost ==
    NoLeader \/ ContainsSeq(LocalLog(zkState.leader), committedMessages)
====

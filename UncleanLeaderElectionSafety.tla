---- MODULE UncleanLeaderElectionSafety ----
EXTENDS Integers, Sequences, FiniteSets, Util, TLC

\* Just use operator instead of constant for smooth prototyping
Brokers == 1..3
UnstableBroker == 1
MinISR == 2

VARIABLES
    \* sequence of records ([offset |-> integer, leaderEpoch |-> integer]) that
    \* replicated to all insync replicas (i.e. producer with acks=all received successful response)
    committedLogs,
    nextOffset,
    leaderEpoch,
    highWatermark,
    localLogs,
    aliveBrokers,
    isrs,
    leader

\* Helper functions

\* Slightly different definition from Kafka's actual leo (i.e. "next offset" against last appended message)
\* for simplicity. Should be fine as it doesn't affect the verification
Leo(broker) == Last(localLogs[broker]).offset

LeaderEpochStartOffset ==
        LET currentEpochLogs == SelectSeq(localLogs[leader], LAMBDA m : m.leaderEpoch = leaderEpoch)
         IN IF Len(currentEpochLogs) > 0 THEN
               currentEpochLogs[1].offset
            ELSE
               Last(SelectSeq(localLogs[leader], LAMBDA m : m.leaderEpoch = leaderEpoch - 1)).offset + 1

UnreplicatedLogs(broker) ==
        LET i == CHOOSE j \in 1..Len(localLogs[leader]) : SubSeq(localLogs[leader], 1, j) = localLogs[broker]
         IN IF i = Len(localLogs[leader]) THEN
                \* fully caught up
                <<>>
            ELSE
                SubSeq(localLogs[leader], i + 1, Len(localLogs[leader]))

NoLeader == leader = -1

TruncatedLog(broker, newLeader) ==
        LET lastLeaderEpoch == Last(localLogs[newLeader]).leaderEpoch
            lastOffset == Last(localLogs[newLeader]).offset
         IN SelectSeq(localLogs[broker], LAMBDA m : m.leaderEpoch < lastLeaderEpoch \/
                                                    (m.leaderEpoch = lastLeaderEpoch /\ m.offset <= lastOffset))

\* Supply one log at initial just for simplicity so that
\* we can retrieve the element of logs without considering empty case
Init == /\ committedLogs = <<[offset |-> 1, leaderEpoch |-> 1]>>
        /\ nextOffset = 2
        /\ leaderEpoch = 1
        /\ highWatermark = 1
        /\ localLogs = [broker \in Brokers |-> <<[offset |-> 1, leaderEpoch |-> 1]>>]
        /\ aliveBrokers = Brokers
        /\ isrs = Brokers
        /\ leader = UnstableBroker

AppendToLeader ==
        /\ leader \in aliveBrokers
        \* further produce not sent until corrent one is committed
        /\ localLogs[leader] = committedLogs
        /\ nextOffset' = nextOffset + 1
        /\ localLogs' = [localLogs EXCEPT![leader] = Append(@, [offset |-> nextOffset, leaderEpoch |-> leaderEpoch])]
        /\ UNCHANGED <<committedLogs, leaderEpoch, highWatermark, aliveBrokers, isrs, leader>>

Replicate(broker) ==
        /\ ~NoLeader
        /\ broker \in aliveBrokers
        /\ broker /= leader
        /\ LET unreplicatedLogs == UnreplicatedLogs(broker)
            IN IF Len(unreplicatedLogs) = 0 THEN
                    /\ localLogs' = localLogs
                    /\ highWatermark' = highWatermark
                    /\ committedLogs' = committedLogs
               ELSE
                    \E i \in 1..Len(unreplicatedLogs):
                        LET newLocalLogs == [localLogs EXCEPT![broker] = @ \o SubSeq(unreplicatedLogs, 1, i)]
                            newCommittedLogs ==
                                IF Cardinality(isrs) >= MinISR THEN
                                    LET minLogLen == Min({Len(newLocalLogs[b]) : b \in isrs})
                                        committed == {k \in 1..minLogLen: \A b \in isrs \ {leader}:
                                                        SubSeq(newLocalLogs[b], 1, k) = SubSeq(newLocalLogs[leader], 1, k)}
                                     IN SubSeq(newLocalLogs[leader], 1, Max(committed))
                                ELSE
                                       committedLogs
                         IN /\ localLogs' = newLocalLogs
                            /\ highWatermark' = Last(newCommittedLogs).offset
                            /\ committedLogs' = newCommittedLogs
        /\ UNCHANGED <<nextOffset, leaderEpoch, aliveBrokers, isrs, leader>>

BecomeOutOfSync(broker) ==
        /\ ~NoLeader
        /\ broker /= leader
        /\ broker \in isrs
        /\ Leo(broker) < Leo(leader)
        /\ isrs' = isrs \ {broker}
        /\ LET newIsrs == isrs \ {broker}
               newCommittedLogs ==
                   IF Cardinality(newIsrs) >= MinISR THEN
                       LET minLogLen == Min({Len(localLogs[b]) : b \in newIsrs})
                           committed == {k \in 1..minLogLen: \A b \in newIsrs \ {leader}:
                                           SubSeq(localLogs[b], 1, k) = SubSeq(localLogs[leader], 1, k)}
                        IN SubSeq(localLogs[leader], 1, Max(committed))
                   ELSE
                          committedLogs
            IN /\ committedLogs' = newCommittedLogs
               /\ highWatermark' = Last(newCommittedLogs).offset
        /\ UNCHANGED <<nextOffset, leaderEpoch, localLogs, aliveBrokers, leader>>

BecomeInSync(broker) ==
        /\ ~NoLeader
        /\ broker /= leader
        /\ broker \notin isrs
        /\ broker \in aliveBrokers
        \* condition in Partition#isFollowerInSync
        /\ /\ Leo(broker) >= highWatermark
           /\ Leo(broker) >= LeaderEpochStartOffset
        /\ isrs' = isrs \cup {broker}
        /\ UNCHANGED <<committedLogs, nextOffset, leaderEpoch, highWatermark, localLogs, aliveBrokers, leader>>

ShutdownUnstableLeader ==
        /\ leader = UnstableBroker
        /\ UnstableBroker \in aliveBrokers
        /\ isrs = {UnstableBroker}
        /\ aliveBrokers' = aliveBrokers \ {UnstableBroker}
        /\ leader' = -1
        /\ UNCHANGED <<committedLogs, nextOffset, leaderEpoch, highWatermark, localLogs, isrs>>

UncleanLeaderElection ==
        /\ NoLeader
        /\ \E broker \in aliveBrokers:
            /\ nextOffset' = Last(localLogs[broker]).offset + 1
            /\ leaderEpoch' = leaderEpoch + 1
            /\ isrs' = {broker}
            /\ leader' = broker
            /\ \A f \in aliveBrokers \ {broker}:
                localLogs' = [localLogs EXCEPT![f] = TruncatedLog(f, broker)]
            /\ UNCHANGED <<committedLogs, highWatermark, aliveBrokers>>

Next == \/ AppendToLeader
        \/ \E broker \in Brokers: Replicate(broker)
        \/ \E broker \in Brokers: BecomeOutOfSync(broker)
        \/ \E broker \in Brokers: BecomeInSync(broker)
        \/ ShutdownUnstableLeader
        \/ UncleanLeaderElection

\* Invariants
CommittedLogNotLost == NoLeader \/ IsSubSeq(committedLogs, localLogs[leader])
====

---- MODULE UncleanLeaderElectionSafety ----
EXTENDS Integers, Sequences, FiniteSets, Util, TLC

\* Just use operator instead of constant for smooth prototyping
Brokers == 1..3
UnstableBroker == 1
MinIsr == 2

VARIABLES
    \* sequence of records ([offset |-> integer, leaderEpoch |-> integer]) that
    \* replicated to all insync replicas (i.e. producer with acks=all received successful response)
    committedLogs,
    nextOffset,
    leaderEpoch,
    localLogs,
    aliveBrokers,
    isrs,
    leader

\* Helpers

\* Slightly different definition from Kafka's actual leo (i.e. "next offset" against last appended message)
\* for simplicity. Should be fine as it doesn't affect the verification
Leo(broker) ==
    Last(localLogs[broker]).offset

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

NoLeader ==
    leader = -1

HighWatermark ==
    Last(committedLogs).offset

TruncatedLog(broker, newLeader) ==
    LET lastLeaderEpoch == Last(localLogs[newLeader]).leaderEpoch
        lastOffset == Last(localLogs[newLeader]).offset
     IN SelectSeq(localLogs[broker], LAMBDA m : m.leaderEpoch < lastLeaderEpoch \/
                                                (m.leaderEpoch = lastLeaderEpoch /\ m.offset <= lastOffset))

\* Supply one log at initial just for simplicity so that
\* we can retrieve the element of logs without considering empty case
Init ==
    /\ committedLogs = <<[offset |-> 1, leaderEpoch |-> 1]>>
    /\ nextOffset = 2
    /\ leaderEpoch = 1
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
    /\ UNCHANGED <<committedLogs, leaderEpoch, aliveBrokers, isrs, leader>>

Replicate(broker) ==
    /\ ~NoLeader
    /\ broker \in aliveBrokers
    /\ broker /= leader
    /\ LET unreplicatedLogs == UnreplicatedLogs(broker)
        IN IF Len(unreplicatedLogs) = 0 THEN
                /\ localLogs' = localLogs
                /\ committedLogs' = committedLogs
           ELSE
                \E i \in 1..Len(unreplicatedLogs):
                    LET newLocalLogs == [localLogs EXCEPT![broker] = @ \o SubSeq(unreplicatedLogs, 1, i)]
                        newCommittedLogs ==
                            IF Cardinality(isrs) >= MinIsr THEN
                                LET minLogLen == Min({Len(newLocalLogs[b]) : b \in isrs})
                                    committed == {k \in 1..minLogLen: \A b \in isrs \ {leader}:
                                                    SubSeq(newLocalLogs[b], 1, k) = SubSeq(newLocalLogs[leader], 1, k)}
                                 IN SubSeq(newLocalLogs[leader], 1, Max(committed))
                            ELSE
                                   committedLogs
                     IN /\ localLogs' = newLocalLogs
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
               IF Cardinality(newIsrs) >= MinIsr THEN
                   LET minLogLen == Min({Len(localLogs[b]) : b \in newIsrs})
                       committed == {k \in 1..minLogLen: \A b \in newIsrs \ {leader}:
                                       SubSeq(localLogs[b], 1, k) = SubSeq(localLogs[leader], 1, k)}
                    IN SubSeq(localLogs[leader], 1, Max(committed))
               ELSE
                      committedLogs
        IN /\ committedLogs' = newCommittedLogs
    /\ UNCHANGED <<nextOffset, leaderEpoch, localLogs, aliveBrokers, leader>>

BecomeInSync(broker) ==
    /\ ~NoLeader
    /\ broker /= leader
    /\ broker \notin isrs
    /\ broker \in aliveBrokers
    \* condition in Partition#isFollowerInSync
    /\ /\ Leo(broker) >= HighWatermark
       /\ Leo(broker) >= LeaderEpochStartOffset
    /\ isrs' = isrs \cup {broker}
    /\ UNCHANGED <<committedLogs, nextOffset, leaderEpoch, localLogs, aliveBrokers, leader>>

ShutdownUnstableLeader ==
    /\ leader = UnstableBroker
    /\ UnstableBroker \in aliveBrokers
    /\ isrs = {UnstableBroker}
    /\ aliveBrokers' = aliveBrokers \ {UnstableBroker}
    /\ leader' = -1
    /\ UNCHANGED <<committedLogs, nextOffset, leaderEpoch, localLogs, isrs>>

\*UncleanLeaderElection ==
\*    /\ NoLeader
\*    /\ \E broker \in aliveBrokers:
\*        /\ nextOffset' = Last(localLogs[broker]).offset + 1
\*        /\ leaderEpoch' = leaderEpoch + 1
\*        /\ isrs' = {broker}
\*        /\ leader' = broker
\*        /\ \A f \in aliveBrokers \ {broker}:
\*            localLogs' = [localLogs EXCEPT![f] = TruncatedLog(f, broker)]
\*        /\ UNCHANGED <<committedLogs, aliveBrokers>>

\* Modified version that elect new leader that has longest local log
UncleanLeaderElection2 ==
    /\ NoLeader
    /\ LET longestLogBrokers ==
            {broker \in aliveBrokers:
                \A other \in aliveBrokers \ {broker}: Len(localLogs[broker]) >= Len(localLogs[other])}
        IN \E broker \in longestLogBrokers:
            /\ nextOffset' = Last(localLogs[broker]).offset + 1
            /\ leaderEpoch' = leaderEpoch + 1
            /\ isrs' = {broker}
            /\ leader' = broker
            /\ \A f \in aliveBrokers \ {broker}:
                localLogs' = [localLogs EXCEPT![f] = TruncatedLog(f, broker)]
            /\ UNCHANGED <<committedLogs, aliveBrokers>>

Next ==
    \/ AppendToLeader
    \/ \E broker \in Brokers: Replicate(broker)
    \/ \E broker \in Brokers: BecomeOutOfSync(broker)
    \/ \E broker \in Brokers: BecomeInSync(broker)
    \/ ShutdownUnstableLeader
\*    \/ UncleanLeaderElection
    \/ UncleanLeaderElection2

\* Invariants
CommittedLogNotLost ==
    NoLeader \/ ContainsSeq(localLogs[leader], committedLogs)
====

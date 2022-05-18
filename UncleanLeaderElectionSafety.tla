---- MODULE UncleanLeaderElectionSafety ----
EXTENDS Integers, Sequences, FiniteSets, Util

CONSTANTS
    \* @type: Set(Int);
    Brokers,
    \* @type: Int;
    UnstableBroker,
    \* @type: Int;
    MinIsr,
    \* @type: Int;
    MaxLogLen,
    \* @type: Set(Int);
    Producers

ASSUME
    /\ Brokers \subseteq Nat
    /\ UnstableBroker \in Brokers
    /\ MinIsr \in Nat /\ MinIsr > 0 /\ MinIsr <= Cardinality(Brokers)
    /\ MaxLogLen \in Nat /\ MaxLogLen > 0
    /\ Producers \subseteq Nat

VARIABLES
    \* sequence of records ([offset |-> integer, leaderEpoch |-> integer]) that
    \* replicated to all insync replicas (i.e. producer with acks=all received successful response)

    \* @type: Seq([offset: Int, leaderEpoch: Int, producer: Int]);
    committedLogs,
    \* @type: Int;
    nextOffset,
    \* @type: Int;
    leaderEpoch,
    \* @type: Int -> Seq([offset: Int, leaderEpoch: Int, producer: Int]);
    localLogs,
    \* @type: Set(Int);
    aliveBrokers,
    \* @type: Set(Int);
    readyToFetchBrokers,
    \* @type: Set(Int);
    isrs,
    \* @type: Int;
    leader,
    \* @type: Set(Int);
    inflightProducers,
    \* @type: Int;
    preferredLeader

vars == <<committedLogs,
          nextOffset,
          leaderEpoch,
          localLogs,
          aliveBrokers,
          readyToFetchBrokers,
          isrs,
          leader,
          inflightProducers,
          preferredLeader>>

TypeOK ==
    /\ \A i \in DOMAIN committedLogs: committedLogs[i] \in [{"offset", "leaderEpoch", "producer"} -> Int]
    /\ nextOffset \in Int
    /\ leaderEpoch \in Int
    /\ aliveBrokers \subseteq Brokers
    /\ readyToFetchBrokers \subseteq Brokers
    /\ isrs \subseteq Brokers
    /\ leader = -1 \/ leader \in Brokers
    /\ inflightProducers \subseteq Producers
    /\ preferredLeader \in Brokers

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
            Last(localLogs[leader]).offset + 1

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
    LET minLogLen == Min({Len(localLogs[broker]), Len(localLogs[newLeader])})
        commonPrefixIdx == {i \in 1..minLogLen: SubSeq(localLogs[broker], 1, i) = SubSeq(localLogs[newLeader], 1, i)}
     IN SubSeq(localLogs[broker], 1, Max(commonPrefixIdx))

\* Supply one log at initial just for simplicity so that
\* we can retrieve the element of logs without considering empty case
Init ==
    /\ committedLogs = <<[offset |-> 1, leaderEpoch |-> 1, producer |-> 1]>>
    /\ nextOffset = 2
    /\ leaderEpoch = 1
    /\ localLogs = [broker \in Brokers |-> <<[offset |-> 1, leaderEpoch |-> 1, producer |-> 1]>>]
    /\ aliveBrokers = Brokers
    /\ isrs = Brokers
    /\ leader = UnstableBroker
    /\ readyToFetchBrokers = Brokers \ {leader}
    /\ inflightProducers = {}
    /\ preferredLeader = 1

AppendToLeader ==
    /\ leader \in aliveBrokers
    /\ Len(localLogs[leader]) <= MaxLogLen
    /\ LET readyProducers == Producers \ inflightProducers
        \* further produce not sent until corrent one is committed (max.inflight.requests.per.connection = 1)
        IN /\ Cardinality(readyProducers) > 0
           /\ \E p \in readyProducers:
                /\ nextOffset' = nextOffset + 1
                /\ localLogs' = [localLogs EXCEPT![leader] = Append(@, [offset |-> nextOffset,
                                                                        leaderEpoch |-> leaderEpoch,
                                                                        producer |-> p])]
                /\ inflightProducers' = inflightProducers \cup {p}
                /\ UNCHANGED <<committedLogs, leaderEpoch, aliveBrokers, isrs, leader, readyToFetchBrokers, preferredLeader>>

Replicate(broker) ==
    /\ ~NoLeader
    /\ broker \in aliveBrokers
    /\ broker \in readyToFetchBrokers
    /\ broker /= leader
    /\ LET unreplicatedLogs == UnreplicatedLogs(broker)
        IN IF Len(unreplicatedLogs) = 0 THEN
                /\ localLogs' = localLogs
                /\ committedLogs' = committedLogs
                /\ UNCHANGED <<inflightProducers>>
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
                        /\ inflightProducers' = inflightProducers \ {newCommittedLogs[r].producer:
                                                                        r \in DOMAIN newCommittedLogs \ DOMAIN committedLogs}
    /\ UNCHANGED <<nextOffset, leaderEpoch, aliveBrokers, isrs, leader, readyToFetchBrokers, preferredLeader>>

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
           /\ inflightProducers' = inflightProducers \ {newCommittedLogs[r].producer:
                                                           r \in DOMAIN newCommittedLogs \ DOMAIN committedLogs}
    /\ UNCHANGED <<nextOffset, leaderEpoch, localLogs, aliveBrokers, leader, readyToFetchBrokers, preferredLeader>>

BecomeInSync(broker) ==
    /\ ~NoLeader
    /\ broker /= leader
    /\ broker \notin isrs
    /\ broker \in aliveBrokers
    /\ broker \in readyToFetchBrokers
    \* condition in Partition#isFollowerInSync
    /\ /\ Leo(broker) >= HighWatermark
       /\ Leo(broker) >= LeaderEpochStartOffset
    /\ isrs' = isrs \cup {broker}
    /\ UNCHANGED <<committedLogs,
                   nextOffset,
                   leaderEpoch,
                   localLogs,
                   aliveBrokers,
                   leader,
                   readyToFetchBrokers,
                   inflightProducers,
                   preferredLeader>>

PreferredLeaderElection ==
    /\ ~NoLeader
    /\ preferredLeader /= leader
    /\ preferredLeader \in isrs
    /\ preferredLeader \in aliveBrokers
    /\ nextOffset' = Last(localLogs[preferredLeader]).offset + 1
    /\ leaderEpoch' = leaderEpoch + 1
    /\ leader' = preferredLeader
    /\ readyToFetchBrokers' = {}
    /\ UNCHANGED <<committedLogs, localLogs, aliveBrokers, isrs, inflightProducers, preferredLeader>>

SwapLeadership(broker) ==
    /\ leader = UnstableBroker
    /\ broker /= leader
    /\ broker \in isrs
    /\ broker \in aliveBrokers
    /\ nextOffset' = Last(localLogs[broker]).offset + 1
    /\ leaderEpoch' = leaderEpoch + 1
    /\ leader' = broker
    /\ readyToFetchBrokers' = {}
    /\ preferredLeader' = broker
    /\ UNCHANGED <<committedLogs, localLogs, aliveBrokers, isrs, inflightProducers>>

\*ElectNewLeaderBecauseCurrentLeaderGotLost(broker) ==
\*    /\ ~NoLeader
\*    /\ broker /= leader
\*    /\ broker \in isrs
\*    /\ broker \in aliveBrokers
\*    \* On leadership change, left-most isr in replica list will be elected
\*    /\ broker = Min(isrs \ {leader})
\*    /\ nextOffset' = Last(localLogs[broker]).offset + 1
\*    /\ leaderEpoch' = leaderEpoch + 1
\*    /\ leader' = broker
\*    /\ readyToFetchBrokers' = {}
\*    /\ isrs' = isrs \ {leader}
\*    /\ UNCHANGED <<committedLogs, localLogs, aliveBrokers, inflightProducers, preferredLeader>>

\*ShutdownUnstableLeader ==
\*    /\ leader = UnstableBroker
\*    /\ UnstableBroker \in aliveBrokers
\*    /\ isrs = {UnstableBroker}
\*    /\ aliveBrokers' = aliveBrokers \ {UnstableBroker}
\*    /\ leader' = -1
\*    /\ UNCHANGED <<committedLogs, nextOffset, leaderEpoch, localLogs, isrs, readyToFetchBrokers, inflightProducers, preferredLeader>>

LeaderFailure(broker) ==
    /\ broker = UnstableBroker
    /\ ~NoLeader
    /\ leader = broker
    /\ broker \in aliveBrokers
    /\ broker \in isrs
    /\ aliveBrokers' = aliveBrokers \ {broker}
    /\ isrs' = isrs \ {broker}
    /\ leader' = -1
    /\ UNCHANGED <<committedLogs, nextOffset, leaderEpoch, localLogs, readyToFetchBrokers, inflightProducers, preferredLeader>>

ElectNewLeader(broker) ==
    /\ NoLeader
    /\ broker \in isrs
    /\ broker \in aliveBrokers
    \* On leadership change, left-most isr in replica list will be elected
    /\ broker = Min(isrs)
    /\ nextOffset' = Last(localLogs[broker]).offset + 1
    /\ leaderEpoch' = leaderEpoch + 1
    /\ leader' = broker
    /\ readyToFetchBrokers' = {}
    /\ UNCHANGED <<committedLogs, localLogs, aliveBrokers, isrs, inflightProducers, preferredLeader>>

FailedBrokerBack(broker) ==
    /\ broker = UnstableBroker
    /\ broker \notin aliveBrokers
    /\ broker \notin isrs
    /\ aliveBrokers' = aliveBrokers \cup {broker}
    /\ UNCHANGED <<committedLogs, nextOffset, leaderEpoch, localLogs, isrs, readyToFetchBrokers, inflightProducers, preferredLeader, leader>>

UncleanLeaderElection ==
    /\ NoLeader
    /\ \E broker \in aliveBrokers:
        /\ nextOffset' = Last(localLogs[broker]).offset + 1
        /\ leaderEpoch' = leaderEpoch + 1
        /\ isrs' = {broker}
        /\ leader' = broker
        /\ readyToFetchBrokers' = {}
        /\ UNCHANGED <<committedLogs, aliveBrokers, localLogs, inflightProducers, preferredLeader>>

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
            /\ readyToFetchBrokers' = {}
            /\ UNCHANGED <<committedLogs, aliveBrokers, localLogs, inflightProducers, preferredLeader>>

UncleanLeaderElection3 ==
    /\ NoLeader
    /\ LET largestEpochBrokers ==
            {broker \in aliveBrokers:
                \A other \in aliveBrokers \ {broker}: Last(localLogs[broker]).leaderEpoch >= Last(localLogs[other]).leaderEpoch}
           longestLogBrokers ==
            {broker \in largestEpochBrokers:
                \A other \in largestEpochBrokers \ {broker}: Last(localLogs[broker]).offset >= Last(localLogs[other]).offset}
        IN \E broker \in longestLogBrokers:
            /\ nextOffset' = Last(localLogs[broker]).offset + 1
            /\ leaderEpoch' = leaderEpoch + 1
            /\ isrs' = {broker}
            /\ leader' = broker
            /\ readyToFetchBrokers' = {}
            /\ UNCHANGED <<committedLogs, aliveBrokers, localLogs, inflightProducers, preferredLeader>>

MakeFollower(broker) ==
    /\ ~NoLeader
    /\ broker \notin readyToFetchBrokers
    /\ broker \in aliveBrokers
    /\ broker /= leader
    /\ localLogs' = [localLogs EXCEPT![broker] = TruncatedLog(broker, leader)]
    /\ readyToFetchBrokers' = readyToFetchBrokers \cup {broker}
    /\ UNCHANGED <<committedLogs, nextOffset, leaderEpoch, aliveBrokers, isrs, leader, inflightProducers, preferredLeader>>

Next ==
    \/ AppendToLeader
    \/ \E broker \in Brokers:
        \/ Replicate(broker)
        \/ BecomeOutOfSync(broker)
        \/ BecomeInSync(broker)
\*        \/ ElectNewLeaderBecauseCurrentLeaderGotLost(broker)
        \/ LeaderFailure(broker)
        \/ ElectNewLeader(broker)
        \/ FailedBrokerBack(broker)
        \/ SwapLeadership(broker)
        \/ MakeFollower(broker)
\*    \/ ShutdownUnstableLeader
    \/ PreferredLeaderElection
\*    \/ UncleanLeaderElection
    \/ UncleanLeaderElection3

Spec == Init /\ [][Next]_vars

\* Invariants
CommittedLogNotLost == NoLeader \/ ContainsSeq(localLogs[leader], committedLogs)
====

---- MODULE UncleanLeaderElectionSafety ----
EXTENDS Integers, Sequences, FiniteSets, Util

CONSTANTS
    Brokers,
    UnstableBroker,
    MinIsr,
    MaxLogLen,
    Producers

ASSUME
    /\ Brokers \subseteq Nat
    /\ UnstableBroker \in Brokers
    /\ MinIsr \in Nat /\ MinIsr >= 0 /\ MinIsr <= Cardinality(Brokers)
    /\ MaxLogLen \in Nat /\ MaxLogLen > 0
    /\ Producers \subseteq Nat

VARIABLES
    \* sequence of records ([offset |-> integer, leaderEpoch |-> integer]) that
    \* replicated to all insync replicas (i.e. producer with acks=all received successful response)

    committedLogs,
    leaderEpoch,
    localLogs,
    aliveBrokers,
    readyToFetchBrokers,
    isrs,
    leader,
    inflightProducers,
    preferredLeader,
    shutdownBrokers,
    producerLeaderMetadata,
    localLeaderEpochs,
    produceMessageSeq

vars == <<committedLogs,
          leaderEpoch,
          localLogs,
          aliveBrokers,
          readyToFetchBrokers,
          isrs,
          leader,
          inflightProducers,
          preferredLeader,
          shutdownBrokers,
          producerLeaderMetadata,
          localLeaderEpochs,
          produceMessageSeq>>

\*TypeOK ==
\*    /\ \A i \in DOMAIN committedLogs: committedLogs[i] \in [{"offset", "leaderEpoch", "producer"} -> Int]
\*\*    /\ nextOffset \in Int
\*    /\ leaderEpoch \in Int
\*    /\ aliveBrokers \subseteq Brokers
\*    /\ readyToFetchBrokers \subseteq Brokers
\*    /\ isrs \subseteq Brokers
\*    /\ leader = -1 \/ leader \in Brokers
\*    /\ inflightProducers \subseteq Producers
\*    /\ preferredLeader \in Brokers

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
    /\ committedLogs = <<[offset |-> 1, leaderEpoch |-> 1, producer |-> 1, producerSeq |-> 1]>>
    /\ leaderEpoch = 1
    /\ localLogs = [broker \in Brokers |-> <<[offset |-> 1, leaderEpoch |-> 1, producer |-> 1, producerSeq |-> 1]>>]
    /\ aliveBrokers = Brokers
    /\ isrs = Brokers
    /\ leader = 1
    /\ readyToFetchBrokers = Brokers \ {leader}
    /\ inflightProducers = {}
    /\ preferredLeader = 1
    /\ shutdownBrokers = {}
    /\ producerLeaderMetadata = [producer \in Producers |-> leader]
    /\ localLeaderEpochs = [broker \in Brokers |-> [leader |-> leader, leaderEpoch |-> leaderEpoch]]
    /\ produceMessageSeq = [producer \in Producers |-> 1]

ProduceMessage ==
    /\ LET readyProducers == Producers \ inflightProducers
        \* further produce not sent until corrent one is committed (max.inflight.requests.per.connection = 1)
        IN /\ Cardinality(readyProducers) > 0
           /\ \E p \in readyProducers:
                LET producerLeader == producerLeaderMetadata[p]
                    epoch == localLeaderEpochs[producerLeader].leaderEpoch
                IN
                  /\ producerLeader = localLeaderEpochs[producerLeader].leader
                  /\ localLeaderEpochs[producerLeader].leaderEpoch = leaderEpoch
                  /\ localLogs' = [localLogs EXCEPT![producerLeader] = Append(@, [offset |-> Last(@).offset + 1,
                                                                                  leaderEpoch |-> epoch,
                                                                                  producer |-> p,
                                                                                  producerSeq |-> produceMessageSeq[p] + 1])]
                  /\ inflightProducers' = inflightProducers \cup {p}
                  /\ produceMessageSeq' = [produceMessageSeq EXCEPT![p] = @ + 1]
                  /\ UNCHANGED <<committedLogs, leaderEpoch, aliveBrokers, isrs, leader, readyToFetchBrokers, preferredLeader, shutdownBrokers, producerLeaderMetadata, localLeaderEpochs>>

RetryProduce ==
    \E p \in inflightProducers:
        /\ ~NoLeader
        /\ IF producerLeaderMetadata[p] /= leader THEN
                producerLeaderMetadata' = [producerLeaderMetadata EXCEPT![p] = leader]
           ELSE
                producerLeaderMetadata' = producerLeaderMetadata
        /\ LET
            producerLeader == leader
            epoch == localLeaderEpochs[producerLeader].leaderEpoch
           IN
             /\ producerLeader = localLeaderEpochs[producerLeader].leader
             /\ localLogs' = [localLogs EXCEPT![producerLeader] = Append(@, [offset |-> Last(@).offset + 1,
                                                                             leaderEpoch |-> epoch,
                                                                             producer |-> p,
                                                                             producerSeq |-> produceMessageSeq[p]])]
             /\ UNCHANGED <<committedLogs, leaderEpoch, aliveBrokers, isrs, leader, readyToFetchBrokers, preferredLeader, shutdownBrokers, localLeaderEpochs, produceMessageSeq, inflightProducers>>

UpdateMetadata ==
    /\ ~NoLeader
    /\ \E p \in Producers:
        /\ producerLeaderMetadata[p] /= leader
        /\ producerLeaderMetadata' = [producerLeaderMetadata EXCEPT![p] = leader]
        /\ UNCHANGED <<committedLogs, leaderEpoch, aliveBrokers, isrs, leader, readyToFetchBrokers, preferredLeader, shutdownBrokers, localLogs, inflightProducers, localLeaderEpochs, produceMessageSeq>>

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
    /\ UNCHANGED <<leaderEpoch, aliveBrokers, isrs, leader, readyToFetchBrokers, preferredLeader, shutdownBrokers, producerLeaderMetadata, localLeaderEpochs, produceMessageSeq>>

BecomeOutOfSync(broker) ==
    /\ ~NoLeader
    /\ \/ leader = UnstableBroker
       \/ broker = UnstableBroker
    /\ broker /= leader
    /\ broker \in isrs
    /\ broker \in readyToFetchBrokers
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
    /\ UNCHANGED <<leaderEpoch, localLogs, aliveBrokers, leader, readyToFetchBrokers, preferredLeader, shutdownBrokers, producerLeaderMetadata, localLeaderEpochs, produceMessageSeq>>

BecomeInSync(broker) ==
    /\ ~NoLeader
    /\ broker /= leader
    /\ broker \notin isrs
    /\ broker \in aliveBrokers
    /\ broker \in readyToFetchBrokers
    /\ /\ Leo(broker) >= HighWatermark
       /\ Leo(broker) >= LeaderEpochStartOffset
    /\ isrs' = isrs \cup {broker}
    /\ UNCHANGED <<
                    committedLogs,
                    leaderEpoch,
                    localLogs,
                    aliveBrokers,
                    leader,
                    readyToFetchBrokers,
                    inflightProducers,
                    preferredLeader,
                    shutdownBrokers,
                    producerLeaderMetadata,
                    localLeaderEpochs,
                    produceMessageSeq
                 >>

MakeLeader(broker) ==
    /\ broker = leader
    /\ \/ localLeaderEpochs[broker].leader /= leader
       \/ localLeaderEpochs[broker].leaderEpoch /= leaderEpoch
    /\ localLeaderEpochs' = [localLeaderEpochs EXCEPT![broker] = [leader |-> leader, leaderEpoch |-> leaderEpoch]]
    /\ UNCHANGED <<
                    committedLogs,
                    localLogs,
                    aliveBrokers,
                    isrs,
                    inflightProducers,
                    shutdownBrokers,
                    producerLeaderMetadata,
                    produceMessageSeq,
                    leaderEpoch,
                    leader,
                    readyToFetchBrokers,
                    preferredLeader
                 >>

PreferredLeaderElection ==
    /\ ~NoLeader
    /\ preferredLeader /= leader
    /\ preferredLeader \in isrs
    /\ preferredLeader \in aliveBrokers
    /\ leaderEpoch' = leaderEpoch + 1
    /\ leader' = preferredLeader
    /\ readyToFetchBrokers' = {}
    /\ UNCHANGED <<committedLogs, localLogs, aliveBrokers, isrs, inflightProducers, preferredLeader, shutdownBrokers, producerLeaderMetadata, produceMessageSeq, localLeaderEpochs>>

SwapLeadership(broker) ==
\*    /\ leader = UnstableBroker
    /\ broker /= leader
    /\ broker \in isrs
    /\ broker \in aliveBrokers
    /\ preferredLeader' = broker
    /\ UNCHANGED <<
                committedLogs,
                localLogs,
                aliveBrokers,
                isrs,
                inflightProducers,
                shutdownBrokers,
                producerLeaderMetadata,
                produceMessageSeq,
                leaderEpoch,
                leader,
                readyToFetchBrokers,
                localLeaderEpochs>>

ShutdownUnstableBroker ==
\*    /\ leader = UnstableBroker
\*    /\ UnstableBroker \in aliveBrokers
\*    /\ isrs = {UnstableBroker}
    /\ aliveBrokers' = aliveBrokers \ {UnstableBroker}
    /\ shutdownBrokers' = shutdownBrokers \cup {UnstableBroker}
    /\ leader' = -1
    /\ UNCHANGED <<committedLogs, leaderEpoch, localLogs, isrs, readyToFetchBrokers, inflightProducers, preferredLeader, producerLeaderMetadata, localLeaderEpochs, produceMessageSeq>>

LeaderFailure(broker) ==
    /\ broker = UnstableBroker
    /\ ~NoLeader
    /\ leader = broker
    /\ broker \in aliveBrokers
    /\ broker \in isrs
    /\ aliveBrokers' = aliveBrokers \ {broker}
    \* https://github.com/apache/kafka/blob/2.4.1/core/src/main/scala/kafka/controller/ReplicaStateMachine.scala#L327
    /\ IF isrs = {broker} THEN isrs' = isrs ELSE isrs' = isrs \ {broker}
    /\ leader' = -1
    /\ UNCHANGED <<committedLogs, leaderEpoch, localLogs, readyToFetchBrokers, inflightProducers, preferredLeader, shutdownBrokers, producerLeaderMetadata, localLeaderEpochs, produceMessageSeq>>

ElectNewLeader(broker) ==
    /\ NoLeader
    /\ broker \in isrs
    /\ broker \in aliveBrokers
    \* On leadership change, left-most isr in replica list will be elected
    /\ broker = Min(isrs)
\*    /\ nextOffset' = Last(localLogs[broker]).offset + 1
    /\ leaderEpoch' = leaderEpoch + 1
    /\ leader' = broker
    /\ readyToFetchBrokers' = {}
    /\ UNCHANGED <<committedLogs, localLogs, aliveBrokers, isrs, inflightProducers, preferredLeader, shutdownBrokers, producerLeaderMetadata, produceMessageSeq, localLeaderEpochs>>

FailedBrokerBack(broker) ==
\*    /\ broker = UnstableBroker
    /\ broker \notin aliveBrokers
\*    /\ broker \notin isrs
    /\ aliveBrokers' = aliveBrokers \cup {broker}
    /\ UNCHANGED <<committedLogs, leaderEpoch, localLogs, isrs, readyToFetchBrokers, inflightProducers, preferredLeader, leader, shutdownBrokers, producerLeaderMetadata, localLeaderEpochs, produceMessageSeq>>

UncleanLeaderElection ==
    /\ NoLeader
    /\ shutdownBrokers /= {}
    /\ \E broker \in aliveBrokers:
\*        /\ nextOffset' = Last(localLogs[broker]).offset + 1
        /\ leaderEpoch' = leaderEpoch + 1
        /\ isrs' = {broker}
        /\ leader' = broker
        /\ readyToFetchBrokers' = {}
        /\ UNCHANGED <<committedLogs, aliveBrokers, localLogs, inflightProducers, preferredLeader, shutdownBrokers, producerLeaderMetadata, produceMessageSeq, localLeaderEpochs>>

\* Modified version that elect new leader that has longest local log
UncleanLeaderElection2 ==
    /\ NoLeader
    /\ (aliveBrokers \cap isrs) = {}
    /\ shutdownBrokers /= {}
    /\ LET longestLogBrokers ==
            {broker \in aliveBrokers:
                \A other \in aliveBrokers \ {broker}: Len(localLogs[broker]) >= Len(localLogs[other])}
        IN \E broker \in longestLogBrokers:
\*            /\ nextOffset' = Last(localLogs[broker]).offset + 1
            /\ leaderEpoch' = leaderEpoch + 1
            /\ isrs' = {broker}
            /\ leader' = broker
            /\ readyToFetchBrokers' = {}
            /\ UNCHANGED <<committedLogs, aliveBrokers, localLogs, inflightProducers, preferredLeader, shutdownBrokers, producerLeaderMetadata, produceMessageSeq, localLeaderEpochs>>

UncleanLeaderElection3 ==
    /\ NoLeader
    /\ (aliveBrokers \cap isrs) = {}
    /\ shutdownBrokers /= {}
    /\ LET largestEpochBrokers ==
            {broker \in aliveBrokers:
                \A other \in aliveBrokers \ {broker}: Last(localLogs[broker]).leaderEpoch >= Last(localLogs[other]).leaderEpoch}
           longestLogBrokers ==
            {broker \in largestEpochBrokers:
                \A other \in largestEpochBrokers \ {broker}: Last(localLogs[broker]).offset >= Last(localLogs[other]).offset}
        IN \E broker \in longestLogBrokers:
\*            /\ nextOffset' = Last(localLogs[broker]).offset + 1
            /\ leaderEpoch' = leaderEpoch + 1
            /\ isrs' = {broker}
            /\ leader' = broker
            /\ readyToFetchBrokers' = {}
            /\ UNCHANGED <<committedLogs, aliveBrokers, localLogs, inflightProducers, preferredLeader, shutdownBrokers, producerLeaderMetadata, produceMessageSeq, localLeaderEpochs>>

MakeFollower(broker) ==
    /\ ~NoLeader
    /\ broker \notin readyToFetchBrokers
    /\ broker \in aliveBrokers
    /\ broker /= leader
    /\ localLogs' = [localLogs EXCEPT![broker] = TruncatedLog(broker, leader)]
    /\ readyToFetchBrokers' = readyToFetchBrokers \cup {broker}
    /\ localLeaderEpochs' = [localLeaderEpochs EXCEPT![broker] = [leader |-> leader, leaderEpoch |-> leaderEpoch]]
    /\ UNCHANGED <<committedLogs, leaderEpoch, aliveBrokers, isrs, leader, inflightProducers, preferredLeader, shutdownBrokers, producerLeaderMetadata, produceMessageSeq>>

Next ==
    \/ ProduceMessage
\*    \/ RetryProduce
    \/ UpdateMetadata
    \/ \E broker \in Brokers:
        \/ Replicate(broker)
        \/ BecomeOutOfSync(broker)
        \/ BecomeInSync(broker)
        \/ LeaderFailure(broker)
        \/ ElectNewLeader(broker)
        \/ FailedBrokerBack(broker)
        \/ SwapLeadership(broker)
        \/ MakeFollower(broker)
        \/ MakeLeader(broker)
    \/ ShutdownUnstableBroker
    \/ PreferredLeaderElection
\*    \/ UncleanLeaderElection
\*    \/ UncleanLeaderElection2
    \/ UncleanLeaderElection3

Spec == Init /\ [][Next]_vars

\* Invariants
CommittedLogNotLost == NoLeader \/ ContainsSeq(localLogs[leader], committedLogs)
NoDuplicatedMessage == \A i,j \in DOMAIN committedLogs:
                             (i /= j) => ~(
                                /\ committedLogs[i].producerSeq = committedLogs[j].producerSeq
                                /\ committedLogs[i].producer = committedLogs[j].producer
                             )
====

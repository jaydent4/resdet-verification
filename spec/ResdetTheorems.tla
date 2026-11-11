--------------------------- MODULE ResdetTheorems ---------------------------
(***************************************************************************
TLAPS proofs, part 5 of 5: the paper's Theorem 1 and its companions.

Everything here is proved for the specification Spec of Resdet.tla with
the strict delivery path (StrictDelivery, defined in ResdetFold.tla) and
no other restriction on the constants. Unlike the TLC runs, nothing is
bounded: the replica set, the request, payload and response sets, the
quorum, MaxSlots, and the batching, crash, and timeout-fallback switches
are arbitrary.

Consensus is the paper's black box. CG1 (index agreement) and CG2 (prefix
agreement) are built into Spec as the single append-only consensusLog that
every replica learns from; they are assumptions of these theorems, not
conclusions.
***************************************************************************)
EXTENDS ResdetDelivery, ResdetPrefix, ResdetValidity, FiniteSetTheorems

(***************************************************************************
Theorem 1 as the paper states it: for every request id x, if replicas r
and t deliver responses y_r and y_t for x, then y_r = y_t.

delivered[r] is the history of everything replica r has delivered, so the
statement covers deliveries made at different times. It quantifies over
all replicas, crashed or not, which is stronger than the paper's
"non-faulty replicas", and taking r = t it also says that one replica
never delivers two different responses for the same request id.
***************************************************************************)
Agreement ==
    \A r, t \in Replicas :
        \A i \in 1..Len(delivered[r]) :
            \A j \in 1..Len(delivered[t]) :
                delivered[r][i].rid = delivered[t][j].rid =>
                    delivered[r][i].value = delivered[t][j].value

(***************************************************************************
A request id has at most one first agreed position.
***************************************************************************)
LEMMA FirstCommitUnique ==
    ASSUME NEW s1 \in Nat, NEW k1 \in 1..Len(consensusLog[s1]),
           NEW s2 \in Nat, NEW k2 \in 1..Len(consensusLog[s2]),
           s1 >= 1, s2 >= 1,
           FirstCommit(s1, k1), FirstCommit(s2, k2),
           consensusLog[s1][k1].rid = consensusLog[s2][k2].rid
    PROVE  s1 = s2 /\ k1 = k2
<1>1. ~Earlier(s1, k1, s2, k2)
  <2> SUFFICES ASSUME Earlier(s1, k1, s2, k2) PROVE FALSE
    OBVIOUS
  <2>1. s1 \in 1..s2
    BY DEF Earlier
  <2> QED
    BY <2>1 DEF FirstCommit
<1>2. ~Earlier(s2, k2, s1, k1)
  <2> SUFFICES ASSUME Earlier(s2, k2, s1, k1) PROVE FALSE
    OBVIOUS
  <2>1. s2 \in 1..s1
    BY DEF Earlier
  <2> QED
    BY <2>1 DEF FirstCommit
<1> QED
  BY <1>1, <1>2 DEF Earlier

LEMMA AgreementFromInv == DeliveryInv => Agreement
<1> SUFFICES ASSUME DeliveryInv,
                    NEW r \in Replicas, NEW t \in Replicas,
                    NEW i \in 1..Len(delivered[r]),
                    NEW j \in 1..Len(delivered[t]),
                    delivered[r][i].rid = delivered[t][j].rid
             PROVE  delivered[r][i].value = delivered[t][j].value
  BY DEF Agreement
<1>1. PICK s1 \in 1..processed[r] :
        \E k \in 1..Len(consensusLog[s1]) :
            /\ delivered[r][i] = consensusLog[s1][k]
            /\ FirstCommit(s1, k)
  BY DEF DeliveryInv, DeliveredFirstCommit
<1>2. PICK k1 \in 1..Len(consensusLog[s1]) :
        /\ delivered[r][i] = consensusLog[s1][k1]
        /\ FirstCommit(s1, k1)
  BY <1>1
<1>3. PICK s2 \in 1..processed[t] :
        \E k \in 1..Len(consensusLog[s2]) :
            /\ delivered[t][j] = consensusLog[s2][k]
            /\ FirstCommit(s2, k)
  BY DEF DeliveryInv, DeliveredFirstCommit
<1>4. PICK k2 \in 1..Len(consensusLog[s2]) :
        /\ delivered[t][j] = consensusLog[s2][k2]
        /\ FirstCommit(s2, k2)
  BY <1>3
<1>5. /\ s1 \in Nat /\ s1 >= 1
      /\ s2 \in Nat /\ s2 >= 1
  BY DEF DeliveryInv, DeliveryTypeOK
<1>6. s1 = s2 /\ k1 = k2
  BY <1>2, <1>4, <1>5, FirstCommitUnique
<1> QED
  BY <1>2, <1>4, <1>6

(***************************************************************************
The same statement in the form the TLC configurations check.
***************************************************************************)
LEMMA ResponseAgreementFromAgreement == Agreement => ResponseAgreement
<1> SUFFICES ASSUME Agreement,
                    NEW left \in Replicas, NEW right \in Replicas,
                    NEW request \in RequestIds,
                    DeliveredValues(left, request) # {},
                    DeliveredValues(right, request) # {}
             PROVE  DeliveredValues(left, request) =
                    DeliveredValues(right, request)
  BY DEF ResponseAgreement
<1>1. \A v \in DeliveredValues(left, request) :
        \A w \in DeliveredValues(right, request) : v = w
  BY DEF Agreement, DeliveredValues, DeliveredPositions
<1> QED
  BY <1>1

(***************************************************************************
At-most-once delivery (paper Sections 4.2-4.3).
***************************************************************************)
LEMMA AtMostOneElement ==
    ASSUME NEW T, \A a, b \in T : a = b
    PROVE  IsFiniteSet(T) /\ Cardinality(T) <= 1
<1>1. CASE T = {}
  BY <1>1, FS_EmptySet
<1>2. CASE T # {}
  <2>1. PICK a \in T : TRUE
    BY <1>2
  <2>2. T = {a}
    BY <2>1
  <2> QED
    BY <2>2, FS_Singleton
<1> QED
  BY <1>1, <1>2

LEMMA AtMostOnceFromInv == DeliveryInv => AtMostOnceDelivery
<1> SUFFICES ASSUME DeliveryInv,
                    NEW replica \in Replicas, NEW request \in RequestIds
             PROVE  Cardinality(DeliveredPositions(replica, request)) <= 1
  BY DEF AtMostOnceDelivery
<1>1. \A a, b \in DeliveredPositions(replica, request) : a = b
  BY DEF DeliveryInv, DeliveredOnce, DeliveredPositions
<1> QED
  BY <1>1, AtMostOneElement

LEMMA SeenMatchesFromInv == DeliveryInv => SeenMatchesDelivered
<1> SUFFICES ASSUME DeliveryInv, NEW replica \in Replicas
             PROVE  seen[replica] =
                        {delivered[replica][index].rid :
                            index \in 1..Len(delivered[replica])}
  BY DEF SeenMatchesDelivered
<1>1. \A x \in seen[replica] :
        \E index \in 1..Len(delivered[replica]) :
            delivered[replica][index].rid = x
  BY DEF DeliveryInv, SeenDelivered
<1>2. \A index \in 1..Len(delivered[replica]) :
        delivered[replica][index].rid \in seen[replica]
  BY DEF DeliveryInv, DeliveredSeen
<1> QED
  BY <1>1, <1>2

(***************************************************************************
Theorem 1 (Safety), paper Section 5.
***************************************************************************)
THEOREM Theorem1 ==
    ASSUME StrictDelivery
    PROVE  Spec => []Agreement
BY DeliveryInvariant, AgreementFromInv, PTL

(***************************************************************************
Delivery histories only grow: a step never removes or rewrites a delivered
response. Together with Theorem1 this is why agreement between histories
in one state is agreement between deliveries made at any two times.
***************************************************************************)
DeliveredGrows ==
    \A r \in Replicas : IsPrefix(delivered[r], delivered'[r])

LEMMA DeliveredGrowsStep ==
    ASSUME StrictDelivery
    PROVE  DeliveryInv /\ [Next]_vars => DeliveredGrows
<1> SUFFICES ASSUME DeliveryInv, [Next]_vars
             PROVE  DeliveredGrows
  OBVIOUS
<1> USE DEF StrictDelivery
<1>0. /\ delivered \in [Replicas -> Seq(ResponseItems)]
      /\ consensusLog \in Seq(Seq(ResponseItems))
      /\ processed \in [Replicas -> Nat]
  BY DEF DeliveryInv, DeliveryTypeOK
<1>a. ASSUME NEW r \in Replicas, delivered'[r] = delivered[r]
      PROVE  IsPrefix(delivered[r], delivered'[r])
  <2>1. delivered[r] \in Seq(ResponseItems)
    BY <1>0
  <2>2. PointwisePrefix(delivered[r], delivered[r])
    BY <2>1 DEF PointwisePrefix
  <2> QED
    BY <1>a, <2>1, <2>2, PointwisePrefixIsPrefix
<1>b. ASSUME UNCHANGED delivered
      PROVE  DeliveredGrows
  BY <1>a, <1>b DEF DeliveredGrows
<1>c. ASSUME NEW r0 \in Replicas, ProcessContiguous(r0)
      PROVE  DeliveredGrows
  <2> DEFINE items == consensusLog[processed[r0] + 1]
             result == ApplyItems(items, seen[r0], delivered[r0])
  <2>1. items \in Seq(ResponseItems)
    BY <1>0, <1>c DEF ProcessContiguous
  <2>2. delivered[r0] \in Seq(ResponseItems)
    BY <1>0
  <2>3. AppliedCorrectly(ResponseItems, items, seen[r0], delivered[r0],
                         result)
    BY <2>1, <2>2, ApplyItemsCorrect
  <2>4. delivered' = [delivered EXCEPT ![r0] = result.output]
    BY <1>c DEF ProcessContiguous
  <2>5. /\ result.output \in Seq(ResponseItems)
        /\ PointwisePrefix(delivered[r0], result.output)
    BY <2>3 DEF AppliedCorrectly, PointwisePrefix
  <2> HIDE DEF items, result
  <2> SUFFICES ASSUME NEW r \in Replicas
               PROVE  IsPrefix(delivered[r], delivered'[r])
    BY DEF DeliveredGrows
  <2>6. CASE r = r0
    <3>1. delivered'[r] = result.output
      BY <1>0, <2>4, <2>6
    <3> QED
      BY <2>2, <2>5, <2>6, <3>1, PointwisePrefixIsPrefix
  <2>7. CASE r # r0
    <3>1. delivered'[r] = delivered[r]
      BY <1>0, <2>4, <2>7
    <3> QED
      BY <1>a, <3>1
  <2> QED
    BY <2>6, <2>7
<1>1. CASE SubmitVoteAction
  BY <1>1, <1>b DEF SubmitVoteAction, SubmitVote
<1>2. CASE SelectAction
  BY <1>2, <1>b DEF SelectAction, SelectByQuorum, TimeoutSelect
<1>3. CASE DispatchAction
  BY <1>3, <1>b DEF DispatchAction, Dispatch
<1>4. CASE ExternalRespondAction
  BY <1>4, <1>b DEF ExternalRespondAction, ExternalRespond
<1>5. CASE ProposeResponseAction
  BY <1>5, <1>b DEF ProposeResponseAction, ProposeResponse
<1>6. CASE DecideAction
  BY <1>6, <1>b DEF DecideAction, DecideOne, DecidePair
<1>7. CASE LearnAction
  BY <1>7, <1>b DEF LearnAction, LearnSlot
<1>8. CASE ProcessAction
  BY <1>8, <1>c DEF ProcessAction
<1>9. CASE \E replica \in Replicas, slot \in 1..MaxSlots :
              ProcessNonContiguous(replica, slot)
  BY <1>9 DEF ProcessNonContiguous
<1>10. CASE \E replica \in Replicas, item \in ResponseItems :
               DeliverBeforeConsensus(replica, item)
  BY <1>10 DEF DeliverBeforeConsensus
<1>11. CASE \E replica \in Replicas : Crash(replica)
  BY <1>11, <1>b DEF Crash
<1>12. CASE \E replica \in Replicas : Recover(replica)
  BY <1>12, <1>b DEF Recover
<1>13. CASE \E replica \in Replicas : Elect(replica)
  BY <1>13, <1>b DEF Elect
<1>14. CASE \E replica \in Replicas,
               request \in RequestIds,
               payload \in Payloads :
               NoLeaderDispatch(replica, request, payload)
  BY <1>14 DEF NoLeaderDispatch
<1>15. CASE \E replica \in Replicas,
               request \in RequestIds,
               responseValue \in Responses :
               DirectNoLeaderRespond(replica, request, responseValue)
  BY <1>15 DEF DirectNoLeaderRespond
<1>16. CASE UNCHANGED vars
  BY <1>16, <1>b DEF vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
     <1>11, <1>12, <1>13, <1>14, <1>15, <1>16 DEF Next

THEOREM DeliveredAppendOnly ==
    ASSUME StrictDelivery
    PROVE  Spec => [][DeliveredGrows]_vars
<1>1. DeliveryInv /\ [Next]_vars => [DeliveredGrows]_vars
  BY DeliveredGrowsStep
<1> QED
  BY <1>1, DeliveryInvariant, PTL DEF Spec

(***************************************************************************
Everything TLAPS proves about the strict protocol, in one statement. The
conjuncts other than Agreement and DeliveredFirstCommit are the invariants
of the same name that the TLC configurations check on bounded models.

  Agreement              Theorem 1.
  ResponseAgreement      Theorem 1 in the TLC configurations' form.
  DeliveredFirstCommit   Every delivered response is the first agreed
                         entry for its request id.
  AtMostOnceDelivery     No replica delivers a request id twice.
  SeenMatchesDelivered   The deduplication state is exactly the set of
                         delivered request ids.
  PrefixAgreement        Any two delivery histories are prefix-comparable.
  RaceWinnerAgreement    Replicas agree on the winner of a response race.
  ResponseValidity       Delivered responses were physically returned for
                         a selected request.
  ConsensusValidity      Every agreed entry was proposed.
  ProposalValidity       Every proposed entry was observed.
  ObservedHasPhysicalExecution
                         Every observed response was returned to a replica
                         that dispatched the request.
  NoDispatchBeforeSelection
                         Requests are dispatched only after selection.
  ProcessedPrefixLearned Lemma 2: no-hole processing.
  LearnedOnlyDecided     Replicas learn only agreed indexes.
  ProcessedWithinLog     Replicas process only agreed indexes.
***************************************************************************)
THEOREM Safety ==
    ASSUME StrictDelivery
    PROVE  Spec => [](/\ Agreement
                      /\ ResponseAgreement
                      /\ DeliveredFirstCommit
                      /\ AtMostOnceDelivery
                      /\ SeenMatchesDelivered
                      /\ PrefixAgreement
                      /\ RaceWinnerAgreement
                      /\ ResponseValidity
                      /\ ConsensusValidity
                      /\ ProposalValidity
                      /\ ObservedHasPhysicalExecution
                      /\ NoDispatchBeforeSelection
                      /\ ProcessedPrefixLearned
                      /\ LearnedOnlyDecided
                      /\ ProcessedWithinLog)
<1>1. DeliveryInv =>
        /\ Agreement
        /\ ResponseAgreement
        /\ DeliveredFirstCommit
        /\ AtMostOnceDelivery
        /\ SeenMatchesDelivered
  BY AgreementFromInv, ResponseAgreementFromAgreement, AtMostOnceFromInv,
     SeenMatchesFromInv
     DEF DeliveryInv
<1> QED
  BY <1>1, DeliveryInvariant, PrefixAgreementInvariant,
     RaceWinnerAgreementInvariant, ResponseValidityInvariant,
     ConsensusValidityInvariant, ProposalChainInvariant,
     ProcessingOrderInvariant, PTL
=============================================================================

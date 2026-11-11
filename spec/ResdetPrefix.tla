---------------------------- MODULE ResdetPrefix ----------------------------
(***************************************************************************
TLAPS proofs, part 3 of 5: replicas that process the same log prefix hold
the same delivery state.

This is the paper's Lemma 1 (same processed index, same entry) and Lemma 2
(no-hole processing) in one statement: a replica's deduplication state and
delivery history are a function of the agreed log and of how many indexes
it has processed, namely the replay of that prefix from the empty state.
Prefix agreement of delivery histories and agreement on the winner of a
response race (paper Section 3.3) follow.

Do not add SequenceTheorems to the EXTENDS list (see ResdetFold.tla); the
one SubSeq fact needed here is proved directly.
***************************************************************************)
EXTENDS ResdetFold

(* ReplayOf(log)[n]: the delivery state after processing indexes 1..n. *)
ReplayOf(log) ==
    LET replay[n \in Nat] ==
            IF n = 0
            THEN [seen |-> {}, output |-> <<>>]
            ELSE ApplyItems(log[n], replay[n - 1].seen, replay[n - 1].output)
    IN replay

(***************************************************************************
The two DOMAIN conjuncts make the invariant inductive: without them an
EXCEPT update of seen or delivered says nothing about the updated entry.
***************************************************************************)
ReplayInv ==
    /\ consensusLog \in Seq(Seq(ResponseItems))
    /\ processed \in [Replicas -> Nat]
    /\ \A r \in Replicas : processed[r] <= Len(consensusLog)
    /\ DOMAIN seen = Replicas
    /\ DOMAIN delivered = Replicas
    /\ \A r \in Replicas :
         /\ seen[r] = ReplayOf(consensusLog)[processed[r]].seen
         /\ delivered[r] = ReplayOf(consensusLog)[processed[r]].output

(* left is a prefix of right, stated index by index. *)
PointwisePrefix(left, right) ==
    /\ Len(left) <= Len(right)
    /\ \A i \in 1..Len(left) : right[i] = left[i]

LEMMA PointwisePrefixIsPrefix ==
    ASSUME NEW S, NEW left \in Seq(S), NEW right \in Seq(S),
           PointwisePrefix(left, right)
    PROVE  IsPrefix(left, right)
<1>1. Len(left) \in Nat /\ Len(right) \in Nat /\ Len(left) <= Len(right)
  BY DEF PointwisePrefix
<1>2. SubSeq(right, 1, Len(left)) \in Seq(S)
  BY <1>1
<1>3. Len(SubSeq(right, 1, Len(left))) = Len(left)
  BY <1>1
<1>4. \A i \in 1..Len(left) : SubSeq(right, 1, Len(left))[i] = left[i]
  BY <1>1 DEF PointwisePrefix
<1>5. SubSeq(right, 1, Len(left)) = left
  BY <1>2, <1>3, <1>4
<1> QED
  BY <1>1, <1>5 DEF IsPrefix

(***************************************************************************
Step 1: the recursive definition of ReplayOf unfolds.
***************************************************************************)
LEMMA ReplayUnfold ==
    ASSUME NEW log
    PROVE  LET f == ReplayOf(log)
           IN  f = [n \in Nat |->
                        IF n = 0
                        THEN [seen |-> {}, output |-> <<>>]
                        ELSE ApplyItems(log[n], f[n - 1].seen,
                                        f[n - 1].output)]
<1> DEFINE f == ReplayOf(log)
           c == [seen |-> {}, output |-> <<>>]
<1>1. NatInductiveDefHypothesis(
          f, c, LAMBDA v, i : ApplyItems(log[i], v.seen, v.output))
  BY DEF NatInductiveDefHypothesis, ReplayOf
<1>2. NatInductiveDefConclusion(
          f, c, LAMBDA v, i : ApplyItems(log[i], v.seen, v.output))
  <2> HIDE DEF f, c
  <2> QED
    BY <1>1, NatInductiveDef
<1> QED
  BY <1>2 DEF NatInductiveDefConclusion

LEMMA ReplayZero ==
    ASSUME NEW log
    PROVE  ReplayOf(log)[0] = [seen |-> {}, output |-> <<>>]
BY ReplayUnfold

LEMMA ReplaySucc ==
    ASSUME NEW log, NEW n \in Nat
    PROVE  ReplayOf(log)[n + 1] =
               ApplyItems(log[n + 1], ReplayOf(log)[n].seen,
                          ReplayOf(log)[n].output)
<1> DEFINE f == ReplayOf(log)
<1>1. f = [m \in Nat |->
               IF m = 0
               THEN [seen |-> {}, output |-> <<>>]
               ELSE ApplyItems(log[m], f[m - 1].seen, f[m - 1].output)]
  BY ReplayUnfold
<1> HIDE DEF f
<1>2. n + 1 \in Nat /\ n + 1 # 0 /\ (n + 1) - 1 = n
  OBVIOUS
<1>3. f[n + 1] = ApplyItems(log[n + 1], f[(n + 1) - 1].seen,
                            f[(n + 1) - 1].output)
  BY <1>1, <1>2
<1> QED
  BY <1>2, <1>3 DEF f

(***************************************************************************
Step 2: replaying one more agreed batch keeps the history a sequence of
response items and keeps the old history as a prefix.
***************************************************************************)
LEMMA ReplayStepApplied ==
    ASSUME ~MutantNoDedup,
           NEW log \in Seq(Seq(ResponseItems)),
           NEW n \in Nat, n + 1 <= Len(log),
           ReplayOf(log)[n].output \in Seq(ResponseItems)
    PROVE  AppliedCorrectly(ResponseItems, log[n + 1],
                            ReplayOf(log)[n].seen, ReplayOf(log)[n].output,
                            ReplayOf(log)[n + 1])
<1>1. log[n + 1] \in Seq(ResponseItems)
  OBVIOUS
<1>2. ReplayOf(log)[n + 1] =
          ApplyItems(log[n + 1], ReplayOf(log)[n].seen,
                     ReplayOf(log)[n].output)
  BY ReplaySucc
<1> QED
  BY <1>1, <1>2, ApplyItemsCorrect

LEMMA ReplayOutputType ==
    ASSUME ~MutantNoDedup, NEW log \in Seq(Seq(ResponseItems))
    PROVE  \A n \in Nat :
               n <= Len(log) => ReplayOf(log)[n].output \in Seq(ResponseItems)
<1> DEFINE P(n) == n <= Len(log) =>
                       ReplayOf(log)[n].output \in Seq(ResponseItems)
<1>1. P(0)
  BY ReplayZero
<1>2. \A n \in Nat : P(n) => P(n + 1)
  <2> TAKE n \in Nat
  <2> SUFFICES ASSUME P(n), n + 1 <= Len(log)
               PROVE  ReplayOf(log)[n + 1].output \in Seq(ResponseItems)
    OBVIOUS
  <2>1. ReplayOf(log)[n].output \in Seq(ResponseItems)
    OBVIOUS
  <2>2. AppliedCorrectly(ResponseItems, log[n + 1],
                         ReplayOf(log)[n].seen, ReplayOf(log)[n].output,
                         ReplayOf(log)[n + 1])
    BY <2>1, ReplayStepApplied
  <2> QED
    BY <2>2 DEF AppliedCorrectly
<1> HIDE DEF P
<1>3. \A n \in Nat : P(n)
  BY <1>1, <1>2, NatInduction
<1> QED
  BY <1>3 DEF P

LEMMA ReplayMonotone ==
    ASSUME ~MutantNoDedup, NEW log \in Seq(Seq(ResponseItems)),
           NEW m \in Nat
    PROVE  \A n \in Nat :
               (m <= n /\ n <= Len(log)) =>
                   PointwisePrefix(ReplayOf(log)[m].output,
                                   ReplayOf(log)[n].output)
<1> DEFINE Out(n) == ReplayOf(log)[n].output
           P(n) == (m <= n /\ n <= Len(log)) => PointwisePrefix(Out(m), Out(n))
<1>0. \A n \in Nat : n <= Len(log) => Out(n) \in Seq(ResponseItems)
  BY ReplayOutputType
<1>1. P(0)
  <2> SUFFICES ASSUME m <= 0, 0 <= Len(log)
               PROVE  PointwisePrefix(Out(m), Out(0))
    OBVIOUS
  <2>1. m = 0
    OBVIOUS
  <2>2. Out(0) \in Seq(ResponseItems)
    BY <1>0
  <2> QED
    BY <2>1, <2>2 DEF PointwisePrefix
<1>2. \A n \in Nat : P(n) => P(n + 1)
  <2> TAKE n \in Nat
  <2> SUFFICES ASSUME P(n), m <= n + 1, n + 1 <= Len(log)
               PROVE  PointwisePrefix(Out(m), Out(n + 1))
    OBVIOUS
  <2>1. Out(n) \in Seq(ResponseItems) /\ Out(n + 1) \in Seq(ResponseItems)
    BY <1>0
  <2>2. CASE m = n + 1
    BY <2>1, <2>2 DEF PointwisePrefix
  <2>3. CASE m <= n
    <3>1. PointwisePrefix(Out(m), Out(n))
      BY <2>3
    <3>2. Out(m) \in Seq(ResponseItems)
      BY <1>0, <2>3
    <3>3. AppliedCorrectly(ResponseItems, log[n + 1],
                           ReplayOf(log)[n].seen, Out(n),
                           ReplayOf(log)[n + 1])
      BY <2>1, ReplayStepApplied
    <3>4. PointwisePrefix(Out(n), Out(n + 1))
      BY <3>3 DEF AppliedCorrectly, PointwisePrefix
    <3> HIDE DEF Out
    <3> QED
      BY <2>1, <3>1, <3>2, <3>4 DEF PointwisePrefix
  <2> QED
    BY <2>2, <2>3
<1> HIDE DEF P
<1>3. \A n \in Nat : P(n)
  BY <1>1, <1>2, NatInduction
<1> QED
  BY <1>3 DEF P

(***************************************************************************
Step 3: agreeing on one more index does not change the replay of the
indexes already agreed.
***************************************************************************)
LEMMA ReplayAppendStable ==
    ASSUME NEW T, NEW log \in Seq(T), NEW b
    PROVE  \A n \in Nat :
               n <= Len(log) =>
                   ReplayOf(Append(log, b))[n] = ReplayOf(log)[n]
<1> DEFINE P(n) == n <= Len(log) =>
                       ReplayOf(Append(log, b))[n] = ReplayOf(log)[n]
<1>1. P(0)
  BY ReplayZero
<1>2. \A n \in Nat : P(n) => P(n + 1)
  <2> TAKE n \in Nat
  <2> SUFFICES ASSUME P(n), n + 1 <= Len(log)
               PROVE  ReplayOf(Append(log, b))[n + 1] = ReplayOf(log)[n + 1]
    OBVIOUS
  <2>1. ReplayOf(Append(log, b))[n] = ReplayOf(log)[n]
    OBVIOUS
  <2>2. Append(log, b)[n + 1] = log[n + 1]
    OBVIOUS
  <2>3. ReplayOf(Append(log, b))[n + 1] =
            ApplyItems(Append(log, b)[n + 1],
                       ReplayOf(Append(log, b))[n].seen,
                       ReplayOf(Append(log, b))[n].output)
    BY ReplaySucc
  <2>4. ReplayOf(log)[n + 1] =
            ApplyItems(log[n + 1], ReplayOf(log)[n].seen,
                       ReplayOf(log)[n].output)
    BY ReplaySucc
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4
<1> HIDE DEF P
<1>3. \A n \in Nat : P(n)
  BY <1>1, <1>2, NatInduction
<1> QED
  BY <1>3 DEF P

(***************************************************************************
Step 4: ReplayInv is an inductive invariant of the strict protocol.
***************************************************************************)
THEOREM ReplayInit == Init => ReplayInv
<1> SUFFICES ASSUME Init PROVE ReplayInv
  OBVIOUS
<1>1. ReplayOf(consensusLog)[0] = [seen |-> {}, output |-> <<>>]
  BY ReplayZero
<1> QED
  BY <1>1 DEF Init, ReplayInv

LEMMA ReplayUnchanged ==
    ASSUME ReplayInv, UNCHANGED <<consensusLog, processed, seen, delivered>>
    PROVE  ReplayInv'
BY DEF ReplayInv

LEMMA ReplayDecide ==
    ASSUME ReplayInv, NEW batch \in Seq(ResponseItems),
           consensusLog' = Append(consensusLog, batch),
           UNCHANGED <<processed, seen, delivered>>
    PROVE  ReplayInv'
<1> USE DEF ReplayInv
<1>1. consensusLog' \in Seq(Seq(ResponseItems))
  OBVIOUS
<1>2. Len(consensusLog') = Len(consensusLog) + 1
  OBVIOUS
<1>3. \A r \in Replicas :
          ReplayOf(consensusLog')[processed[r]] =
              ReplayOf(consensusLog)[processed[r]]
  BY ReplayAppendStable
<1>4. \A r \in Replicas : processed'[r] <= Len(consensusLog')
  BY <1>2
<1> QED
  BY <1>1, <1>3, <1>4

LEMMA ReplayProcess ==
    ASSUME ReplayInv, NEW replica \in Replicas, ProcessContiguous(replica)
    PROVE  ReplayInv'
<1> DEFINE slot == processed[replica] + 1
           R == ReplayOf(consensusLog)
           result == ApplyItems(consensusLog[slot], seen[replica],
                                delivered[replica])
<1> USE DEF ReplayInv
<1>1. /\ slot \in 1..Len(consensusLog)
      /\ processed' = [processed EXCEPT ![replica] = slot]
      /\ seen' = [seen EXCEPT ![replica] = result.seen]
      /\ delivered' = [delivered EXCEPT ![replica] = result.output]
      /\ consensusLog' = consensusLog
  BY DEF ProcessContiguous
<1>2. processed[replica] \in Nat
  OBVIOUS
<1>3. R[slot] = ApplyItems(consensusLog[slot], R[processed[replica]].seen,
                           R[processed[replica]].output)
  BY <1>2, ReplaySucc
<1>4. R[slot] = result
  BY <1>3
<1> HIDE DEF R, result
<1>5. processed' \in [Replicas -> Nat]
  BY <1>1, <1>2
<1>6. \A r \in Replicas : processed'[r] <= Len(consensusLog')
  BY <1>1, <1>2
<1>7. DOMAIN seen' = Replicas /\ DOMAIN delivered' = Replicas
  BY <1>1
<1>8. \A r \in Replicas :
          /\ seen'[r] = R[processed'[r]].seen
          /\ delivered'[r] = R[processed'[r]].output
  <2> TAKE r \in Replicas
  <2>1. CASE r = replica
    BY <1>1, <1>4, <2>1
  <2>2. CASE r # replica
    BY <1>1, <2>2 DEF R
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>5, <1>6, <1>7, <1>8 DEF R

THEOREM ReplayStep ==
    ASSUME StrictDelivery
    PROVE  ReplayInv /\ [Next]_vars => ReplayInv'
<1> SUFFICES ASSUME ReplayInv, [Next]_vars PROVE ReplayInv'
  OBVIOUS
<1> USE DEF StrictDelivery
<1>1. CASE \E item \in ResponseItems : DecideOne(item)
  <2> PICK item \in ResponseItems : DecideOne(item)
    BY <1>1
  <2>1. <<item>> \in Seq(ResponseItems)
    OBVIOUS
  <2> QED
    BY <2>1, ReplayDecide DEF DecideOne
<1>2. CASE \E first \in ResponseItems, second \in ResponseItems :
              DecidePair(first, second)
  <2> PICK first \in ResponseItems, second \in ResponseItems :
              DecidePair(first, second)
    BY <1>2
  <2>1. <<first, second>> \in Seq(ResponseItems)
    OBVIOUS
  <2> QED
    BY <2>1, ReplayDecide DEF DecidePair
<1>3. CASE ProcessAction
  BY <1>3, ReplayProcess DEF ProcessAction
<1>4. CASE UNCHANGED <<consensusLog, processed, seen, delivered>>
  BY <1>4, ReplayUnchanged
<1>5. \/ \E item \in ResponseItems : DecideOne(item)
      \/ \E first \in ResponseItems, second \in ResponseItems :
              DecidePair(first, second)
      \/ ProcessAction
      \/ UNCHANGED <<consensusLog, processed, seen, delivered>>
  <2>1. CASE UNCHANGED vars
    BY <2>1 DEF vars
  <2>2. CASE SubmitVoteAction
    BY <2>2 DEF SubmitVoteAction, SubmitVote
  <2>3. CASE SelectAction
    BY <2>3 DEF SelectAction, SelectByQuorum, TimeoutSelect
  <2>4. CASE DispatchAction
    BY <2>4 DEF DispatchAction, Dispatch
  <2>5. CASE ExternalRespondAction
    BY <2>5 DEF ExternalRespondAction, ExternalRespond
  <2>6. CASE ProposeResponseAction
    BY <2>6 DEF ProposeResponseAction, ProposeResponse
  <2>7. CASE DecideAction
    BY <2>7 DEF DecideAction
  <2>8. CASE LearnAction
    BY <2>8 DEF LearnAction, LearnSlot
  <2>9. CASE ProcessAction
    BY <2>9
  <2>10. CASE \E replica \in Replicas, slot \in 1..MaxSlots :
                  ProcessNonContiguous(replica, slot)
    BY <2>10 DEF ProcessNonContiguous
  <2>11. CASE \E replica \in Replicas, item \in ResponseItems :
                  DeliverBeforeConsensus(replica, item)
    BY <2>11 DEF DeliverBeforeConsensus
  <2>12. CASE \E replica \in Replicas : Crash(replica)
    BY <2>12 DEF Crash
  <2>13. CASE \E replica \in Replicas : Recover(replica)
    BY <2>13 DEF Recover
  <2>14. CASE \E replica \in Replicas : Elect(replica)
    BY <2>14 DEF Elect
  <2>15. CASE \E replica \in Replicas,
                 request \in RequestIds,
                 payload \in Payloads :
                  NoLeaderDispatch(replica, request, payload)
    BY <2>15 DEF NoLeaderDispatch
  <2>16. CASE \E replica \in Replicas,
                 request \in RequestIds,
                 responseValue \in Responses :
                  DirectNoLeaderRespond(replica, request, responseValue)
    BY <2>16 DEF DirectNoLeaderRespond
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
       <2>11, <2>12, <2>13, <2>14, <2>15, <2>16 DEF Next
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

THEOREM ReplayInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []ReplayInv
<1>1. Init => ReplayInv
  BY ReplayInit
<1>2. ReplayInv /\ [Next]_vars => ReplayInv'
  BY ReplayStep
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************
Step 5: prefix agreement and race-winner agreement.
***************************************************************************)
LEMMA ReplayPointwisePrefix ==
    ASSUME ~MutantNoDedup, ReplayInv,
           NEW left \in Replicas, NEW right \in Replicas,
           processed[left] <= processed[right]
    PROVE  /\ delivered[left] \in Seq(ResponseItems)
           /\ delivered[right] \in Seq(ResponseItems)
           /\ PointwisePrefix(delivered[left], delivered[right])
<1> USE DEF ReplayInv
<1>1. /\ processed[left] \in Nat
      /\ processed[right] \in Nat
      /\ processed[left] <= Len(consensusLog)
      /\ processed[right] <= Len(consensusLog)
  OBVIOUS
<1>2. /\ ReplayOf(consensusLog)[processed[left]].output \in Seq(ResponseItems)
      /\ ReplayOf(consensusLog)[processed[right]].output
             \in Seq(ResponseItems)
  BY <1>1, ReplayOutputType
<1>3. PointwisePrefix(ReplayOf(consensusLog)[processed[left]].output,
                      ReplayOf(consensusLog)[processed[right]].output)
  BY <1>1, ReplayMonotone
<1> QED
  BY <1>2, <1>3

THEOREM ReplayPrefixAgreement ==
    ASSUME ~MutantNoDedup
    PROVE  ReplayInv => PrefixAgreement
<1> SUFFICES ASSUME ReplayInv, NEW left \in Replicas, NEW right \in Replicas
             PROVE  \/ IsPrefix(delivered[left], delivered[right])
                    \/ IsPrefix(delivered[right], delivered[left])
  BY DEF PrefixAgreement
<1>1. processed[left] \in Nat /\ processed[right] \in Nat
  BY DEF ReplayInv
<1>2. CASE processed[left] <= processed[right]
  BY <1>2, ReplayPointwisePrefix, PointwisePrefixIsPrefix
<1>3. CASE processed[right] <= processed[left]
  BY <1>3, ReplayPointwisePrefix, PointwisePrefixIsPrefix
<1> QED
  BY <1>1, <1>2, <1>3

THEOREM ReplayRaceWinnerAgreement ==
    ASSUME ~MutantNoDedup
    PROVE  ReplayInv => RaceWinnerAgreement
<1> SUFFICES ASSUME ReplayInv, NEW left \in Replicas, NEW right \in Replicas,
                    RaceWinner(left) # NoValue, RaceWinner(right) # NoValue
             PROVE  RaceWinner(left) = RaceWinner(right)
  BY DEF RaceWinnerAgreement
<1>1. processed[left] \in Nat /\ processed[right] \in Nat
  BY DEF ReplayInv
<1>2. Len(delivered[left]) # 0 /\ Len(delivered[right]) # 0
  BY DEF RaceWinner
<1>3. ASSUME NEW a \in Replicas, NEW b \in Replicas,
             processed[a] <= processed[b],
             Len(delivered[a]) # 0, Len(delivered[b]) # 0
      PROVE  Head(delivered[a]) = Head(delivered[b])
  <2>1. /\ delivered[a] \in Seq(ResponseItems)
        /\ delivered[b] \in Seq(ResponseItems)
        /\ PointwisePrefix(delivered[a], delivered[b])
    BY <1>3, ReplayPointwisePrefix
  <2>2. 1 \in 1..Len(delivered[a])
    BY <1>3, <2>1
  <2> QED
    BY <2>1, <2>2 DEF PointwisePrefix
<1>4. Head(delivered[left]) = Head(delivered[right])
  BY <1>1, <1>2, <1>3
<1> QED
  BY <1>2, <1>4 DEF RaceWinner

THEOREM PrefixAgreementInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []PrefixAgreement
<1>1. Spec => []ReplayInv
  BY ReplayInvariant
<1>2. ReplayInv => PrefixAgreement
  BY ReplayPrefixAgreement DEF StrictDelivery
<1> QED
  BY <1>1, <1>2, PTL

THEOREM RaceWinnerAgreementInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []RaceWinnerAgreement
<1>1. Spec => []ReplayInv
  BY ReplayInvariant
<1>2. ReplayInv => RaceWinnerAgreement
  BY ReplayRaceWinnerAgreement DEF StrictDelivery
<1> QED
  BY <1>1, <1>2, PTL
=============================================================================

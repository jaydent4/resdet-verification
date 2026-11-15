-------------------------- MODULE ResdetContinuation --------------------------
(***************************************************************************
TLAPS proofs of two further claims of the paper, about Resdet.tla.

Deterministic continuation (Sections 3.3 and 6.3). Service code that
consumes delivered responses in delivery order, starting from the same
state and with a deterministic transition function, is in the same state
at every replica after consuming the same number of responses.

Batching (Section 6.2). How agreed entries are grouped into batches does
not matter: two logs with the same entries in the same order produce the
same deliveries.
***************************************************************************)
EXTENDS ResdetApplied

(* RunUpTo(Step, s0, history)[n]: the application state after consuming
   the first n delivered responses of history from state s0. *)
RunUpTo(Step(_, _), s0, history) ==
    LET run[n \in 0..Len(history)] ==
            IF n = 0 THEN s0 ELSE Step(run[n - 1], history[n])
    IN run

AppState(Step(_, _), s0, history, n) == RunUpTo(Step, s0, history)[n]

SameContinuation(Step(_, _), s0) ==
    \A r, t \in Replicas :
        \A n \in 0..Len(delivered[r]) :
            n <= Len(delivered[t]) =>
                AppState(Step, s0, delivered[r], n) =
                    AppState(Step, s0, delivered[t], n)

(***************************************************************************
RunUpTo unfolded: the state after no responses is s0, and the state after
n responses is one Step from the state after n - 1.
***************************************************************************)
LEMMA RunUpToUnfold ==
    ASSUME NEW Step(_, _), NEW s0, NEW S, NEW h \in Seq(S)
    PROVE  LET f == RunUpTo(Step, s0, h)
           IN  f = [n \in 0..Len(h) |->
                        IF n = 0 THEN s0 ELSE Step(f[n - 1], h[n])]
<1> DEFINE f == RunUpTo(Step, s0, h)
<1>1. Len(h) \in Nat
  OBVIOUS
<1>2. FiniteNatInductiveDefHypothesis(
          f, s0, LAMBDA v, k : Step(v, h[k]), 0, Len(h))
  BY DEF FiniteNatInductiveDefHypothesis, RunUpTo
<1>3. FiniteNatInductiveDefConclusion(
          f, s0, LAMBDA v, k : Step(v, h[k]), 0, Len(h))
  <2> HIDE DEF f
  <2> QED
    BY <1>1, <1>2, FiniteNatInductiveDef
<1> QED
  BY <1>3 DEF FiniteNatInductiveDefConclusion

(***************************************************************************
Two histories that agree on their first n responses lead to the same
application state after n responses.
***************************************************************************)
LEMMA RunAgree ==
    ASSUME NEW Step(_, _), NEW s0, NEW S,
           NEW h1 \in Seq(S), NEW h2 \in Seq(S)
    PROVE  \A n \in Nat :
               (/\ n <= Len(h1)
                /\ n <= Len(h2)
                /\ \A k \in 1..n : h1[k] = h2[k])
               => RunUpTo(Step, s0, h1)[n] = RunUpTo(Step, s0, h2)[n]
<1> DEFINE f1 == RunUpTo(Step, s0, h1)
           f2 == RunUpTo(Step, s0, h2)
           P(n) == (/\ n <= Len(h1)
                    /\ n <= Len(h2)
                    /\ \A k \in 1..n : h1[k] = h2[k])
                   => f1[n] = f2[n]
<1>1. /\ Len(h1) \in Nat
      /\ Len(h2) \in Nat
  OBVIOUS
<1>2. f1 = [n \in 0..Len(h1) |->
               IF n = 0 THEN s0 ELSE Step(f1[n - 1], h1[n])]
  BY RunUpToUnfold
<1>3. f2 = [n \in 0..Len(h2) |->
               IF n = 0 THEN s0 ELSE Step(f2[n - 1], h2[n])]
  BY RunUpToUnfold
<1>4. P(0)
  <2>1. f1[0] = s0
    <3> HIDE DEF f1
    <3> QED
      BY <1>1, <1>2
  <2>2. f2[0] = s0
    <3> HIDE DEF f2
    <3> QED
      BY <1>1, <1>3
  <2> QED
    BY <2>1, <2>2
<1>5. \A n \in Nat : P(n) => P(n + 1)
  <2> TAKE n \in Nat
  <2> HAVE P(n)
  <2> SUFFICES ASSUME n + 1 <= Len(h1),
                      n + 1 <= Len(h2),
                      \A k \in 1..(n + 1) : h1[k] = h2[k]
               PROVE  f1[n + 1] = f2[n + 1]
    OBVIOUS
  <2>1. /\ n <= Len(h1)
        /\ n <= Len(h2)
        /\ \A k \in 1..n : h1[k] = h2[k]
    BY <1>1
  <2>2. f1[n] = f2[n]
    BY <2>1
  <2>3. /\ n + 1 \in 0..Len(h1)
        /\ n + 1 \in 0..Len(h2)
        /\ n + 1 # 0
        /\ (n + 1) - 1 = n
    BY <1>1
  <2>4. f1[n + 1] = Step(f1[n], h1[n + 1])
    <3> HIDE DEF f1
    <3> QED
      BY <1>2, <2>3
  <2>5. f2[n + 1] = Step(f2[n], h2[n + 1])
    <3> HIDE DEF f2
    <3> QED
      BY <1>3, <2>3
  <2>6. h1[n + 1] = h2[n + 1]
    BY <1>1
  <2> HIDE DEF f1, f2
  <2> QED
    BY <2>2, <2>4, <2>5, <2>6
<1>6. \A n \in Nat : P(n)
  <2> HIDE DEF P
  <2> QED
    BY <1>4, <1>5, NatInduction
<1> QED
  BY <1>6

(***************************************************************************
Prefix-comparable histories agree on every index both of them have.
***************************************************************************)
LEMMA PrefixAgreesPointwise ==
    ASSUME NEW S, NEW left \in Seq(S), NEW right \in Seq(S),
           IsPrefix(left, right)
    PROVE  \A k \in 1..Len(left) : left[k] = right[k]
<1>1. CASE left = <<>>
  <2>1. Len(left) = 0
    BY <1>1
  <2> QED
    BY <2>1
<1>2. CASE /\ Len(left) <= Len(right)
           /\ SubSeq(right, 1, Len(left)) = left
  <2>1. /\ Len(left) \in Nat
        /\ Len(right) \in Nat
    OBVIOUS
  <2>2. \A k \in 1..Len(left) :
            SubSeq(right, 1, Len(left))[k] = right[k]
    BY <1>2, <2>1
  <2> QED
    BY <1>2, <2>2
<1> QED
  BY <1>1, <1>2 DEF IsPrefix

LEMMA ContinuationFromPrefix ==
    ASSUME NEW Step(_, _), NEW s0
    PROVE  DeliveryInv /\ PrefixAgreement => SameContinuation(Step, s0)
<1> SUFFICES ASSUME DeliveryInv, PrefixAgreement,
                    NEW r \in Replicas, NEW t \in Replicas,
                    NEW n \in 0..Len(delivered[r]),
                    n <= Len(delivered[t])
             PROVE  AppState(Step, s0, delivered[r], n) =
                        AppState(Step, s0, delivered[t], n)
  BY DEF SameContinuation
<1>1. PICK h1 \in Seq(ResponseItems) : h1 = delivered[r]
  BY DEF DeliveryInv, DeliveryTypeOK
<1>2. PICK h2 \in Seq(ResponseItems) : h2 = delivered[t]
  BY DEF DeliveryInv, DeliveryTypeOK
<1>3. /\ Len(h1) \in Nat
      /\ Len(h2) \in Nat
      /\ n \in Nat
      /\ n <= Len(h1)
      /\ n <= Len(h2)
  BY <1>1, <1>2
<1>4. IsPrefix(h1, h2) \/ IsPrefix(h2, h1)
  BY <1>1, <1>2 DEF PrefixAgreement
<1>5. \A k \in 1..n : h1[k] = h2[k]
  <2>1. CASE IsPrefix(h1, h2)
    <3>1. \A k \in 1..Len(h1) : h1[k] = h2[k]
      BY <2>1, PrefixAgreesPointwise
    <3> QED
      BY <1>3, <3>1
  <2>2. CASE IsPrefix(h2, h1)
    <3>1. \A k \in 1..Len(h2) : h2[k] = h1[k]
      BY <2>2, PrefixAgreesPointwise
    <3> QED
      BY <1>3, <3>1
  <2> QED
    BY <1>4, <2>1, <2>2
<1>6. \A m \in Nat :
          (/\ m <= Len(h1)
           /\ m <= Len(h2)
           /\ \A k \in 1..m : h1[k] = h2[k])
          => RunUpTo(Step, s0, h1)[m] = RunUpTo(Step, s0, h2)[m]
  BY RunAgree
<1>7. RunUpTo(Step, s0, h1)[n] = RunUpTo(Step, s0, h2)[n]
  BY <1>3, <1>5, <1>6
<1> QED
  BY <1>1, <1>2, <1>7 DEF AppState

THEOREM DeterministicContinuation ==
    ASSUME StrictDelivery, NEW Step(_, _), NEW s0
    PROVE  Spec => []SameContinuation(Step, s0)
<1>1. DeliveryInv /\ PrefixAgreement => SameContinuation(Step, s0)
  BY ContinuationFromPrefix
<1> QED
  BY <1>1, DeliveryInvariant, PrefixAgreementInvariant, PTL

(***************************************************************************
The replay of a whole log is the deduplication of its flattening, so it
depends on the log only through the flattening.
***************************************************************************)
LEMMA ReplayOfWholeLog ==
    ASSUME ~MutantNoDedup, NEW S, NEW log \in Seq(Seq(S))
    PROVE  /\ ReplayOf(log)[Len(log)].output =
                  DedupRun(FlattenBatches(log), {}, <<>>).output
           /\ ReplayOf(log)[Len(log)].seen =
                  DedupRun(FlattenBatches(log), {}, <<>>).seen
<1>1. Len(log) \in Nat /\ Len(log) <= Len(log)
  OBVIOUS
<1>2. FlattenBatches(log) = FlatUpTo(log)[Len(log)]
  BY FlattenIsFlatUpTo
<1>3. /\ DedupRun(FlatUpTo(log)[Len(log)], {}, <<>>).seen =
            ReplayOf(log)[Len(log)].seen
      /\ DedupRun(FlatUpTo(log)[Len(log)], {}, <<>>).output =
            ReplayOf(log)[Len(log)].output
  BY <1>1, DedupFlatIsReplay
<1> QED
  BY <1>2, <1>3

THEOREM RebatchingPreservesDelivery ==
    ASSUME ~MutantNoDedup,
           NEW S,
           NEW log1 \in Seq(Seq(S)), NEW log2 \in Seq(Seq(S)),
           FlattenBatches(log1) = FlattenBatches(log2)
    PROVE  /\ ReplayOf(log1)[Len(log1)].output =
                  ReplayOf(log2)[Len(log2)].output
           /\ ReplayOf(log1)[Len(log1)].seen =
                  ReplayOf(log2)[Len(log2)].seen
<1>1. /\ ReplayOf(log1)[Len(log1)].output =
            DedupRun(FlattenBatches(log1), {}, <<>>).output
      /\ ReplayOf(log1)[Len(log1)].seen =
            DedupRun(FlattenBatches(log1), {}, <<>>).seen
  BY ReplayOfWholeLog
<1>2. /\ ReplayOf(log2)[Len(log2)].output =
            DedupRun(FlattenBatches(log2), {}, <<>>).output
      /\ ReplayOf(log2)[Len(log2)].seen =
            DedupRun(FlattenBatches(log2), {}, <<>>).seen
  BY ReplayOfWholeLog
<1> QED
  BY <1>1, <1>2
=============================================================================

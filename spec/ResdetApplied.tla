---------------------------- MODULE ResdetApplied ----------------------------
(***************************************************************************
TLAPS proof of AppliedPrefixCorrect in the literal form the TLC
configurations check: a replica's delivery history is the deduplicated
flattening of the log prefix it has processed,

    delivered[r] = DedupFrom(FlattenBatches(SubSeq(consensusLog, 1, n)), {})

for n = processed[r]. ReplayInvariant (ResdetPrefix.tla) states the same
fact through ApplyItems; this module connects the two folds.

The connection is a statement about folds only, with no reference to the
protocol. Write G(n) for the flattening of the first n batches of a log.

  FlatPrefix          FlattenBatches(SubSeq(log, 1, n)) is G(n), and
                      G(n + 1) = G(n) \o log[n + 1].
  DedupConcat         Deduplicating a \o b is deduplicating b, started
                      from the state that deduplicating a ends in.
  DedupIsApply        Deduplicating one batch from a given state is
                      ApplyItems on that batch (with MutantNoDedup off).
  DedupFlatIsReplay   By induction on n: deduplicating G(n) from the
                      empty state gives the replay state ReplayOf(log)[n].

Do not add SequenceTheorems to the EXTENDS list (see ResdetFold.tla); the
facts about \o and SubSeq used here are proved directly.
***************************************************************************)
EXTENDS ResdetTheorems

(***************************************************************************
The two folds of Resdet.tla with their recursive functions named, so the
proofs can speak about the state after a prefix. DedupFrom(items, sn) is
DedupRun(items, sn, <<>>).output and FlattenBatches(log) is
FlatUpTo(log)[Len(log)], by definition.
***************************************************************************)
DedupUpTo(items, sn, out) ==
    LET step[count \in 0..Len(items)] ==
            IF count = 0
            THEN [seen |-> sn, output |-> out]
            ELSE DedupItem(step[count - 1], items[count])
    IN step

DedupRun(items, sn, out) == DedupUpTo(items, sn, out)[Len(items)]

FlatUpTo(log) ==
    LET flat[count \in 0..Len(log)] ==
            IF count = 0
            THEN <<>>
            ELSE flat[count - 1] \o log[count]
    IN flat

LEMMA DedupFromIsRun ==
    ASSUME NEW items, NEW sn
    PROVE  DedupFrom(items, sn) = DedupRun(items, sn, <<>>).output
BY DEF DedupFrom, DedupRun, DedupUpTo

LEMMA FlattenIsFlatUpTo ==
    ASSUME NEW log
    PROVE  FlattenBatches(log) = FlatUpTo(log)[Len(log)]
BY DEF FlattenBatches, FlatUpTo

(***************************************************************************
Unfolding the three recursive functions: the value at 0 and at n + 1.
***************************************************************************)
LEMMA DedupUpToStep ==
    ASSUME NEW S, NEW items \in Seq(S), NEW sn, NEW out
    PROVE  /\ DedupUpTo(items, sn, out)[0] = [seen |-> sn, output |-> out]
           /\ \A n \in Nat :
                n < Len(items) =>
                    DedupUpTo(items, sn, out)[n + 1] =
                        DedupItem(DedupUpTo(items, sn, out)[n], items[n + 1])
<1> DEFINE f == DedupUpTo(items, sn, out)
           c == [seen |-> sn, output |-> out]
<1>1. Len(items) \in Nat
  OBVIOUS
<1>2. FiniteNatInductiveDefHypothesis(
          f, c, LAMBDA v, i : DedupItem(v, items[i]), 0, Len(items))
  BY DEF FiniteNatInductiveDefHypothesis, DedupUpTo
<1>3. FiniteNatInductiveDefConclusion(
          f, c, LAMBDA v, i : DedupItem(v, items[i]), 0, Len(items))
  <2> HIDE DEF f, c
  <2> QED
    BY <1>1, <1>2, FiniteNatInductiveDef
<1>4. f = [count \in 0..Len(items) |->
              IF count = 0 THEN c ELSE DedupItem(f[count - 1], items[count])]
  BY <1>3 DEF FiniteNatInductiveDefConclusion
<1> HIDE DEF f
<1>5. f[0] = c
  BY <1>1, <1>4
<1>6. ASSUME NEW n \in Nat, n < Len(items)
      PROVE  f[n + 1] = DedupItem(f[n], items[n + 1])
  <2>1. n + 1 \in 0..Len(items) /\ n + 1 # 0 /\ (n + 1) - 1 = n
    BY <1>1, <1>6
  <2>2. f[n + 1] = DedupItem(f[(n + 1) - 1], items[n + 1])
    BY <1>4, <2>1
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>5, <1>6 DEF f

LEMMA ApplyUpToStep ==
    ASSUME NEW S, NEW items \in Seq(S), NEW sn, NEW out
    PROVE  /\ ApplyItemsUpTo(items, sn, out)[0] =
                 [seen |-> sn, output |-> out]
           /\ \A n \in Nat :
                n < Len(items) =>
                    ApplyItemsUpTo(items, sn, out)[n + 1] =
                        ApplyItem(ApplyItemsUpTo(items, sn, out)[n],
                                  items[n + 1])
<1> DEFINE f == ApplyItemsUpTo(items, sn, out)
           c == [seen |-> sn, output |-> out]
<1>1. Len(items) \in Nat
  OBVIOUS
<1>4. f = [count \in 0..Len(items) |->
              IF count = 0 THEN c ELSE ApplyItem(f[count - 1], items[count])]
  BY ApplyItemsUpToUnfold
<1> HIDE DEF f
<1>5. f[0] = c
  BY <1>1, <1>4
<1>6. ASSUME NEW n \in Nat, n < Len(items)
      PROVE  f[n + 1] = ApplyItem(f[n], items[n + 1])
  <2>1. n + 1 \in 0..Len(items) /\ n + 1 # 0 /\ (n + 1) - 1 = n
    BY <1>1, <1>6
  <2>2. f[n + 1] = ApplyItem(f[(n + 1) - 1], items[n + 1])
    BY <1>4, <2>1
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>5, <1>6 DEF f

LEMMA FlatUpToStep ==
    ASSUME NEW S, NEW log \in Seq(Seq(S))
    PROVE  /\ FlatUpTo(log)[0] = <<>>
           /\ \A n \in Nat :
                n < Len(log) =>
                    FlatUpTo(log)[n + 1] = FlatUpTo(log)[n] \o log[n + 1]
<1> DEFINE f == FlatUpTo(log)
<1>1. Len(log) \in Nat
  OBVIOUS
<1>2. FiniteNatInductiveDefHypothesis(
          f, <<>>, LAMBDA v, i : v \o log[i], 0, Len(log))
  BY DEF FiniteNatInductiveDefHypothesis, FlatUpTo
<1>3. FiniteNatInductiveDefConclusion(
          f, <<>>, LAMBDA v, i : v \o log[i], 0, Len(log))
  <2> HIDE DEF f
  <2> QED
    BY <1>1, <1>2, FiniteNatInductiveDef
<1>4. f = [count \in 0..Len(log) |->
              IF count = 0 THEN <<>> ELSE f[count - 1] \o log[count]]
  BY <1>3 DEF FiniteNatInductiveDefConclusion
<1> HIDE DEF f
<1>5. f[0] = <<>>
  BY <1>1, <1>4
<1>6. ASSUME NEW n \in Nat, n < Len(log)
      PROVE  f[n + 1] = f[n] \o log[n + 1]
  <2>1. n + 1 \in 0..Len(log) /\ n + 1 # 0 /\ (n + 1) - 1 = n
    BY <1>1, <1>6
  <2>2. f[n + 1] = f[(n + 1) - 1] \o log[n + 1]
    BY <1>4, <2>1
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>5, <1>6 DEF f

(***************************************************************************
One step of either fold reads only the seen and output fields of the
state. ApplyItem builds a fresh record where DedupItem may return its
argument, so the folds are compared field by field.
***************************************************************************)
LEMMA DedupItemFields ==
    ASSUME NEW st1, NEW st2, NEW item,
           st1.seen = st2.seen, st1.output = st2.output
    PROVE  /\ DedupItem(st1, item).seen = DedupItem(st2, item).seen
           /\ DedupItem(st1, item).output = DedupItem(st2, item).output
BY DEF DedupItem

LEMMA DedupApplyFields ==
    ASSUME ~MutantNoDedup, NEW st1, NEW st2, NEW item,
           st1.seen = st2.seen, st1.output = st2.output
    PROVE  /\ DedupItem(st1, item).seen = ApplyItem(st2, item).seen
           /\ DedupItem(st1, item).output = ApplyItem(st2, item).output
BY DEF DedupItem, ApplyItem

(***************************************************************************
With deduplication on, the dedup fold over a batch is ApplyItems.
***************************************************************************)
LEMMA DedupIsApply ==
    ASSUME ~MutantNoDedup, NEW S, NEW items \in Seq(S), NEW sn, NEW out
    PROVE  /\ DedupRun(items, sn, out).seen =
                 ApplyItems(items, sn, out).seen
           /\ DedupRun(items, sn, out).output =
                 ApplyItems(items, sn, out).output
<1> DEFINE fd == DedupUpTo(items, sn, out)
           fa == ApplyItemsUpTo(items, sn, out)
           Q(n) == n \in 0..Len(items) =>
                       /\ fd[n].seen = fa[n].seen
                       /\ fd[n].output = fa[n].output
<1>0. Len(items) \in Nat
  OBVIOUS
<1>1. /\ fd[0] = [seen |-> sn, output |-> out]
      /\ \A n \in Nat :
           n < Len(items) => fd[n + 1] = DedupItem(fd[n], items[n + 1])
  BY DedupUpToStep
<1>2. /\ fa[0] = [seen |-> sn, output |-> out]
      /\ \A n \in Nat :
           n < Len(items) => fa[n + 1] = ApplyItem(fa[n], items[n + 1])
  BY ApplyUpToStep
<1> HIDE DEF fd, fa
<1>3. Q(0)
  BY <1>1, <1>2
<1>4. \A n \in Nat : Q(n) => Q(n + 1)
  <2> TAKE n \in Nat
  <2> SUFFICES ASSUME Q(n), n + 1 \in 0..Len(items)
               PROVE  /\ fd[n + 1].seen = fa[n + 1].seen
                      /\ fd[n + 1].output = fa[n + 1].output
    OBVIOUS
  <2>1. n \in 0..Len(items) /\ n < Len(items)
    BY <1>0
  <2>2. fd[n].seen = fa[n].seen /\ fd[n].output = fa[n].output
    BY <2>1
  <2>3. fd[n + 1] = DedupItem(fd[n], items[n + 1])
    BY <1>1, <2>1
  <2>4. fa[n + 1] = ApplyItem(fa[n], items[n + 1])
    BY <1>2, <2>1
  <2>5. /\ DedupItem(fd[n], items[n + 1]).seen =
              ApplyItem(fa[n], items[n + 1]).seen
        /\ DedupItem(fd[n], items[n + 1]).output =
              ApplyItem(fa[n], items[n + 1]).output
    BY <2>2, DedupApplyFields
  <2> QED
    BY <2>3, <2>4, <2>5
<1>5. \A n \in Nat : Q(n)
  <2> HIDE DEF Q
  <2> QED
    BY <1>3, <1>4, NatInduction
<1>6. Q(Len(items))
  BY <1>0, <1>5
<1> QED
  BY <1>0, <1>6 DEF DedupRun, ApplyItems, fd, fa

(***************************************************************************
The dedup fold over a concatenation.
***************************************************************************)
LEMMA DedupConcat ==
    ASSUME NEW S, NEW a \in Seq(S), NEW b \in Seq(S), NEW sn, NEW out
    PROVE  /\ DedupRun(a \o b, sn, out).seen =
                 DedupRun(b, DedupRun(a, sn, out).seen,
                          DedupRun(a, sn, out).output).seen
           /\ DedupRun(a \o b, sn, out).output =
                 DedupRun(b, DedupRun(a, sn, out).seen,
                          DedupRun(a, sn, out).output).output
<1> DEFINE ab == a \o b
           fa == DedupUpTo(a, sn, out)
           fab == DedupUpTo(ab, sn, out)
           mid == fa[Len(a)]
           fb == DedupUpTo(b, mid.seen, mid.output)
           P1(i) == i \in 0..Len(a) => fab[i] = fa[i]
           P2(j) == j \in 0..Len(b) =>
                       /\ fab[Len(a) + j].seen = fb[j].seen
                       /\ fab[Len(a) + j].output = fb[j].output
<1>0. /\ Len(a) \in Nat
      /\ Len(b) \in Nat
      /\ ab \in Seq(S)
      /\ Len(ab) = Len(a) + Len(b)
  OBVIOUS
<1>0a. \A i \in 1..Len(a) : ab[i] = a[i]
  OBVIOUS
<1>0b. \A j \in 1..Len(b) : ab[Len(a) + j] = b[j]
  OBVIOUS
<1>1. /\ fa[0] = [seen |-> sn, output |-> out]
      /\ \A n \in Nat : n < Len(a) => fa[n + 1] = DedupItem(fa[n], a[n + 1])
  BY DedupUpToStep
<1>2. /\ fab[0] = [seen |-> sn, output |-> out]
      /\ \A n \in Nat :
           n < Len(ab) => fab[n + 1] = DedupItem(fab[n], ab[n + 1])
  BY <1>0, DedupUpToStep
<1>3. /\ fb[0] = [seen |-> mid.seen, output |-> mid.output]
      /\ \A n \in Nat : n < Len(b) => fb[n + 1] = DedupItem(fb[n], b[n + 1])
  BY DedupUpToStep
<1>4. mid = fa[Len(a)]
  OBVIOUS
<1> HIDE DEF ab, fa, fab, mid, fb
<1>5. \A i \in Nat : P1(i)
  <2>1. P1(0)
    BY <1>1, <1>2
  <2>2. \A i \in Nat : P1(i) => P1(i + 1)
    <3> TAKE i \in Nat
    <3> SUFFICES ASSUME P1(i), i + 1 \in 0..Len(a)
                 PROVE  fab[i + 1] = fa[i + 1]
      OBVIOUS
    <3>1. /\ i \in 0..Len(a) /\ i < Len(a) /\ i < Len(ab)
          /\ i + 1 \in 1..Len(a)
      BY <1>0
    <3>2. fab[i] = fa[i]
      BY <3>1
    <3>3. fab[i + 1] = DedupItem(fab[i], ab[i + 1])
      BY <1>2, <3>1
    <3>4. fa[i + 1] = DedupItem(fa[i], a[i + 1])
      BY <1>1, <3>1
    <3>5. ab[i + 1] = a[i + 1]
      BY <1>0a, <3>1
    <3> QED
      BY <3>2, <3>3, <3>4, <3>5
  <2> HIDE DEF P1
  <2> QED
    BY <2>1, <2>2, NatInduction
<1>6. fab[Len(a)] = mid
  BY <1>0, <1>4, <1>5
<1>7. \A j \in Nat : P2(j)
  <2>1. P2(0)
    <3>1. Len(a) + 0 = Len(a)
      BY <1>0
    <3> QED
      BY <1>3, <1>6, <3>1
  <2>2. \A j \in Nat : P2(j) => P2(j + 1)
    <3> TAKE j \in Nat
    <3> SUFFICES ASSUME P2(j), j + 1 \in 0..Len(b)
                 PROVE  /\ fab[Len(a) + (j + 1)].seen = fb[j + 1].seen
                        /\ fab[Len(a) + (j + 1)].output = fb[j + 1].output
      OBVIOUS
    <3>1. /\ j \in 0..Len(b) /\ j < Len(b)
          /\ j + 1 \in 1..Len(b)
          /\ Len(a) + j \in Nat
          /\ Len(a) + j < Len(ab)
          /\ (Len(a) + j) + 1 = Len(a) + (j + 1)
      BY <1>0
    <3>2. /\ fab[Len(a) + j].seen = fb[j].seen
          /\ fab[Len(a) + j].output = fb[j].output
      BY <3>1
    <3>3. fab[(Len(a) + j) + 1] =
              DedupItem(fab[Len(a) + j], ab[(Len(a) + j) + 1])
      BY <1>2, <3>1
    <3>4. fb[j + 1] = DedupItem(fb[j], b[j + 1])
      BY <1>3, <3>1
    <3>5. ab[Len(a) + (j + 1)] = b[j + 1]
      BY <1>0b, <3>1
    <3>6. fab[Len(a) + (j + 1)] = DedupItem(fab[Len(a) + j], b[j + 1])
      BY <3>1, <3>3, <3>5
    <3>7. /\ DedupItem(fab[Len(a) + j], b[j + 1]).seen =
                DedupItem(fb[j], b[j + 1]).seen
          /\ DedupItem(fab[Len(a) + j], b[j + 1]).output =
                DedupItem(fb[j], b[j + 1]).output
      BY <3>2, DedupItemFields
    <3> QED
      BY <3>4, <3>6, <3>7
  <2> HIDE DEF P2
  <2> QED
    BY <2>1, <2>2, NatInduction
<1>8. /\ fab[Len(ab)].seen = fb[Len(b)].seen
      /\ fab[Len(ab)].output = fb[Len(b)].output
  BY <1>0, <1>7
<1> QED
  BY <1>8 DEF DedupRun, ab, fa, fab, mid, fb

(***************************************************************************
Flattening a prefix of the log.
***************************************************************************)
LEMMA FlatUpToType ==
    ASSUME NEW S, NEW log \in Seq(Seq(S))
    PROVE  \A n \in Nat : n <= Len(log) => FlatUpTo(log)[n] \in Seq(S)
<1> DEFINE f == FlatUpTo(log)
           T(n) == n <= Len(log) => f[n] \in Seq(S)
<1>0. Len(log) \in Nat
  OBVIOUS
<1>1. /\ f[0] = <<>>
      /\ \A n \in Nat : n < Len(log) => f[n + 1] = f[n] \o log[n + 1]
  BY FlatUpToStep
<1> HIDE DEF f
<1>2. T(0)
  BY <1>1
<1>3. \A n \in Nat : T(n) => T(n + 1)
  <2> TAKE n \in Nat
  <2> SUFFICES ASSUME T(n), n + 1 <= Len(log)
               PROVE  f[n + 1] \in Seq(S)
    OBVIOUS
  <2>1. n <= Len(log) /\ n < Len(log) /\ n + 1 \in 1..Len(log)
    BY <1>0
  <2>2. f[n] \in Seq(S)
    BY <2>1
  <2>3. log[n + 1] \in Seq(S)
    BY <2>1
  <2>4. f[n + 1] = f[n] \o log[n + 1]
    BY <1>1, <2>1
  <2> QED
    BY <2>2, <2>3, <2>4
<1>4. \A n \in Nat : T(n)
  <2> HIDE DEF T
  <2> QED
    BY <1>2, <1>3, NatInduction
<1> QED
  BY <1>4 DEF f

LEMMA FlatPrefix ==
    ASSUME NEW S, NEW log \in Seq(Seq(S)), NEW n \in Nat, n <= Len(log)
    PROVE  FlattenBatches(SubSeq(log, 1, n)) = FlatUpTo(log)[n]
<1> DEFINE p == SubSeq(log, 1, n)
           fp == FlatUpTo(p)
           fl == FlatUpTo(log)
           R(i) == i \in 0..n => fp[i] = fl[i]
<1>0. Len(log) \in Nat
  OBVIOUS
<1>0a. p \in Seq(Seq(S))
  BY <1>0
<1>0b. Len(p) = n
  BY <1>0
<1>0c. \A i \in 1..n : p[i] = log[i]
  BY <1>0
<1>1. /\ fp[0] = <<>>
      /\ \A i \in Nat : i < Len(p) => fp[i + 1] = fp[i] \o p[i + 1]
  BY <1>0a, FlatUpToStep
<1>2. /\ fl[0] = <<>>
      /\ \A i \in Nat : i < Len(log) => fl[i + 1] = fl[i] \o log[i + 1]
  BY FlatUpToStep
<1>3. FlattenBatches(p) = fp[Len(p)]
  BY FlattenIsFlatUpTo
<1> HIDE DEF p, fp, fl
<1>4. R(0)
  BY <1>1, <1>2
<1>5. \A i \in Nat : R(i) => R(i + 1)
  <2> TAKE i \in Nat
  <2> SUFFICES ASSUME R(i), i + 1 \in 0..n
               PROVE  fp[i + 1] = fl[i + 1]
    OBVIOUS
  <2>1. /\ i \in 0..n /\ i < n /\ i < Len(p) /\ i < Len(log)
        /\ i + 1 \in 1..n
    BY <1>0, <1>0b
  <2>2. fp[i] = fl[i]
    BY <2>1
  <2>3. fp[i + 1] = fp[i] \o p[i + 1]
    BY <1>1, <2>1
  <2>4. fl[i + 1] = fl[i] \o log[i + 1]
    BY <1>2, <2>1
  <2>5. p[i + 1] = log[i + 1]
    BY <1>0c, <2>1
  <2> QED
    BY <2>2, <2>3, <2>4, <2>5
<1>6. \A i \in Nat : R(i)
  <2> HIDE DEF R
  <2> QED
    BY <1>4, <1>5, NatInduction
<1>7. fp[n] = fl[n]
  BY <1>6
<1> QED
  BY <1>0b, <1>3, <1>7 DEF p, fl

(***************************************************************************
Deduplicating the flattened n-prefix from the empty state gives the
replay state after n indexes.
***************************************************************************)
LEMMA DedupFlatIsReplay ==
    ASSUME ~MutantNoDedup, NEW S, NEW log \in Seq(Seq(S))
    PROVE  \A n \in Nat :
               n <= Len(log) =>
                   /\ DedupRun(FlatUpTo(log)[n], {}, <<>>).seen =
                         ReplayOf(log)[n].seen
                   /\ DedupRun(FlatUpTo(log)[n], {}, <<>>).output =
                         ReplayOf(log)[n].output
<1> DEFINE G(n) == FlatUpTo(log)[n]
           D(n) == DedupRun(G(n), {}, <<>>)
           Rep(n) == ReplayOf(log)[n]
           M(n) == n <= Len(log) =>
                       /\ D(n).seen = Rep(n).seen
                       /\ D(n).output = Rep(n).output
<1>0. Len(log) \in Nat
  OBVIOUS
<1>1. \A n \in Nat : n <= Len(log) => G(n) \in Seq(S)
  BY FlatUpToType
<1>2. /\ G(0) = <<>>
      /\ \A n \in Nat : n < Len(log) => G(n + 1) = G(n) \o log[n + 1]
  BY FlatUpToStep
<1>3. M(0)
  <2>1. <<>> \in Seq(S) /\ Len(<<>>) = 0
    OBVIOUS
  <2>2. DedupUpTo(<<>>, {}, <<>>)[0] = [seen |-> {}, output |-> <<>>]
    BY <2>1, DedupUpToStep
  <2>3. D(0) = [seen |-> {}, output |-> <<>>]
    BY <1>2, <2>1, <2>2 DEF DedupRun
  <2>4. Rep(0) = [seen |-> {}, output |-> <<>>]
    BY ReplayZero
  <2> QED
    BY <2>3, <2>4
<1>4. \A n \in Nat : M(n) => M(n + 1)
  <2> TAKE n \in Nat
  <2> SUFFICES ASSUME M(n), n + 1 <= Len(log)
               PROVE  /\ D(n + 1).seen = Rep(n + 1).seen
                      /\ D(n + 1).output = Rep(n + 1).output
    OBVIOUS
  <2>1. n <= Len(log) /\ n < Len(log) /\ n + 1 \in 1..Len(log)
    BY <1>0
  <2>2. D(n).seen = Rep(n).seen /\ D(n).output = Rep(n).output
    BY <2>1
  <2>3. G(n) \in Seq(S)
    BY <1>1, <2>1
  <2>4. log[n + 1] \in Seq(S)
    BY <2>1
  <2>5. G(n + 1) = G(n) \o log[n + 1]
    BY <1>2, <2>1
  <2> DEFINE batch == log[n + 1]
             next == DedupRun(batch, D(n).seen, D(n).output)
  <2>6. /\ DedupRun(G(n) \o batch, {}, <<>>).seen = next.seen
        /\ DedupRun(G(n) \o batch, {}, <<>>).output = next.output
    <3> HIDE DEF G
    <3> QED
      BY <2>3, <2>4, DedupConcat
  <2>7. /\ next.seen = ApplyItems(batch, D(n).seen, D(n).output).seen
        /\ next.output = ApplyItems(batch, D(n).seen, D(n).output).output
    <3> HIDE DEF D
    <3> QED
      BY <2>4, DedupIsApply
  <2>8. ApplyItems(batch, D(n).seen, D(n).output) =
            ApplyItems(batch, Rep(n).seen, Rep(n).output)
    <3> HIDE DEF D, Rep, batch
    <3> QED
      BY <2>2
  <2>9. Rep(n + 1) = ApplyItems(batch, Rep(n).seen, Rep(n).output)
    BY ReplaySucc
  <2>10. D(n + 1) = DedupRun(G(n) \o batch, {}, <<>>)
    <3> HIDE DEF G
    <3> QED
      BY <2>5
  <2> HIDE DEF D, G, Rep, batch, next
  <2> QED
    BY <2>6, <2>7, <2>8, <2>9, <2>10
<1>5. \A n \in Nat : M(n)
  <2> HIDE DEF M
  <2> QED
    BY <1>3, <1>4, NatInduction
<1> QED
  BY <1>5

(***************************************************************************
The replay invariant gives the literal TLC invariant.
***************************************************************************)
LEMMA ReplayImpliesApplied ==
    ASSUME ~MutantNoDedup
    PROVE  ReplayInv => AppliedPrefixCorrect
<1> SUFFICES ASSUME ReplayInv, NEW r \in Replicas
             PROVE  delivered[r] = CorrectAppliedPrefix(r)
  BY DEF AppliedPrefixCorrect
<1> DEFINE n == processed[r]
<1>1. /\ consensusLog \in Seq(Seq(ResponseItems))
      /\ n \in Nat
      /\ n <= Len(consensusLog)
      /\ delivered[r] = ReplayOf(consensusLog)[n].output
  BY DEF ReplayInv
<1>2. FlattenedPrefix(n) = FlatUpTo(consensusLog)[n]
  <2>1. CASE n = 0
    <3>1. FlattenedPrefix(n) = <<>>
      BY <2>1 DEF FlattenedPrefix
    <3>2. FlatUpTo(consensusLog)[0] = <<>>
      BY <1>1, FlatUpToStep
    <3> QED
      BY <2>1, <3>1, <3>2
  <2>2. CASE n # 0
    <3>1. FlattenedPrefix(n) = FlattenBatches(SubSeq(consensusLog, 1, n))
      BY <2>2 DEF FlattenedPrefix
    <3>2. FlattenBatches(SubSeq(consensusLog, 1, n)) =
              FlatUpTo(consensusLog)[n]
      BY <1>1, FlatPrefix
    <3> QED
      BY <3>1, <3>2
  <2> QED
    BY <2>1, <2>2
<1>3. CorrectAppliedPrefix(r) =
          DedupRun(FlattenedPrefix(n), {}, <<>>).output
  BY DedupFromIsRun DEF CorrectAppliedPrefix
<1>4. DedupRun(FlatUpTo(consensusLog)[n], {}, <<>>).output =
          ReplayOf(consensusLog)[n].output
  BY <1>1, DedupFlatIsReplay
<1> HIDE DEF n
<1> QED
  BY <1>1, <1>2, <1>3, <1>4

THEOREM AppliedPrefixCorrectInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []AppliedPrefixCorrect
<1>1. ReplayInv => AppliedPrefixCorrect
  BY ReplayImpliesApplied DEF StrictDelivery
<1> QED
  BY <1>1, ReplayInvariant, PTL
=============================================================================

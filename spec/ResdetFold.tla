----------------------------- MODULE ResdetFold -----------------------------
(***************************************************************************
TLAPS proofs, part 1 of 5: what applying one agreed batch does to a
replica's delivery state.

ApplyItems (Resdet.tla) is the body of the pseudocode's process() loop for
one log index. It is a recursive function over a prefix length, so every
fact about it is proved here by induction on that length and the other
proof modules use only the summary AppliedCorrectly.

Do not add SequenceTheorems to the EXTENDS list of this module: it makes a
second, LOCAL copy of NaturalsInduction, and TLAPS then cannot match
FiniteNatInductiveDefHypothesis/Conclusion against the library theorem.
***************************************************************************)
EXTENDS Resdet, NaturalsInduction, TLAPS

(***************************************************************************
The strict protocol's delivery path. Every theorem about delivery assumes
these four switches are off; each one is a deliberate TLC mutant (or the
no-known-leader escape hatch) that bypasses agreement, ordering, or
deduplication. All other constants stay arbitrary: any replica set, any
request/response sets, any quorum, batching on or off, crashes and
re-elections on or off, timeout fallback on or off, any MaxSlots.
***************************************************************************)
StrictDelivery ==
    /\ ~MutantNoDedup
    /\ ~MutantNonContiguous
    /\ ~MutantEarlyDelivery
    /\ ~EnableNoLeaderFallback

(***************************************************************************
AppliedCorrectly(S, items, sn, out, result) says result is what processing
the batch items does to a replica whose deduplication state is sn and whose
delivery history is out:

  1. every request id in the batch is recorded;
  2. the history stays a sequence over S;
  3-4. the old history is kept as a prefix;
  5. each newly delivered entry is a batch entry whose request id was not
     recorded before and does not occur earlier in the batch;
  6. no request id is newly delivered twice;
  7. every not-yet-recorded request id in the batch is delivered.
***************************************************************************)
AppliedCorrectly(S, items, sn, out, result) ==
    /\ result.seen = sn \union {items[k].rid : k \in 1..Len(items)}
    /\ result.output \in Seq(S)
    /\ Len(out) <= Len(result.output)
    /\ \A i \in 1..Len(out) : result.output[i] = out[i]
    /\ \A i \in (Len(out) + 1)..Len(result.output) :
         \E k \in 1..Len(items) :
            /\ result.output[i] = items[k]
            /\ items[k].rid \notin sn
            /\ \A j \in 1..(k - 1) : items[j].rid # items[k].rid
    /\ \A i, j \in (Len(out) + 1)..Len(result.output) :
         result.output[i].rid = result.output[j].rid => i = j
    /\ \A k \in 1..Len(items) :
         items[k].rid \notin sn =>
            \E i \in (Len(out) + 1)..Len(result.output) :
                result.output[i].rid = items[k].rid

LEMMA ApplyItemsUpToUnfold ==
    ASSUME NEW S, NEW items \in Seq(S), NEW sn, NEW out
    PROVE  LET f == ApplyItemsUpTo(items, sn, out)
           IN  f = [count \in 0..Len(items) |->
                        IF count = 0
                        THEN [seen |-> sn, output |-> out]
                        ELSE ApplyItem(f[count - 1], items[count])]
<1> DEFINE f == ApplyItemsUpTo(items, sn, out)
           c == [seen |-> sn, output |-> out]
<1>1. Len(items) \in Nat
  OBVIOUS
<1>2. FiniteNatInductiveDefHypothesis(
          f, c, LAMBDA v, i : ApplyItem(v, items[i]), 0, Len(items))
  BY DEF FiniteNatInductiveDefHypothesis, ApplyItemsUpTo
<1>3. FiniteNatInductiveDefConclusion(
          f, c, LAMBDA v, i : ApplyItem(v, items[i]), 0, Len(items))
  <2> HIDE DEF f, c
  <2> QED
    BY <1>1, <1>2, FiniteNatInductiveDef
<1> QED
  BY <1>3 DEF FiniteNatInductiveDefConclusion

(***************************************************************************
PrefixApplied is AppliedCorrectly for the first n entries of the batch:
st is the delivery state after the first n iterations of the process()
loop body. It is inductive in n as it stands.
***************************************************************************)
PrefixApplied(S, items, sn, out, n, st) ==
    /\ st.seen = sn \union {items[k].rid : k \in 1..n}
    /\ st.output \in Seq(S)
    /\ Len(out) <= Len(st.output)
    /\ \A i \in 1..Len(out) : st.output[i] = out[i]
    /\ \A i \in (Len(out) + 1)..Len(st.output) :
         \E k \in 1..n :
            /\ st.output[i] = items[k]
            /\ items[k].rid \notin sn
            /\ \A j \in 1..(k - 1) : items[j].rid # items[k].rid
    /\ \A i, j \in (Len(out) + 1)..Len(st.output) :
         st.output[i].rid = st.output[j].rid => i = j
    /\ \A k \in 1..n :
         items[k].rid \notin sn =>
            \E i \in (Len(out) + 1)..Len(st.output) :
                st.output[i].rid = items[k].rid

LEMMA ApplyItemBase ==
    ASSUME NEW S, NEW items \in Seq(S), NEW sn, NEW out \in Seq(S)
    PROVE  PrefixApplied(S, items, sn, out, 0,
                         [seen |-> sn, output |-> out])
BY DEF PrefixApplied

LEMMA ApplyItemStep ==
    ASSUME ~MutantNoDedup,
           NEW S, NEW items \in Seq(S), NEW sn, NEW out \in Seq(S),
           NEW n \in Nat, n < Len(items),
           NEW st, PrefixApplied(S, items, sn, out, n, st)
    PROVE  PrefixApplied(S, items, sn, out, n + 1,
                         ApplyItem(st, items[n + 1]))
<1> DEFINE item == items[n + 1]
           next == ApplyItem(st, item)
           lo == Len(out)
<1>0. /\ Len(items) \in Nat
      /\ n + 1 \in 1..Len(items)
      /\ item \in S
      /\ lo \in Nat
      /\ Len(st.output) \in Nat
      /\ st.output \in Seq(S)
      /\ lo <= Len(st.output)
  BY DEF PrefixApplied
<1>a. st.seen = sn \union {items[k].rid : k \in 1..n}
  BY DEF PrefixApplied
<1>b. \A i \in 1..lo : st.output[i] = out[i]
  BY DEF PrefixApplied
<1>c. \A i \in (lo + 1)..Len(st.output) :
         \E k \in 1..n :
            /\ st.output[i] = items[k]
            /\ items[k].rid \notin sn
            /\ \A j \in 1..(k - 1) : items[j].rid # items[k].rid
  BY DEF PrefixApplied
<1>d. \A i, j \in (lo + 1)..Len(st.output) :
         st.output[i].rid = st.output[j].rid => i = j
  BY DEF PrefixApplied
<1>e. \A k \in 1..n :
         items[k].rid \notin sn =>
            \E i \in (lo + 1)..Len(st.output) :
                st.output[i].rid = items[k].rid
  BY DEF PrefixApplied
<1>f. \A i \in (lo + 1)..Len(st.output) : st.output[i].rid \in st.seen
  BY <1>a, <1>c
<1>1. CASE item.rid \in st.seen
  <2>1. next.seen = st.seen /\ next.output = st.output
    BY <1>1 DEF ApplyItem
  <2>2. next.seen = sn \union {items[k].rid : k \in 1..(n + 1)}
    <3>1. {items[k].rid : k \in 1..(n + 1)} =
            {items[k].rid : k \in 1..n} \union {item.rid}
      BY <1>0
    <3> QED
      BY <2>1, <1>a, <1>1, <3>1
  <2>3. \A i \in (lo + 1)..Len(next.output) :
          \E k \in 1..(n + 1) :
            /\ next.output[i] = items[k]
            /\ items[k].rid \notin sn
            /\ \A j \in 1..(k - 1) : items[j].rid # items[k].rid
    <3> TAKE i \in (lo + 1)..Len(next.output)
    <3>1. PICK k \in 1..n :
            /\ st.output[i] = items[k]
            /\ items[k].rid \notin sn
            /\ \A j \in 1..(k - 1) : items[j].rid # items[k].rid
      BY <2>1, <1>c
    <3>2. k \in 1..(n + 1)
      BY <1>0
    <3> QED
      BY <3>1, <3>2, <2>1
  <2>4. \A k \in 1..(n + 1) :
          items[k].rid \notin sn =>
            \E i \in (lo + 1)..Len(next.output) :
                next.output[i].rid = items[k].rid
    <3> TAKE k \in 1..(n + 1)
    <3> HAVE items[k].rid \notin sn
    <3>1. PICK k2 \in 1..n : items[k2].rid = items[k].rid
      <4>1. CASE k \in 1..n
        BY <4>1
      <4>2. CASE k = n + 1
        BY <4>2, <1>1, <1>a
      <4> QED
        BY <4>1, <4>2, <1>0
    <3> QED
      BY <3>1, <1>e, <2>1
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <1>0, <1>b, <1>d DEF PrefixApplied
<1>2. CASE item.rid \notin st.seen
  <2>1. /\ next.seen = st.seen \union {item.rid}
        /\ next.output = Append(st.output, item)
    BY <1>2 DEF ApplyItem
  <2> DEFINE ln == Len(st.output)
  <2>2. /\ next.output \in Seq(S)
        /\ Len(next.output) = ln + 1
        /\ \A i \in 1..ln : next.output[i] = st.output[i]
        /\ next.output[ln + 1] = item
    BY <2>1, <1>0
  <2>3. next.seen = sn \union {items[k].rid : k \in 1..(n + 1)}
    <3>1. {items[k].rid : k \in 1..(n + 1)} =
            {items[k].rid : k \in 1..n} \union {item.rid}
      BY <1>0
    <3> QED
      BY <2>1, <1>a, <3>1
  <2>4. item.rid \notin sn /\ \A j \in 1..n : items[j].rid # item.rid
    BY <1>2, <1>a
  <2>5. \A i \in (lo + 1)..Len(next.output) :
          \E k \in 1..(n + 1) :
            /\ next.output[i] = items[k]
            /\ items[k].rid \notin sn
            /\ \A j \in 1..(k - 1) : items[j].rid # items[k].rid
    <3> TAKE i \in (lo + 1)..Len(next.output)
    <3>1. CASE i \in (lo + 1)..ln
      <4>1. PICK k \in 1..n :
              /\ st.output[i] = items[k]
              /\ items[k].rid \notin sn
              /\ \A j \in 1..(k - 1) : items[j].rid # items[k].rid
        BY <3>1, <1>c
      <4>2. k \in 1..(n + 1) /\ next.output[i] = st.output[i]
        BY <3>1, <2>2, <1>0
      <4> QED
        BY <4>1, <4>2
    <3>2. CASE i = ln + 1
      <4>1. n + 1 \in 1..(n + 1) /\ next.output[i] = items[n + 1]
        BY <3>2, <2>2, <1>0
      <4>2. \A j \in 1..((n + 1) - 1) : items[j].rid # items[n + 1].rid
        BY <2>4
      <4> QED
        BY <4>1, <4>2, <2>4
    <3> QED
      BY <3>1, <3>2, <2>2, <1>0
  <2>6. \A i, j \in (lo + 1)..Len(next.output) :
          next.output[i].rid = next.output[j].rid => i = j
    <3> TAKE i, j \in (lo + 1)..Len(next.output)
    <3> HAVE next.output[i].rid = next.output[j].rid
    <3>1. \A m \in (lo + 1)..ln :
            /\ next.output[m] = st.output[m]
            /\ st.output[m].rid \in st.seen
      BY <2>2, <1>f, <1>0
    <3>2. next.output[ln + 1].rid \notin st.seen
      BY <2>2, <1>2
    <3>3. i \in (lo + 1)..(ln + 1) /\ j \in (lo + 1)..(ln + 1)
      BY <2>2
    <3>4. CASE i \in (lo + 1)..ln /\ j \in (lo + 1)..ln
      BY <3>4, <3>1, <1>d
    <3>5. CASE i = ln + 1 /\ j = ln + 1
      BY <3>5
    <3>6. CASE i \in (lo + 1)..ln /\ j = ln + 1
      BY <3>6, <3>1, <3>2
    <3>7. CASE i = ln + 1 /\ j \in (lo + 1)..ln
      BY <3>7, <3>1, <3>2
    <3> QED
      BY <3>3, <3>4, <3>5, <3>6, <3>7, <1>0
  <2>7. \A k \in 1..(n + 1) :
          items[k].rid \notin sn =>
            \E i \in (lo + 1)..Len(next.output) :
                next.output[i].rid = items[k].rid
    <3> TAKE k \in 1..(n + 1)
    <3> HAVE items[k].rid \notin sn
    <3>1. CASE k \in 1..n
      <4>1. PICK i \in (lo + 1)..ln : st.output[i].rid = items[k].rid
        BY <3>1, <1>e
      <4>2. i \in (lo + 1)..Len(next.output) /\ next.output[i] = st.output[i]
        BY <2>2, <1>0
      <4> QED
        BY <4>1, <4>2
    <3>2. CASE k = n + 1
      <4>1. ln + 1 \in (lo + 1)..Len(next.output)
        BY <2>2, <1>0
      <4> QED
        BY <4>1, <2>2, <3>2
    <3> QED
      BY <3>1, <3>2, <1>0
  <2>8. /\ lo <= Len(next.output)
        /\ \A i \in 1..lo : next.output[i] = out[i]
    BY <2>2, <1>0, <1>b
  <2> QED
    BY <2>2, <2>3, <2>5, <2>6, <2>7, <2>8 DEF PrefixApplied
<1> QED
  BY <1>1, <1>2

LEMMA ApplyItemsCorrect ==
    ASSUME ~MutantNoDedup,
           NEW S, NEW items \in Seq(S), NEW sn, NEW out \in Seq(S)
    PROVE  AppliedCorrectly(S, items, sn, out, ApplyItems(items, sn, out))
<1> DEFINE f == ApplyItemsUpTo(items, sn, out)
           Q(n) == n \in 0..Len(items) =>
                       PrefixApplied(S, items, sn, out, n, f[n])
<1>0. Len(items) \in Nat
  OBVIOUS
<1>1. f = [count \in 0..Len(items) |->
              IF count = 0
              THEN [seen |-> sn, output |-> out]
              ELSE ApplyItem(f[count - 1], items[count])]
  BY ApplyItemsUpToUnfold
<1>2. Q(0)
  <2>1. f[0] = [seen |-> sn, output |-> out]
    BY <1>0, <1>1
  <2> QED
    BY <2>1, ApplyItemBase
<1>3. \A n \in Nat : Q(n) => Q(n + 1)
  <2> TAKE n \in Nat
  <2> HAVE Q(n)
  <2> SUFFICES ASSUME n + 1 \in 0..Len(items)
               PROVE  PrefixApplied(S, items, sn, out, n + 1, f[n + 1])
    OBVIOUS
  <2>1. n \in 0..Len(items) /\ n < Len(items)
    BY <1>0
  <2>2. PrefixApplied(S, items, sn, out, n, f[n])
    BY <2>1
  <2>3. f[n + 1] = ApplyItem(f[n], items[n + 1])
    <3> HIDE DEF f
    <3> QED
      BY <1>0, <1>1, <2>1
  <2>4. PrefixApplied(S, items, sn, out, n + 1,
                      ApplyItem(f[n], items[n + 1]))
    <3> HIDE DEF f
    <3> QED
      BY <2>1, <2>2, ApplyItemStep
  <2> QED
    BY <2>3, <2>4
<1>4. \A n \in Nat : Q(n)
  <2> HIDE DEF Q
  <2> QED
    BY <1>2, <1>3, NatInduction
<1>5. PrefixApplied(S, items, sn, out, Len(items), f[Len(items)])
  BY <1>0, <1>4
<1> QED
  BY <1>5 DEF PrefixApplied, AppliedCorrectly, ApplyItems
=============================================================================

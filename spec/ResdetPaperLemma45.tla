------------------------- MODULE ResdetPaperLemma45 -------------------------
(***************************************************************************
TLAPS proofs about ResdetPaper.tla, part 4 of 5.

Lemma 4 (Eventual prefix learning). If index i is agreed, every non-faulty
replica eventually learns every index through i (CG2, CG3(3), L4).

Lemma 5 (Eventual delivery). If a non-faulty replica has learned every
index through i and the entry at i has request id x, the replica has
delivered or eventually delivers a response for x (L4).

Both are proved by induction on a natural number that is a constant of
the proof: the number of indexes learned so far for Lemma 4, and the
processed index for Lemma 5. Each induction step is one use of weak
fairness, of Learn at one index or of Process.
***************************************************************************)
EXTENDS ResdetPaperLive, NaturalsInduction

(***************************************************************************
What one step can do to the agreed log, to the replicas' logs, and to the
processed indexes.
***************************************************************************)
LEMMA StepEffect ==
    LiveState /\ [Next]_vars =>
        /\ \/ agreed' = agreed
           \/ \E e \in Entries : agreed' = Append(agreed, e)
        /\ \/ log' = log
           \/ \E r2 \in Replicas, k2 \in Nat : Learn(r2, k2)
        /\ \/ processed' = processed
           \/ \E r2 \in Replicas : Process(r2)
<1> SUFFICES ASSUME LiveState, [Next]_vars
             PROVE  /\ \/ agreed' = agreed
                       \/ \E e \in Entries : agreed' = Append(agreed, e)
                    /\ \/ log' = log
                       \/ \E r2 \in Replicas, k2 \in Nat : Learn(r2, k2)
                    /\ \/ processed' = processed
                       \/ \E r2 \in Replicas : Process(r2)
  OBVIOUS
<1>1. CASE \E x \in Rids : Submit(x)
  BY <1>1 DEF Submit
<1>2. CASE \E l \in Replicas : Elect(l)
  BY <1>2 DEF Elect
<1>3. CASE \E r \in Replicas : Crash(r)
  BY <1>3 DEF Crash
<1>4. CASE \E x \in Rids : Accept(x)
  BY <1>4 DEF Accept
<1>5. CASE \E l \in Replicas, x \in Rids, y \in Responses : Respond(l, x, y)
  BY <1>5 DEF Respond
<1>6. CASE \E l \in Replicas, e \in Entries : Propose(l, e)
  BY <1>6 DEF Propose
<1>7. CASE \E p \in Proposals : Agree(p)
  <2>1. PICK p \in Proposals : Agree(p)
    BY <1>7
  <2>2. p.entry \in Entries
    BY DEF Proposals
  <2>3. agreed' = Append(agreed, p.entry)
    BY <2>1 DEF Agree
  <2>4. log' = log /\ processed' = processed
    BY <2>1 DEF Agree
  <2> QED
    BY <2>2, <2>3, <2>4
<1>8. CASE \E p \in Proposals : Drop(p)
  BY <1>8 DEF Drop
<1>9. CASE \E r \in Replicas, k \in Nat : Learn(r, k)
  <2>1. agreed' = agreed /\ processed' = processed
    BY <1>9 DEF Learn
  <2> QED
    BY <1>9, <2>1
<1>10. CASE \E r \in Replicas : Process(r)
  <2>1. agreed' = agreed /\ log' = log
    BY <1>10 DEF Process
  <2> QED
    BY <1>10, <2>1
<1>11. CASE UNCHANGED vars
  BY <1>11 DEF vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11
     DEF Next

(* An agreed index stays agreed, with the same entry. *)
LEMMA AgreedIndexStable ==
    ASSUME NEW k \in Nat
    PROVE  LiveState /\ k \in 1..Len(agreed) /\ [Next]_vars
           => (k \in 1..Len(agreed))'
<1> SUFFICES ASSUME LiveState, k \in 1..Len(agreed), [Next]_vars
             PROVE  k \in 1..Len(agreed')
  OBVIOUS
<1>1. agreed \in Seq(Entries)
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. \/ agreed' = agreed
      \/ \E e \in Entries : agreed' = Append(agreed, e)
  BY StepEffect
<1> QED
  BY <1>1, <1>2

LEMMA AgreedAtStable ==
    ASSUME NEW x \in Rids, NEW k \in Nat
    PROVE  LiveState /\ AgreedAt(x, k) /\ [Next]_vars => AgreedAt(x, k)'
<1> SUFFICES ASSUME LiveState, AgreedAt(x, k), [Next]_vars
             PROVE  k \in 1..Len(agreed') /\ agreed'[k].rid = x
  BY DEF AgreedAt
<1>1. agreed \in Seq(Entries)
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. k \in 1..Len(agreed) /\ agreed[k].rid = x
  BY DEF AgreedAt
<1>3. \/ agreed' = agreed
      \/ \E e \in Entries : agreed' = Append(agreed, e)
  BY StepEffect
<1>4. CASE agreed' = agreed
  BY <1>2, <1>4
<1>5. CASE \E e \in Entries : agreed' = Append(agreed, e)
  <2>1. PICK e \in Entries : agreed' = Append(agreed, e)
    BY <1>5
  <2>2. Len(agreed') = Len(agreed) + 1 /\ agreed'[k] = agreed[k]
    BY <1>1, <1>2, <2>1
  <2> QED
    BY <1>1, <1>2, <2>2
<1> QED
  BY <1>3, <1>4, <1>5

(* A replica never forgets a learned index. *)
LEMMA LogDomainStep ==
    ASSUME NEW r \in Replicas
    PROVE  LiveState /\ [Next]_vars
           => \A k \in DOMAIN log[r] : k \in DOMAIN log'[r]
<1> SUFFICES ASSUME LiveState, [Next]_vars,
                    NEW k \in DOMAIN log[r]
             PROVE  k \in DOMAIN log'[r]
  OBVIOUS
<1>1. DOMAIN log = Replicas
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. \/ log' = log
      \/ \E r2 \in Replicas, k2 \in Nat : Learn(r2, k2)
  BY StepEffect
<1>3. CASE log' = log
  BY <1>3
<1>4. CASE \E r2 \in Replicas, k2 \in Nat : Learn(r2, k2)
  <2>1. PICK r2 \in Replicas, k2 \in Nat : Learn(r2, k2)
    BY <1>4
  <2>2. log' = [log EXCEPT ![r2] =
                   [j \in DOMAIN log[r2] \union {k2} |->
                       IF j = k2 THEN agreed[k2] ELSE log[r2][j]]]
    BY <2>1 DEF Learn
  <2>3. CASE r = r2
    <3>1. log'[r] = [j \in DOMAIN log[r2] \union {k2} |->
                        IF j = k2 THEN agreed[k2] ELSE log[r2][j]]
      BY <1>1, <2>2, <2>3
    <3>2. DOMAIN log'[r] = DOMAIN log[r2] \union {k2}
      BY <3>1
    <3> QED
      BY <2>3, <3>2
  <2>4. CASE r # r2
    <3>1. log'[r] = log[r]
      BY <1>1, <2>2, <2>4
    <3> QED
      BY <3>1
  <2> QED
    BY <2>3, <2>4
<1> QED
  BY <1>2, <1>3, <1>4

LEMMA LearnedStable ==
    ASSUME NEW r \in Replicas, NEW k \in Nat
    PROVE  LiveState /\ k \in DOMAIN log[r] /\ [Next]_vars
           => (k \in DOMAIN log[r])'
BY LogDomainStep

LEMMA LearnedThroughStable ==
    ASSUME NEW r \in Replicas, NEW n \in Nat
    PROVE  LiveState /\ LearnedThrough(r, n) /\ [Next]_vars
           => LearnedThrough(r, n)'
<1> SUFFICES ASSUME LiveState, LearnedThrough(r, n), [Next]_vars
             PROVE  \A k \in 1..n : k \in DOMAIN log'[r]
  BY DEF LearnedThrough
<1>1. \A k \in DOMAIN log[r] : k \in DOMAIN log'[r]
  BY LogDomainStep
<1>2. \A k \in 1..n : k \in DOMAIN log[r]
  BY DEF LearnedThrough
<1> QED
  BY <1>1, <1>2

(* A Learn step for index k at r records k. *)
LEMMA LearnStepLearns ==
    ASSUME NEW r \in Replicas, NEW k \in Nat
    PROVE  LiveState /\ <<Learn(r, k)>>_vars => (k \in DOMAIN log[r])'
<1> SUFFICES ASSUME LiveState, Learn(r, k)
             PROVE  k \in DOMAIN log'[r]
  OBVIOUS
<1>1. DOMAIN log = Replicas
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. log' = [log EXCEPT ![r] =
                 [j \in DOMAIN log[r] \union {k} |->
                     IF j = k THEN agreed[k] ELSE log[r][j]]]
  BY DEF Learn
<1>3. log'[r] = [j \in DOMAIN log[r] \union {k} |->
                    IF j = k THEN agreed[k] ELSE log[r][j]]
  BY <1>1, <1>2
<1>4. DOMAIN log'[r] = DOMAIN log[r] \union {k}
  BY <1>3
<1> QED
  BY <1>4

(* The processed index never goes back, and advances one at a time. *)
LEMMA ProcessedStep ==
    ASSUME NEW r \in Replicas
    PROVE  LiveState /\ [Next]_vars
           => \/ processed'[r] = processed[r]
              \/ processed'[r] = processed[r] + 1
<1> SUFFICES ASSUME LiveState, [Next]_vars
             PROVE  \/ processed'[r] = processed[r]
                    \/ processed'[r] = processed[r] + 1
  OBVIOUS
<1>1. processed \in [Replicas -> Nat]
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. \/ processed' = processed
      \/ \E r2 \in Replicas : Process(r2)
  BY StepEffect
<1>3. CASE processed' = processed
  BY <1>3
<1>4. CASE \E r2 \in Replicas : Process(r2)
  <2>1. PICK r2 \in Replicas : Process(r2)
    BY <1>4
  <2>2. processed' = [processed EXCEPT ![r2] = processed[r2] + 1]
    BY <2>1 DEF Process
  <2> QED
    BY <1>1, <2>2
<1> QED
  BY <1>2, <1>3, <1>4

LEMMA ProcessStepAdvances ==
    ASSUME NEW r \in Replicas
    PROVE  LiveState /\ <<Process(r)>>_vars
           => processed'[r] = processed[r] + 1
<1> SUFFICES ASSUME LiveState, Process(r)
             PROVE  processed'[r] = processed[r] + 1
  OBVIOUS
<1>1. processed \in [Replicas -> Nat]
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. processed' = [processed EXCEPT ![r] = processed[r] + 1]
  BY DEF Process
<1> QED
  BY <1>1, <1>2

(***************************************************************************
Lemma 4.

CG3(3) for one index: once index k is agreed, a replica that stays up
learns it, and then has it for good.
***************************************************************************)
LEMMA LearnOne ==
    ASSUME NEW r \in Replicas, NEW k \in Nat
    PROVE  LiveHyp /\ NonFaulty(r)
           => [](k \in 1..Len(agreed) => <>[](k \in DOMAIN log[r]))
<1>1. LiveState /\ k \in 1..Len(agreed) /\ [Next]_vars
      => (k \in 1..Len(agreed))'
  BY AgreedIndexStable
<1>2. LiveState /\ k \in DOMAIN log[r] /\ [Next]_vars
      => (k \in DOMAIN log[r])'
  BY LearnedStable
<1>3. LiveState /\ <<Learn(r, k)>>_vars => (k \in DOMAIN log[r])'
  BY LearnStepLearns
<1>4. LiveState /\ r \in up /\ k \in 1..Len(agreed)
          /\ ~(k \in DOMAIN log[r])
      => ENABLED <<Learn(r, k)>>_vars
  BY EnabledLearn
<1>5. LearnFair => WF_vars(Learn(r, k))
  BY LearnFairAt
<1>6. LiveHyp => WF_vars(Learn(r, k))
  BY <1>5, PTL DEF LiveHyp, Fairness
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>6, PTL DEF LiveHyp, NonFaulty

(* The induction predicate of Lemma 4: once index n is agreed, the replica
   eventually has every index through n, for good. *)
LearnsThrough(r, n) ==
    LiveHyp /\ NonFaulty(r)
    => [](n \in 1..Len(agreed) => <>[]LearnedThrough(r, n))

LEMMA LearnsThroughStep ==
    ASSUME NEW r \in Replicas, NEW n \in Nat
    PROVE  LearnsThrough(r, n) => LearnsThrough(r, n + 1)
<1>1. PICK k \in Nat : k = n + 1
  OBVIOUS
<1>2. LiveHyp /\ NonFaulty(r)
      => [](k \in 1..Len(agreed) => <>[](k \in DOMAIN log[r]))
  BY LearnOne
<1>3. LiveState /\ k \in 1..Len(agreed)
      => n \in 1..Len(agreed) \/ LearnedThrough(r, n)
  <2> SUFFICES ASSUME LiveState, k \in 1..Len(agreed),
                      ~(n \in 1..Len(agreed))
               PROVE  LearnedThrough(r, n)
    OBVIOUS
  <2>1. Len(agreed) \in Nat
    BY DEF LiveState, PaperInv, PaperTypeOK
  <2>2. n = 0
    BY <1>1, <2>1
  <2> QED
    BY <2>2 DEF LearnedThrough
<1>4. LiveState /\ LearnedThrough(r, n) /\ [Next]_vars
      => LearnedThrough(r, n)'
  BY LearnedThroughStable
<1>5. LearnedThrough(r, n) /\ k \in DOMAIN log[r] => LearnedThrough(r, k)
  BY <1>1 DEF LearnedThrough
<1>6. LearnsThrough(r, n) => LearnsThrough(r, k)
  BY <1>2, <1>3, <1>4, <1>5, PTL DEF LearnsThrough, LiveHyp
<1> QED
  BY <1>1, <1>6

LEMMA LearnsThroughAll ==
    ASSUME NEW r \in Replicas
    PROVE  \A n \in Nat : LearnsThrough(r, n)
<1> DEFINE P(n) == LearnsThrough(r, n)
<1>1. P(0)
  <2>1. LiveState => ~(0 \in 1..Len(agreed))
    BY DEF LiveState, PaperInv, PaperTypeOK
  <2> QED
    BY <2>1, PTL DEF LearnsThrough, LiveHyp
<1>2. \A n \in Nat : P(n) => P(n + 1)
  BY LearnsThroughStep
<1> HIDE DEF P
<1>3. \A n \in Nat : P(n)
  BY <1>1, <1>2, NatInduction
<1> QED
  BY <1>3 DEF P

THEOREM Lemma4Core ==
    ASSUME NEW r \in Replicas, NEW i \in Nat
    PROVE  LiveHyp /\ NonFaulty(r)
           => (i \in 1..Len(agreed) ~> LearnedThrough(r, i))
<1>1. LearnsThrough(r, i)
  BY LearnsThroughAll
<1> QED
  BY <1>1, PTL DEF LearnsThrough

THEOREM Lemma4 ==
    ASSUME NEW r \in Replicas, NEW i \in Nat
    PROVE  LiveSpec /\ NonFaulty(r)
           => (i \in 1..Len(agreed) ~> LearnedThrough(r, i))
BY Lemma4Core, LiveSpecHyp, PTL

(***************************************************************************
Lemma 5.

Once a replica has processed index i, and the entry agreed at i has
request id x, the replica has delivered a response for x: either at i, or
earlier, at the index that put x into its deduplication state.
***************************************************************************)
LEMMA DeliveredWhenProcessed ==
    ASSUME NEW r \in Replicas, NEW x \in Rids, NEW i \in Nat
    PROVE  LiveState /\ AgreedAt(x, i) /\ processed[r] >= i
           => Delivers(r, x)
<1> SUFFICES ASSUME LiveState, AgreedAt(x, i), processed[r] >= i
             PROVE  Delivers(r, x)
  OBVIOUS
<1>1. i \in 1..Len(agreed) /\ agreed[i].rid = x
  BY DEF AgreedAt
<1>2. processed[r] \in Nat
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>3. i \in 1..processed[r]
  BY <1>1, <1>2
<1>4. i \in DOMAIN log[r]
  BY <1>3 DEF LiveState, PaperInv, ProcessedLearned
<1>5. log[r][i] = agreed[i]
  BY <1>4 DEF LiveState, PaperInv, LearnedIsAgreed
<1>6. log[r][i].rid \in dset[r]
  BY <1>3 DEF LiveState, PaperInv, DsetIsProcessed
<1>7. x \in dset[r]
  BY <1>1, <1>5, <1>6
<1> QED
  BY <1>7 DEF LiveState, PaperInv, DsetDelivered

(* The induction predicate of Lemma 5: a replica that has learned every
   index through i eventually processes index m, for m up to i. *)
ProcessesTo(r, x, i, m) ==
    m <= i =>
        (LiveHyp /\ NonFaulty(r)
         => []((LearnedThrough(r, i) /\ AgreedAt(x, i))
               => <>(processed[r] >= m)))

LEMMA ProcessesToStep ==
    ASSUME NEW r \in Replicas, NEW x \in Rids, NEW i \in Nat, NEW m \in Nat
    PROVE  ProcessesTo(r, x, i, m) => ProcessesTo(r, x, i, m + 1)
<1> SUFFICES ASSUME m + 1 <= i
             PROVE  ProcessesTo(r, x, i, m)
                    => (LiveHyp /\ NonFaulty(r)
                        => []((LearnedThrough(r, i) /\ AgreedAt(x, i))
                              => <>(processed[r] >= m + 1)))
  BY DEF ProcessesTo
<1>1. ProcessesTo(r, x, i, m)
      => (LiveHyp /\ NonFaulty(r)
          => []((LearnedThrough(r, i) /\ AgreedAt(x, i))
                => <>(processed[r] >= m)))
  <2>1. m <= i
    OBVIOUS
  <2> QED
    BY <2>1 DEF ProcessesTo
<1>2. LiveState /\ LearnedThrough(r, i) /\ [Next]_vars
      => LearnedThrough(r, i)'
  BY LearnedThroughStable
<1>3. LiveState /\ AgreedAt(x, i) /\ [Next]_vars => AgreedAt(x, i)'
  BY AgreedAtStable
<1>4. /\ LiveState /\ processed[r] >= m /\ [Next]_vars
         => (processed[r] >= m)'
      /\ LiveState /\ processed[r] >= m + 1 /\ [Next]_vars
         => (processed[r] >= m + 1)'
  <2>1. LiveState => processed[r] \in Nat
    BY DEF LiveState, PaperInv, PaperTypeOK
  <2>2. LiveState /\ [Next]_vars
        => \/ processed'[r] = processed[r]
           \/ processed'[r] = processed[r] + 1
    BY ProcessedStep
  <2> QED
    BY <2>1, <2>2
<1>5. LiveState /\ processed[r] >= m /\ ~(processed[r] >= m + 1)
          /\ <<Process(r)>>_vars
      => (processed[r] >= m + 1)'
  <2>1. LiveState => processed[r] \in Nat
    BY DEF LiveState, PaperInv, PaperTypeOK
  <2>2. LiveState /\ <<Process(r)>>_vars
        => processed'[r] = processed[r] + 1
    BY ProcessStepAdvances
  <2> QED
    BY <2>1, <2>2
<1>6. LiveState /\ r \in up /\ LearnedThrough(r, i)
          /\ processed[r] >= m /\ ~(processed[r] >= m + 1)
      => ENABLED <<Process(r)>>_vars
  <2> SUFFICES ASSUME LiveState, r \in up, LearnedThrough(r, i),
                      processed[r] >= m, ~(processed[r] >= m + 1)
               PROVE  ENABLED <<Process(r)>>_vars
    OBVIOUS
  <2>1. processed[r] \in Nat
    BY DEF LiveState, PaperInv, PaperTypeOK
  <2>2. processed[r] + 1 \in 1..i
    BY <2>1
  <2>3. processed[r] + 1 \in DOMAIN log[r]
    BY <2>2 DEF LearnedThrough
  <2> QED
    BY <2>3, EnabledProcess
<1>7. ProcessFair => WF_vars(Process(r))
  BY ProcessFairAt
<1>8. LiveHyp => WF_vars(Process(r))
  BY <1>7, PTL DEF LiveHyp, Fairness
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>8, PTL DEF LiveHyp, NonFaulty

LEMMA ProcessesToAll ==
    ASSUME NEW r \in Replicas, NEW x \in Rids, NEW i \in Nat
    PROVE  \A m \in Nat : ProcessesTo(r, x, i, m)
<1> DEFINE P(m) == ProcessesTo(r, x, i, m)
<1>1. P(0)
  <2>1. LiveState => processed[r] >= 0
    BY DEF LiveState, PaperInv, PaperTypeOK
  <2> QED
    BY <2>1, PTL DEF ProcessesTo, LiveHyp
<1>2. \A m \in Nat : P(m) => P(m + 1)
  BY ProcessesToStep
<1> HIDE DEF P
<1>3. \A m \in Nat : P(m)
  BY <1>1, <1>2, NatInduction
<1> QED
  BY <1>3 DEF P

THEOREM Lemma5Core ==
    ASSUME NEW r \in Replicas, NEW x \in Rids, NEW i \in Nat
    PROVE  LiveHyp /\ NonFaulty(r)
           => ((LearnedThrough(r, i) /\ AgreedAt(x, i)) ~> Delivers(r, x))
<1>1. ProcessesTo(r, x, i, i)
  BY ProcessesToAll
<1>2. LiveHyp /\ NonFaulty(r)
      => []((LearnedThrough(r, i) /\ AgreedAt(x, i))
            => <>(processed[r] >= i))
  <2>1. i <= i
    OBVIOUS
  <2> QED
    BY <1>1, <2>1 DEF ProcessesTo
<1>3. LiveState /\ AgreedAt(x, i) /\ [Next]_vars => AgreedAt(x, i)'
  BY AgreedAtStable
<1>4. LiveState /\ AgreedAt(x, i) /\ processed[r] >= i => Delivers(r, x)
  BY DeliveredWhenProcessed
<1> QED
  BY <1>2, <1>3, <1>4, PTL DEF LiveHyp

THEOREM Lemma5 ==
    ASSUME NEW r \in Replicas, NEW x \in Rids, NEW i \in Nat
    PROVE  LiveSpec /\ NonFaulty(r)
           => ((LearnedThrough(r, i) /\ AgreedAt(x, i)) ~> Delivers(r, x))
BY Lemma5Core, LiveSpecHyp, PTL
=============================================================================

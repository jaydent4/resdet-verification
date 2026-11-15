------------------------- MODULE ResdetPaperSafety -------------------------
(***************************************************************************
TLAPS proofs about ResdetPaper.tla, part 1 of 5: the paper's safety
results, as the paper states them.

  Lemma 1    Two replicas that have both processed index i processed the
             same entry there.
  Lemma 2    A replica that has processed index i has processed every
             index through i, one at a time.
  Theorem 1  If two replicas deliver responses for the same request id,
             the responses are equal.

PaperInv is the inductive invariant behind them. Its conjuncts are also
what the liveness modules know about a reachable state.
***************************************************************************)
EXTENDS ResdetPaper, TLAPS

PaperTypeOK ==
    /\ up \subseteq Replicas
    /\ leader \in Replicas \union {NoLeader}
    /\ submitted \subseteq Rids
    /\ accepted \in [Replicas -> SUBSET Rids]
    /\ calling \in [Replicas -> SUBSET Rids]
    /\ ready \in [Replicas -> SUBSET Entries]
    /\ pending \subseteq Proposals
    /\ agreed \in Seq(Entries)
    /\ DOMAIN log = Replicas
    /\ processed \in [Replicas -> Nat]
    /\ done \in [Replicas -> SUBSET Nat]
    /\ dset \in [Replicas -> SUBSET Rids]
    /\ delivered \in [Replicas -> Seq(Entries)]

(* The leader, if there is one, has not crashed. *)
LeaderUp == leader # NoLeader => leader \in up

(* CG1 and CG2 as they hold of the consensus box: what a replica has
   learned at an index is the entry agreed at that index. *)
LearnedIsAgreed ==
    \A r \in Replicas :
        \A k \in DOMAIN log[r] :
            k \in 1..Len(agreed) /\ log[r][k] = agreed[k]

(* The delivery-deduplication state is exactly the request ids of the
   indexes processed so far. *)
DsetIsProcessed ==
    \A r \in Replicas :
        /\ \A x \in dset[r] :
             \E j \in 1..processed[r] : log[r][j].rid = x
        /\ \A j \in 1..processed[r] : log[r][j].rid \in dset[r]

(* First-commit-wins: every delivered response is the first agreed entry
   for its request id, at an index the replica has processed. *)
DeliveredFirst ==
    \A r \in Replicas :
        \A i \in 1..Len(delivered[r]) :
            \E j \in 1..processed[r] :
                /\ delivered[r][i] = agreed[j]
                /\ \A j2 \in 1..(j - 1) : agreed[j2].rid # agreed[j].rid

(* Every recorded request id has a delivered response, and conversely. *)
DsetDelivered ==
    \A r \in Replicas :
        /\ \A x \in dset[r] : Delivers(r, x)
        /\ \A i \in 1..Len(delivered[r]) : delivered[r][i].rid \in dset[r]

(* The indexes a replica has processed are exactly those up to its
   processed counter. This is where the induction behind Lemma 2 lives:
   the counter only advances by one, and each advance records its index. *)
DoneIsProcessed == \A r \in Replicas : done[r] = 1..processed[r]

PaperInv ==
    /\ PaperTypeOK
    /\ LeaderUp
    /\ LearnedIsAgreed
    /\ ProcessedLearned
    /\ DoneIsProcessed
    /\ DsetIsProcessed
    /\ DeliveredFirst
    /\ DsetDelivered
    /\ DeliveredOnce

(***************************************************************************
The invariant holds initially.
***************************************************************************)
LEMMA PaperInit == Init => PaperInv
<1> SUFFICES ASSUME Init PROVE PaperInv
  OBVIOUS
<1>1. PaperTypeOK
  BY DEF Init, PaperTypeOK
<1>2. LeaderUp
  BY DEF Init, LeaderUp
<1>3. LearnedIsAgreed
  BY DEF Init, LearnedIsAgreed
<1>4. ProcessedLearned
  BY DEF Init, ProcessedLearned
<1>5. DsetIsProcessed
  BY DEF Init, DsetIsProcessed
<1>6. DeliveredFirst
  BY DEF Init, DeliveredFirst
<1>7. DsetDelivered
  BY DEF Init, DsetDelivered, Delivers
<1>8. DeliveredOnce
  BY DEF Init, DeliveredOnce
<1>9. DoneIsProcessed
  BY DEF Init, DoneIsProcessed
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF PaperInv

(***************************************************************************
The conjuncts about learning, processing and delivery read only these
variables, so a step that leaves them alone preserves those conjuncts.
***************************************************************************)
DeliveryVars == <<agreed, log, processed, done, dset, delivered>>

LEMMA DeliveryFrame ==
    ASSUME PaperInv, UNCHANGED DeliveryVars
    PROVE  /\ LearnedIsAgreed'
           /\ ProcessedLearned'
           /\ DoneIsProcessed'
           /\ DsetIsProcessed'
           /\ DeliveredFirst'
           /\ DsetDelivered'
           /\ DeliveredOnce'
BY DEF DeliveryVars, PaperInv, LearnedIsAgreed, ProcessedLearned,
       DoneIsProcessed, DsetIsProcessed, DeliveredFirst, DsetDelivered,
       DeliveredOnce, Delivers

LEMMA PaperFrame ==
    ASSUME PaperInv, UNCHANGED DeliveryVars, PaperTypeOK', LeaderUp'
    PROVE  PaperInv'
BY DeliveryFrame DEF PaperInv

(***************************************************************************
Consensus agrees one more entry. Indexes already agreed keep their
entries, and everything the invariant says about the log is about indexes
that some replica has learned.
***************************************************************************)
LEMMA PaperAgree ==
    ASSUME PaperInv, NEW p \in Proposals, Agree(p)
    PROVE  PaperInv'
<1>0. /\ PaperTypeOK
      /\ LeaderUp
      /\ LearnedIsAgreed
      /\ ProcessedLearned
      /\ DoneIsProcessed
      /\ DsetIsProcessed
      /\ DeliveredFirst
      /\ DsetDelivered
      /\ DeliveredOnce
  BY DEF PaperInv
<1>1. /\ agreed' = Append(agreed, p.entry)
      /\ pending' = pending \ {p}
      /\ UNCHANGED <<up, leader, submitted, accepted, calling, ready, log,
                     processed, done, dset, delivered>>
  BY DEF Agree
<1>2. /\ agreed \in Seq(Entries)
      /\ p.entry \in Entries
      /\ Len(agreed) \in Nat
  BY <1>0 DEF PaperTypeOK, Proposals
<1>3. /\ agreed' \in Seq(Entries)
      /\ Len(agreed') = Len(agreed) + 1
      /\ \A k \in 1..Len(agreed) : agreed'[k] = agreed[k]
  BY <1>1, <1>2
<1>4. PaperTypeOK'
  BY <1>0, <1>1, <1>3 DEF PaperTypeOK
<1>5. LeaderUp'
  BY <1>0, <1>1 DEF LeaderUp
<1>6. LearnedIsAgreed'
  <2> SUFFICES ASSUME NEW r \in Replicas, NEW k \in DOMAIN log[r]
               PROVE  k \in 1..Len(agreed') /\ log[r][k] = agreed'[k]
    BY <1>1 DEF LearnedIsAgreed
  <2>1. k \in 1..Len(agreed) /\ log[r][k] = agreed[k]
    BY <1>0 DEF LearnedIsAgreed
  <2> QED
    BY <2>1, <1>2, <1>3
<1>7. ProcessedLearned'
  BY <1>0, <1>1 DEF ProcessedLearned
<1>8. DsetIsProcessed'
  BY <1>0, <1>1 DEF DsetIsProcessed
<1>9. DeliveredFirst'
  <2> SUFFICES ASSUME NEW r \in Replicas,
                      NEW i \in 1..Len(delivered[r])
               PROVE  \E j \in 1..processed[r] :
                          /\ delivered[r][i] = agreed'[j]
                          /\ \A j2 \in 1..(j - 1) :
                                 agreed'[j2].rid # agreed'[j].rid
    BY <1>1 DEF DeliveredFirst
  <2>1. PICK j \in 1..processed[r] :
            /\ delivered[r][i] = agreed[j]
            /\ \A j2 \in 1..(j - 1) : agreed[j2].rid # agreed[j].rid
    BY <1>0 DEF DeliveredFirst
  <2>2. j \in 1..Len(agreed)
    BY <1>0 DEF ProcessedLearned, LearnedIsAgreed
  <2>3. \A j2 \in 1..(j - 1) : j2 \in 1..Len(agreed)
    BY <2>2, <1>2
  <2>4. agreed'[j] = agreed[j]
    BY <2>2, <1>3
  <2>5. \A j2 \in 1..(j - 1) : agreed'[j2] = agreed[j2]
    BY <2>3, <1>3
  <2> QED
    BY <2>1, <2>4, <2>5
<1>10. DsetDelivered'
  BY <1>0, <1>1 DEF DsetDelivered, Delivers
<1>11. DeliveredOnce'
  BY <1>0, <1>1 DEF DeliveredOnce
<1>12. DoneIsProcessed'
  BY <1>0, <1>1 DEF DoneIsProcessed
<1> QED
  BY <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12 DEF PaperInv

(***************************************************************************
A replica learns one more index. Its log gains that index, with the
agreed entry, and keeps every entry it had.
***************************************************************************)
LEMMA PaperLearn ==
    ASSUME PaperInv, NEW r0 \in Replicas, NEW k \in Nat, Learn(r0, k)
    PROVE  PaperInv'
<1>0. /\ PaperTypeOK
      /\ LeaderUp
      /\ LearnedIsAgreed
      /\ ProcessedLearned
      /\ DoneIsProcessed
      /\ DsetIsProcessed
      /\ DeliveredFirst
      /\ DsetDelivered
      /\ DeliveredOnce
  BY DEF PaperInv
<1>1. /\ k \in 1..Len(agreed)
      /\ k \notin DOMAIN log[r0]
      /\ log' = [log EXCEPT ![r0] =
                    [i \in DOMAIN log[r0] \union {k} |->
                        IF i = k THEN agreed[k] ELSE log[r0][i]]]
      /\ UNCHANGED <<up, leader, submitted, accepted, calling, ready,
                     pending, agreed, processed, done, dset, delivered>>
  BY DEF Learn
<1>2. DOMAIN log = Replicas
  BY <1>0 DEF PaperTypeOK
<1>3. /\ DOMAIN log' = Replicas
      /\ \A t \in Replicas : t # r0 => log'[t] = log[t]
      /\ log'[r0] = [i \in DOMAIN log[r0] \union {k} |->
                        IF i = k THEN agreed[k] ELSE log[r0][i]]
  BY <1>1, <1>2
<1>4. /\ DOMAIN log'[r0] = DOMAIN log[r0] \union {k}
      /\ log'[r0][k] = agreed[k]
      /\ \A i \in DOMAIN log[r0] : log'[r0][i] = log[r0][i]
  BY <1>1, <1>3
<1>5. PaperTypeOK'
  BY <1>0, <1>1, <1>3 DEF PaperTypeOK
<1>6. LeaderUp'
  BY <1>0, <1>1 DEF LeaderUp
<1>7. LearnedIsAgreed'
  <2> SUFFICES ASSUME NEW r \in Replicas, NEW kk \in DOMAIN log'[r]
               PROVE  kk \in 1..Len(agreed) /\ log'[r][kk] = agreed[kk]
    BY <1>1 DEF LearnedIsAgreed
  <2>1. CASE r # r0
    BY <2>1, <1>3, <1>0 DEF LearnedIsAgreed
  <2>2. CASE r = r0 /\ kk = k
    BY <2>2, <1>1, <1>4
  <2>3. CASE r = r0 /\ kk # k
    <3>1. kk \in DOMAIN log[r0]
      BY <2>3, <1>4
    <3>2. log'[r][kk] = log[r0][kk]
      BY <2>3, <3>1, <1>4
    <3> QED
      BY <2>3, <3>1, <3>2, <1>0 DEF LearnedIsAgreed
  <2> QED
    BY <2>1, <2>2, <2>3
<1>8. \A r \in Replicas :
          \A j \in 1..processed[r] :
              j \in DOMAIN log'[r] /\ log'[r][j] = log[r][j]
  <2> SUFFICES ASSUME NEW r \in Replicas, NEW j \in 1..processed[r]
               PROVE  j \in DOMAIN log'[r] /\ log'[r][j] = log[r][j]
    OBVIOUS
  <2>1. j \in DOMAIN log[r]
    BY <1>0 DEF ProcessedLearned
  <2>2. CASE r # r0
    BY <2>1, <2>2, <1>3
  <2>3. CASE r = r0
    BY <2>1, <2>3, <1>4
  <2> QED
    BY <2>2, <2>3
<1>9. ProcessedLearned'
  BY <1>8, <1>1 DEF ProcessedLearned
<1>10. DsetIsProcessed'
  <2> SUFFICES ASSUME NEW r \in Replicas
               PROVE  /\ \A x \in dset[r] :
                           \E j \in 1..processed[r] : log'[r][j].rid = x
                      /\ \A j \in 1..processed[r] :
                           log'[r][j].rid \in dset[r]
    BY <1>1 DEF DsetIsProcessed
  <2>1. /\ \A x \in dset[r] :
             \E j \in 1..processed[r] : log[r][j].rid = x
        /\ \A j \in 1..processed[r] : log[r][j].rid \in dset[r]
    BY <1>0 DEF DsetIsProcessed
  <2>2. \A j \in 1..processed[r] : log'[r][j] = log[r][j]
    BY <1>8
  <2> QED
    BY <2>1, <2>2
<1>11. DeliveredFirst'
  BY <1>0, <1>1 DEF DeliveredFirst
<1>12. DsetDelivered'
  BY <1>0, <1>1 DEF DsetDelivered, Delivers
<1>13. DeliveredOnce'
  BY <1>0, <1>1 DEF DeliveredOnce
<1>14. DoneIsProcessed'
  BY <1>0, <1>1 DEF DoneIsProcessed
<1> QED
  BY <1>5, <1>6, <1>7, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14
     DEF PaperInv

(***************************************************************************
A replica processes its next index. The entry there is the agreed entry.
If its request id is not yet recorded, then no earlier agreed index has
that id, because every earlier index was processed and so recorded: the
entry is the first one agreed for its id, and it is delivered.
***************************************************************************)
LEMMA PaperProcess ==
    ASSUME PaperInv, NEW r0 \in Replicas, Process(r0)
    PROVE  PaperInv'
<1> DEFINE next == processed[r0] + 1
           entry == log[r0][next]
           old == delivered[r0]
           n == Len(old)
<1>0. /\ PaperTypeOK
      /\ LeaderUp
      /\ LearnedIsAgreed
      /\ ProcessedLearned
      /\ DoneIsProcessed
      /\ DsetIsProcessed
      /\ DeliveredFirst
      /\ DsetDelivered
      /\ DeliveredOnce
  BY DEF PaperInv
<1>1. /\ next \in DOMAIN log[r0]
      /\ processed' = [processed EXCEPT ![r0] = next]
      /\ done' = [done EXCEPT ![r0] = done[r0] \union {next}]
      /\ UNCHANGED <<up, leader, submitted, accepted, calling, ready,
                     pending, agreed, log>>
      /\ \/ /\ entry.rid \in dset[r0]
            /\ UNCHANGED <<dset, delivered>>
         \/ /\ entry.rid \notin dset[r0]
            /\ dset' = [dset EXCEPT ![r0] = dset[r0] \union {entry.rid}]
            /\ delivered' = [delivered EXCEPT ![r0] = Append(old, entry)]
  BY DEF Process
<1>2. /\ processed \in [Replicas -> Nat]
      /\ processed[r0] \in Nat
      /\ next \in Nat
      /\ next = processed[r0] + 1
      /\ Len(agreed) \in Nat
  BY <1>0 DEF PaperTypeOK
<1>3. /\ next \in 1..Len(agreed)
      /\ entry = agreed[next]
      /\ entry \in Entries
      /\ entry.rid \in Rids
  <2>1. next \in 1..Len(agreed) /\ entry = agreed[next]
    BY <1>0, <1>1 DEF LearnedIsAgreed
  <2>2. agreed[next] \in Entries
    BY <2>1, <1>0 DEF PaperTypeOK
  <2> QED
    BY <2>1, <2>2 DEF Entries
<1>4. /\ processed' \in [Replicas -> Nat]
      /\ processed'[r0] = next
      /\ \A t \in Replicas : t # r0 => processed'[t] = processed[t]
  BY <1>1, <1>2
<1>11. /\ done \in [Replicas -> SUBSET Nat]
       /\ done' \in [Replicas -> SUBSET Nat]
       /\ done'[r0] = done[r0] \union {next}
       /\ \A t \in Replicas : t # r0 => done'[t] = done[t]
  BY <1>0, <1>1, <1>2 DEF PaperTypeOK
<1>5. \A j \in 1..processed[r0] :
          /\ j \in DOMAIN log[r0]
          /\ log[r0][j] = agreed[j]
          /\ log[r0][j].rid \in dset[r0]
  BY <1>0 DEF ProcessedLearned, LearnedIsAgreed, DsetIsProcessed
<1>6. /\ old \in Seq(Entries)
      /\ n \in Nat
      /\ dset[r0] \in SUBSET Rids
      /\ delivered \in [Replicas -> Seq(Entries)]
      /\ dset \in [Replicas -> SUBSET Rids]
  BY <1>0 DEF PaperTypeOK
<1> HIDE DEF next, entry, old, n
<1>7. LeaderUp'
  BY <1>0, <1>1 DEF LeaderUp
<1>8. LearnedIsAgreed'
  BY <1>0, <1>1 DEF LearnedIsAgreed
<1>9. ProcessedLearned'
  <2> SUFFICES ASSUME NEW r \in Replicas, NEW j \in 1..processed'[r]
               PROVE  j \in DOMAIN log[r]
    BY <1>1 DEF ProcessedLearned
  <2>1. CASE r # r0
    BY <2>1, <1>4, <1>0 DEF ProcessedLearned
  <2>2. CASE r = r0
    <3>1. j \in 1..processed[r0] \/ j = next
      BY <2>2, <1>4, <1>2
    <3> QED
      BY <3>1, <2>2, <1>5, <1>1
  <2> QED
    BY <2>1, <2>2
<1>10. \A r \in Replicas :
           \A j \in 1..processed[r] : j \in 1..processed'[r]
  <2> SUFFICES ASSUME NEW r \in Replicas, NEW j \in 1..processed[r]
               PROVE  j \in 1..processed'[r]
    OBVIOUS
  <2>1. CASE r # r0
    BY <2>1, <1>4
  <2>2. CASE r = r0
    BY <2>2, <1>4, <1>2
  <2> QED
    BY <2>1, <2>2
<1>12. DoneIsProcessed'
  <2> SUFFICES ASSUME NEW r \in Replicas
               PROVE  done'[r] = 1..processed'[r]
    BY DEF DoneIsProcessed
  <2>1. done[r] = 1..processed[r]
    BY <1>0 DEF DoneIsProcessed
  <2>2. CASE r # r0
    BY <2>1, <2>2, <1>4, <1>11
  <2>3. CASE r = r0
    <3>1. done'[r] = (1..processed[r0]) \union {next}
      BY <2>1, <2>3, <1>11
    <3>2. processed'[r] = next
      BY <2>3, <1>4
    <3>3. (1..processed[r0]) \union {next} = 1..next
      BY <1>2
    <3> QED
      BY <3>1, <3>2, <3>3
  <2> QED
    BY <2>2, <2>3
<1>A. CASE entry.rid \in dset[r0] /\ UNCHANGED <<dset, delivered>>
  <2>1. PaperTypeOK'
    BY <1>A, <1>0, <1>1, <1>4, <1>11 DEF PaperTypeOK
  <2>2. DsetIsProcessed'
    <3> SUFFICES ASSUME NEW r \in Replicas
                 PROVE  /\ \A x \in dset[r] :
                             \E j \in 1..processed'[r] : log[r][j].rid = x
                        /\ \A j \in 1..processed'[r] :
                             log[r][j].rid \in dset[r]
      BY <1>A, <1>1 DEF DsetIsProcessed
    <3>1. /\ \A x \in dset[r] :
               \E j \in 1..processed[r] : log[r][j].rid = x
          /\ \A j \in 1..processed[r] : log[r][j].rid \in dset[r]
      BY <1>0 DEF DsetIsProcessed
    <3>2. \A x \in dset[r] :
              \E j \in 1..processed'[r] : log[r][j].rid = x
      BY <3>1, <1>10
    <3>3. \A j \in 1..processed'[r] : log[r][j].rid \in dset[r]
      <4> SUFFICES ASSUME NEW j \in 1..processed'[r]
                   PROVE  log[r][j].rid \in dset[r]
        OBVIOUS
      <4>1. CASE r # r0
        BY <4>1, <1>4, <3>1
      <4>2. CASE r = r0
        <5>1. j \in 1..processed[r0] \/ j = next
          BY <4>2, <1>4, <1>2
        <5>2. CASE j \in 1..processed[r0]
          BY <5>2, <4>2, <1>5
        <5>3. CASE j = next
          BY <5>3, <4>2, <1>A DEF entry
        <5> QED
          BY <5>1, <5>2, <5>3
      <4> QED
        BY <4>1, <4>2
    <3> QED
      BY <3>2, <3>3
  <2>3. DeliveredFirst'
    <3> SUFFICES ASSUME NEW r \in Replicas,
                        NEW i \in 1..Len(delivered[r])
                 PROVE  \E j \in 1..processed'[r] :
                            /\ delivered[r][i] = agreed[j]
                            /\ \A j2 \in 1..(j - 1) :
                                   agreed[j2].rid # agreed[j].rid
      BY <1>A, <1>1 DEF DeliveredFirst
    <3>1. PICK j \in 1..processed[r] :
              /\ delivered[r][i] = agreed[j]
              /\ \A j2 \in 1..(j - 1) : agreed[j2].rid # agreed[j].rid
      BY <1>0 DEF DeliveredFirst
    <3>2. j \in 1..processed'[r]
      BY <1>10
    <3> QED
      BY <3>1, <3>2
  <2>4. DsetDelivered'
    BY <1>A, <1>0 DEF DsetDelivered, Delivers
  <2>5. DeliveredOnce'
    BY <1>A, <1>0 DEF DeliveredOnce
  <2> QED
    BY <2>1, <1>7, <1>8, <1>9, <1>12, <2>2, <2>3, <2>4, <2>5 DEF PaperInv
<1>B. CASE /\ entry.rid \notin dset[r0]
           /\ dset' = [dset EXCEPT ![r0] = dset[r0] \union {entry.rid}]
           /\ delivered' = [delivered EXCEPT ![r0] = Append(old, entry)]
  <2>1. /\ dset' \in [Replicas -> SUBSET Rids]
        /\ dset'[r0] = dset[r0] \union {entry.rid}
        /\ \A t \in Replicas : t # r0 => dset'[t] = dset[t]
    BY <1>B, <1>6, <1>3
  <2>2. /\ Append(old, entry) \in Seq(Entries)
        /\ Len(Append(old, entry)) = n + 1
        /\ \A i \in 1..n : Append(old, entry)[i] = old[i]
        /\ Append(old, entry)[n + 1] = entry
    BY <1>6, <1>3 DEF n
  <2>3. /\ delivered' \in [Replicas -> Seq(Entries)]
        /\ delivered'[r0] = Append(old, entry)
        /\ \A t \in Replicas : t # r0 => delivered'[t] = delivered[t]
    BY <1>B, <1>6, <2>2
  <2>4. /\ Len(delivered'[r0]) = n + 1
        /\ \A i \in 1..n : delivered'[r0][i] = delivered[r0][i]
        /\ delivered'[r0][n + 1] = entry
        /\ Len(delivered[r0]) = n
    BY <2>2, <2>3 DEF old, n
  <2>5. PaperTypeOK'
    BY <1>0, <1>1, <1>4, <1>11, <2>1, <2>3 DEF PaperTypeOK
  <2>6. DsetIsProcessed'
    <3> SUFFICES ASSUME NEW r \in Replicas
                 PROVE  /\ \A x \in dset'[r] :
                             \E j \in 1..processed'[r] : log[r][j].rid = x
                        /\ \A j \in 1..processed'[r] :
                             log[r][j].rid \in dset'[r]
      BY <1>1 DEF DsetIsProcessed
    <3>1. /\ \A x \in dset[r] :
               \E j \in 1..processed[r] : log[r][j].rid = x
          /\ \A j \in 1..processed[r] : log[r][j].rid \in dset[r]
      BY <1>0 DEF DsetIsProcessed
    <3>2. CASE r # r0
      BY <3>2, <3>1, <1>4, <2>1
    <3>3. CASE r = r0
      <4>1. \A x \in dset'[r] :
                \E j \in 1..processed'[r] : log[r][j].rid = x
        <5> SUFFICES ASSUME NEW x \in dset'[r]
                     PROVE  \E j \in 1..processed'[r] : log[r][j].rid = x
          OBVIOUS
        <5>1. x \in dset[r0] \/ x = entry.rid
          BY <3>3, <2>1
        <5>2. CASE x \in dset[r0]
          BY <5>2, <3>3, <3>1, <1>10
        <5>3. CASE x = entry.rid
          <6>1. next \in 1..processed'[r]
            BY <3>3, <1>4, <1>2
          <6>2. log[r][next].rid = x
            BY <5>3, <3>3 DEF entry
          <6> QED
            BY <6>1, <6>2
        <5> QED
          BY <5>1, <5>2, <5>3
      <4>2. \A j \in 1..processed'[r] : log[r][j].rid \in dset'[r]
        <5> SUFFICES ASSUME NEW j \in 1..processed'[r]
                     PROVE  log[r][j].rid \in dset'[r]
          OBVIOUS
        <5>1. j \in 1..processed[r0] \/ j = next
          BY <3>3, <1>4, <1>2
        <5>2. CASE j \in 1..processed[r0]
          BY <5>2, <3>3, <1>5, <2>1
        <5>3. CASE j = next
          BY <5>3, <3>3, <2>1 DEF entry
        <5> QED
          BY <5>1, <5>2, <5>3
      <4> QED
        BY <4>1, <4>2
    <3> QED
      BY <3>2, <3>3
  <2>7. DeliveredFirst'
    <3> SUFFICES ASSUME NEW r \in Replicas,
                        NEW i \in 1..Len(delivered'[r])
                 PROVE  \E j \in 1..processed'[r] :
                            /\ delivered'[r][i] = agreed[j]
                            /\ \A j2 \in 1..(j - 1) :
                                   agreed[j2].rid # agreed[j].rid
      BY <1>1 DEF DeliveredFirst
    <3>1. CASE r # r0
      <4>1. delivered'[r] = delivered[r]
        BY <3>1, <2>3
      <4>2. PICK j \in 1..processed[r] :
                /\ delivered[r][i] = agreed[j]
                /\ \A j2 \in 1..(j - 1) : agreed[j2].rid # agreed[j].rid
        BY <4>1, <1>0 DEF DeliveredFirst
      <4>3. j \in 1..processed'[r]
        BY <1>10
      <4> QED
        BY <4>1, <4>2, <4>3
    <3>2. CASE r = r0 /\ i \in 1..n
      <4>1. delivered'[r][i] = delivered[r0][i]
        BY <3>2, <2>4
      <4>2. i \in 1..Len(delivered[r0])
        BY <3>2, <2>4
      <4>3. PICK j \in 1..processed[r0] :
                /\ delivered[r0][i] = agreed[j]
                /\ \A j2 \in 1..(j - 1) : agreed[j2].rid # agreed[j].rid
        BY <4>2, <1>0 DEF DeliveredFirst
      <4>4. j \in 1..processed'[r]
        BY <3>2, <1>10
      <4> QED
        BY <4>1, <4>3, <4>4
    <3>3. CASE r = r0 /\ i = n + 1
      <4>1. delivered'[r][i] = agreed[next]
        BY <3>3, <2>4, <1>3
      <4>2. next \in 1..processed'[r]
        BY <3>3, <1>4, <1>2
      <4>3. \A j2 \in 1..(next - 1) : agreed[j2].rid # agreed[next].rid
        <5> SUFFICES ASSUME NEW j2 \in 1..(next - 1)
                     PROVE  agreed[j2].rid # agreed[next].rid
          OBVIOUS
        <5>1. j2 \in 1..processed[r0]
          BY <1>2
        <5>2. agreed[j2].rid \in dset[r0]
          BY <5>1, <1>5
        <5>3. agreed[next].rid \notin dset[r0]
          BY <1>B, <1>3
        <5> QED
          BY <5>2, <5>3
      <4> QED
        BY <4>1, <4>2, <4>3
    <3>4. r = r0 => i \in 1..n \/ i = n + 1
      BY <2>4, <1>6
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4
  <2>8. DsetDelivered'
    <3> SUFFICES ASSUME NEW r \in Replicas
                 PROVE  /\ \A x \in dset'[r] :
                             \E i \in 1..Len(delivered'[r]) :
                                 delivered'[r][i].rid = x
                        /\ \A i \in 1..Len(delivered'[r]) :
                             delivered'[r][i].rid \in dset'[r]
      BY DEF DsetDelivered, Delivers
    <3>1. /\ \A x \in dset[r] :
               \E i \in 1..Len(delivered[r]) : delivered[r][i].rid = x
          /\ \A i \in 1..Len(delivered[r]) : delivered[r][i].rid \in dset[r]
      BY <1>0 DEF DsetDelivered, Delivers
    <3>2. CASE r # r0
      BY <3>2, <3>1, <2>1, <2>3
    <3>3. CASE r = r0
      <4>1. \A x \in dset'[r] :
                \E i \in 1..Len(delivered'[r]) : delivered'[r][i].rid = x
        <5> SUFFICES ASSUME NEW x \in dset'[r]
                     PROVE  \E i \in 1..Len(delivered'[r]) :
                                delivered'[r][i].rid = x
          OBVIOUS
        <5>1. x \in dset[r0] \/ x = entry.rid
          BY <3>3, <2>1
        <5>2. CASE x \in dset[r0]
          <6>1. PICK i \in 1..n : delivered[r0][i].rid = x
            BY <5>2, <3>3, <3>1, <2>4
          <6>2. i \in 1..Len(delivered'[r]) /\ delivered'[r][i].rid = x
            BY <6>1, <3>3, <2>4, <1>6
          <6> QED
            BY <6>2
        <5>3. CASE x = entry.rid
          <6>1. n + 1 \in 1..Len(delivered'[r])
            BY <3>3, <2>4, <1>6
          <6>2. delivered'[r][n + 1].rid = x
            BY <5>3, <3>3, <2>4
          <6> QED
            BY <6>1, <6>2
        <5> QED
          BY <5>1, <5>2, <5>3
      <4>2. \A i \in 1..Len(delivered'[r]) :
                delivered'[r][i].rid \in dset'[r]
        <5> SUFFICES ASSUME NEW i \in 1..Len(delivered'[r])
                     PROVE  delivered'[r][i].rid \in dset'[r]
          OBVIOUS
        <5>1. i \in 1..n \/ i = n + 1
          BY <3>3, <2>4, <1>6
        <5>2. CASE i \in 1..n
          <6>1. delivered'[r][i] = delivered[r0][i]
            BY <5>2, <3>3, <2>4
          <6>2. delivered[r0][i].rid \in dset[r0]
            BY <5>2, <3>3, <3>1, <2>4
          <6> QED
            BY <6>1, <6>2, <3>3, <2>1
        <5>3. CASE i = n + 1
          BY <5>3, <3>3, <2>4, <2>1
        <5> QED
          BY <5>1, <5>2, <5>3
      <4> QED
        BY <4>1, <4>2
    <3> QED
      BY <3>2, <3>3
  <2>9. DeliveredOnce'
    <3> SUFFICES ASSUME NEW r \in Replicas,
                        NEW i \in 1..Len(delivered'[r]),
                        NEW j \in 1..Len(delivered'[r]),
                        delivered'[r][i].rid = delivered'[r][j].rid
                 PROVE  i = j
      BY DEF DeliveredOnce
    <3>1. CASE r # r0
      BY <3>1, <2>3, <1>0 DEF DeliveredOnce
    <3>2. CASE r = r0
      <4>1. /\ i \in 1..n \/ i = n + 1
            /\ j \in 1..n \/ j = n + 1
        BY <3>2, <2>4, <1>6
      <4>2. \A m \in 1..n :
                /\ delivered'[r][m] = delivered[r0][m]
                /\ delivered[r0][m].rid \in dset[r0]
        BY <3>2, <2>4, <1>0 DEF DsetDelivered
      <4>3. delivered'[r][n + 1].rid \notin dset[r0]
        BY <3>2, <2>4, <1>B
      <4>4. CASE i \in 1..n /\ j \in 1..n
        BY <4>4, <4>2, <2>4, <1>0 DEF DeliveredOnce
      <4>5. CASE i = n + 1 /\ j = n + 1
        BY <4>5
      <4>6. CASE i \in 1..n /\ j = n + 1
        BY <4>6, <4>2, <4>3
      <4>7. CASE i = n + 1 /\ j \in 1..n
        BY <4>7, <4>2, <4>3
      <4> QED
        BY <4>1, <4>4, <4>5, <4>6, <4>7
    <3> QED
      BY <3>1, <3>2
  <2> QED
    BY <2>5, <1>7, <1>8, <1>9, <1>12, <2>6, <2>7, <2>8, <2>9 DEF PaperInv
<1> QED
  BY <1>1, <1>A, <1>B

(***************************************************************************
Every step preserves the invariant.
***************************************************************************)
LEMMA PaperStep == PaperInv /\ [Next]_vars => PaperInv'
<1> SUFFICES ASSUME PaperInv, [Next]_vars
             PROVE  PaperInv'
  OBVIOUS
<1>0. PaperTypeOK /\ LeaderUp
  BY DEF PaperInv
<1>1. ASSUME NEW x \in Rids, Submit(x)
      PROVE  PaperInv'
  <2>1. UNCHANGED DeliveryVars
    BY <1>1 DEF Submit, DeliveryVars
  <2>2. PaperTypeOK'
    BY <1>0, <1>1 DEF Submit, PaperTypeOK
  <2>3. LeaderUp'
    BY <1>0, <1>1 DEF Submit, LeaderUp
  <2> QED
    BY <2>1, <2>2, <2>3, PaperFrame
<1>2. ASSUME NEW l \in Replicas, Elect(l)
      PROVE  PaperInv'
  <2>1. UNCHANGED DeliveryVars
    BY <1>2 DEF Elect, DeliveryVars
  <2>2. PaperTypeOK'
    BY <1>0, <1>2 DEF Elect, PaperTypeOK
  <2>3. LeaderUp'
    BY <1>0, <1>2 DEF Elect, LeaderUp
  <2> QED
    BY <2>1, <2>2, <2>3, PaperFrame
<1>3. ASSUME NEW r \in Replicas, Crash(r)
      PROVE  PaperInv'
  <2>1. UNCHANGED DeliveryVars
    BY <1>3 DEF Crash, DeliveryVars
  <2>2. PaperTypeOK'
    BY <1>0, <1>3 DEF Crash, PaperTypeOK
  <2>3. LeaderUp'
    BY <1>0, <1>3 DEF Crash, LeaderUp
  <2> QED
    BY <2>1, <2>2, <2>3, PaperFrame
<1>4. ASSUME NEW x \in Rids, Accept(x)
      PROVE  PaperInv'
  <2>1. UNCHANGED DeliveryVars
    BY <1>4 DEF Accept, DeliveryVars
  <2>2. PaperTypeOK'
    BY <1>0, <1>4 DEF Accept, PaperTypeOK
  <2>3. LeaderUp'
    BY <1>0, <1>4 DEF Accept, LeaderUp
  <2> QED
    BY <2>1, <2>2, <2>3, PaperFrame
<1>5. ASSUME NEW l \in Replicas, NEW x \in Rids, NEW y \in Responses,
             Respond(l, x, y)
      PROVE  PaperInv'
  <2>1. UNCHANGED DeliveryVars
    BY <1>5 DEF Respond, DeliveryVars
  <2>2. Entry(x, y) \in Entries
    BY DEF Entry, Entries
  <2>3. PaperTypeOK'
    BY <1>0, <1>5, <2>2 DEF Respond, PaperTypeOK
  <2>4. LeaderUp'
    BY <1>0, <1>5 DEF Respond, LeaderUp
  <2> QED
    BY <2>1, <2>3, <2>4, PaperFrame
<1>6. ASSUME NEW l \in Replicas, NEW e \in Entries, Propose(l, e)
      PROVE  PaperInv'
  <2>1. UNCHANGED DeliveryVars
    BY <1>6 DEF Propose, DeliveryVars
  <2>2. Proposal(e, l) \in Proposals
    BY DEF Proposal, Proposals
  <2>3. PaperTypeOK'
    BY <1>0, <1>6, <2>2 DEF Propose, PaperTypeOK
  <2>4. LeaderUp'
    BY <1>0, <1>6 DEF Propose, LeaderUp
  <2> QED
    BY <2>1, <2>3, <2>4, PaperFrame
<1>7. ASSUME NEW p \in Proposals, Agree(p)
      PROVE  PaperInv'
  BY <1>7, PaperAgree
<1>8. ASSUME NEW p \in Proposals, Drop(p)
      PROVE  PaperInv'
  <2>1. UNCHANGED DeliveryVars
    BY <1>8 DEF Drop, DeliveryVars
  <2>2. PaperTypeOK'
    BY <1>0, <1>8 DEF Drop, PaperTypeOK
  <2>3. LeaderUp'
    BY <1>0, <1>8 DEF Drop, LeaderUp
  <2> QED
    BY <2>1, <2>2, <2>3, PaperFrame
<1>9. ASSUME NEW r \in Replicas, NEW k \in Nat, Learn(r, k)
      PROVE  PaperInv'
  BY <1>9, PaperLearn
<1>10. ASSUME NEW r \in Replicas, Process(r)
       PROVE  PaperInv'
  BY <1>10, PaperProcess
<1>11. CASE UNCHANGED vars
  <2>1. UNCHANGED DeliveryVars
    BY <1>11 DEF vars, DeliveryVars
  <2>2. PaperTypeOK'
    BY <1>0, <1>11 DEF vars, PaperTypeOK
  <2>3. LeaderUp'
    BY <1>0, <1>11 DEF vars, LeaderUp
  <2> QED
    BY <2>1, <2>2, <2>3, PaperFrame
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11
     DEF Next

THEOREM PaperInvariant == Spec => []PaperInv
BY PaperInit, PaperStep, PTL DEF Spec

(***************************************************************************
Lemma 1 (same processed index implies same entry). An index a replica has
processed is at most its processed counter, so the replica learned it
before processing it, and what a replica learns at an index is the entry
agreed there (CG1).
***************************************************************************)
LEMMA SameEntryFromInv == PaperInv => SameProcessedEntry
<1> SUFFICES ASSUME PaperInv,
                    NEW r \in Replicas, NEW t \in Replicas,
                    NEW i \in done[r],
                    i \in done[t]
             PROVE  log[r][i] = log[t][i]
  BY DEF SameProcessedEntry
<1>1. i \in 1..processed[r] /\ i \in 1..processed[t]
  BY DEF PaperInv, DoneIsProcessed
<1>2. i \in DOMAIN log[r] /\ i \in DOMAIN log[t]
  BY <1>1 DEF PaperInv, ProcessedLearned
<1>3. log[r][i] = agreed[i] /\ log[t][i] = agreed[i]
  BY <1>2 DEF PaperInv, LearnedIsAgreed
<1> QED
  BY <1>3

THEOREM Lemma1 == Spec => []SameProcessedEntry
BY PaperInvariant, SameEntryFromInv, PTL

(***************************************************************************
Lemma 2 (no-hole processing). The processed index only ever advances by
one, and each advance records the index it reaches, so the set of indexes
a replica has processed is always an initial segment 1..n. That is the
paper's induction, carried by the invariant DoneIsProcessed.
***************************************************************************)
LEMMA ProcessInOrderStep == PaperInv /\ [Next]_vars => ProcessInOrder
<1> SUFFICES ASSUME PaperInv, [Next]_vars
             PROVE  ProcessInOrder
  OBVIOUS
<1>0. processed \in [Replicas -> Nat]
  BY DEF PaperInv, PaperTypeOK
<1>a. ASSUME processed' = processed
      PROVE  ProcessInOrder
  BY <1>a DEF ProcessInOrder
<1>1. ASSUME NEW x \in Rids, Submit(x)
      PROVE  ProcessInOrder
  BY <1>1, <1>a DEF Submit
<1>2. ASSUME NEW l \in Replicas, Elect(l)
      PROVE  ProcessInOrder
  BY <1>2, <1>a DEF Elect
<1>3. ASSUME NEW r \in Replicas, Crash(r)
      PROVE  ProcessInOrder
  BY <1>3, <1>a DEF Crash
<1>4. ASSUME NEW x \in Rids, Accept(x)
      PROVE  ProcessInOrder
  BY <1>4, <1>a DEF Accept
<1>5. ASSUME NEW l \in Replicas, NEW x \in Rids, NEW y \in Responses,
             Respond(l, x, y)
      PROVE  ProcessInOrder
  BY <1>5, <1>a DEF Respond
<1>6. ASSUME NEW l \in Replicas, NEW e \in Entries, Propose(l, e)
      PROVE  ProcessInOrder
  BY <1>6, <1>a DEF Propose
<1>7. ASSUME NEW p \in Proposals, Agree(p)
      PROVE  ProcessInOrder
  BY <1>7, <1>a DEF Agree
<1>8. ASSUME NEW p \in Proposals, Drop(p)
      PROVE  ProcessInOrder
  BY <1>8, <1>a DEF Drop
<1>9. ASSUME NEW r \in Replicas, NEW k \in Nat, Learn(r, k)
      PROVE  ProcessInOrder
  BY <1>9, <1>a DEF Learn
<1>10. ASSUME NEW r0 \in Replicas, Process(r0)
       PROVE  ProcessInOrder
  <2>1. processed' = [processed EXCEPT ![r0] = processed[r0] + 1]
    BY <1>10 DEF Process
  <2>2. /\ processed'[r0] = processed[r0] + 1
        /\ \A t \in Replicas : t # r0 => processed'[t] = processed[t]
    BY <2>1, <1>0
  <2> QED
    BY <2>2 DEF ProcessInOrder
<1>11. CASE UNCHANGED vars
  BY <1>11, <1>a DEF vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11
     DEF Next

LEMMA NoHoleFromInv == PaperInv => NoHoleProcessing
<1> SUFFICES ASSUME PaperInv,
                    NEW r \in Replicas,
                    NEW i \in done[r],
                    NEW j \in 1..i
             PROVE  j \in done[r]
  BY DEF NoHoleProcessing
<1>1. done[r] = 1..processed[r] /\ processed[r] \in Nat
  BY DEF PaperInv, DoneIsProcessed, PaperTypeOK
<1> QED
  BY <1>1

THEOREM Lemma2 == Spec => []NoHoleProcessing /\ [][ProcessInOrder]_vars
<1>1. PaperInv => NoHoleProcessing
  BY NoHoleFromInv
<1>2. PaperInv /\ [Next]_vars => [ProcessInOrder]_vars
  BY ProcessInOrderStep
<1> QED
  BY <1>1, <1>2, PaperInvariant, PTL DEF Spec

(***************************************************************************
Theorem 1 (Safety). Each of the two delivered responses is the first
agreed entry for the request id. A request id has one first agreed
entry, so the responses are the same entry.
***************************************************************************)
LEMMA AgreementFromInv == PaperInv => Agreement
<1> SUFFICES ASSUME PaperInv,
                    NEW r \in Replicas, NEW t \in Replicas,
                    NEW i \in 1..Len(delivered[r]),
                    NEW j \in 1..Len(delivered[t]),
                    delivered[r][i].rid = delivered[t][j].rid
             PROVE  delivered[r][i].value = delivered[t][j].value
  BY DEF Agreement
<1>1. PICK a \in 1..processed[r] :
          /\ delivered[r][i] = agreed[a]
          /\ \A a2 \in 1..(a - 1) : agreed[a2].rid # agreed[a].rid
  BY DEF PaperInv, DeliveredFirst
<1>2. PICK b \in 1..processed[t] :
          /\ delivered[t][j] = agreed[b]
          /\ \A b2 \in 1..(b - 1) : agreed[b2].rid # agreed[b].rid
  BY DEF PaperInv, DeliveredFirst
<1>3. processed[r] \in Nat /\ processed[t] \in Nat
  BY DEF PaperInv, PaperTypeOK
<1>4. a \in Nat /\ b \in Nat /\ a >= 1 /\ b >= 1
  BY <1>3
<1>5. ~(a < b)
  <2> SUFFICES ASSUME a < b PROVE FALSE
    OBVIOUS
  <2>1. a \in 1..(b - 1)
    BY <1>4
  <2> QED
    BY <2>1, <1>1, <1>2
<1>6. ~(b < a)
  <2> SUFFICES ASSUME b < a PROVE FALSE
    OBVIOUS
  <2>1. b \in 1..(a - 1)
    BY <1>4
  <2> QED
    BY <2>1, <1>1, <1>2
<1>7. a = b
  BY <1>4, <1>5, <1>6
<1> QED
  BY <1>1, <1>2, <1>7

THEOREM Theorem1 == Spec => []Agreement
BY PaperInvariant, AgreementFromInv, PTL

(* A replica delivers a request id at most once. *)
THEOREM DeliveredOnceInvariant == Spec => []DeliveredOnce
<1>1. PaperInv => DeliveredOnce
  BY DEF PaperInv
<1> QED
  BY <1>1, PaperInvariant, PTL
=============================================================================

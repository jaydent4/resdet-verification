--------------------------- MODULE ResdetDelivery ---------------------------
(***************************************************************************
TLAPS proofs, part 2 of 5: the inductive invariant behind Theorem 1.

The paper's proof of Theorem 1 argues that a replica delivers a response
for request id x only from the first agreed log position carrying x, since
any earlier position would have recorded x and suppressed the delivery.
DeliveryInv states that directly, for every replica, in every reachable
state, with no bound on replicas, requests, responses, or log length.

A log position is a pair (s, k): entry k of the batch agreed at index s.
Without batching every batch has one entry and (s, 1) is the paper's
index s.
***************************************************************************)
EXTENDS ResdetFold

Earlier(s2, k2, s, k) == s2 < s \/ (s2 = s /\ k2 < k)

(* Position (s, k) holds the first agreed entry for its request id. *)
FirstCommit(s, k) ==
    \A s2 \in 1..s :
        \A k2 \in 1..Len(consensusLog[s2]) :
            Earlier(s2, k2, s, k) =>
                consensusLog[s2][k2].rid # consensusLog[s][k].rid

DeliveryTypeOK ==
    /\ consensusLog \in Seq(Seq(ResponseItems))
    /\ processed \in [Replicas -> Nat]
    /\ \A r \in Replicas : processed[r] <= Len(consensusLog)
    /\ delivered \in [Replicas -> Seq(ResponseItems)]
    /\ seen \in [Replicas -> SUBSET RequestIds]

(* The deduplication state is exactly the request ids processed so far. *)
SeenIsProcessed ==
    \A r \in Replicas :
        /\ \A x \in seen[r] :
             \E s \in 1..processed[r] :
                \E k \in 1..Len(consensusLog[s]) :
                    consensusLog[s][k].rid = x
        /\ \A s \in 1..processed[r] :
             \A k \in 1..Len(consensusLog[s]) :
                consensusLog[s][k].rid \in seen[r]

(* First-commit-wins: every delivered response is the first agreed entry
   for its request id, at a position the replica has processed. *)
DeliveredFirstCommit ==
    \A r \in Replicas :
        \A i \in 1..Len(delivered[r]) :
            \E s \in 1..processed[r] :
                \E k \in 1..Len(consensusLog[s]) :
                    /\ delivered[r][i] = consensusLog[s][k]
                    /\ FirstCommit(s, k)

DeliveredSeen ==
    \A r \in Replicas :
        \A i \in 1..Len(delivered[r]) :
            delivered[r][i].rid \in seen[r]

SeenDelivered ==
    \A r \in Replicas :
        \A x \in seen[r] :
            \E i \in 1..Len(delivered[r]) : delivered[r][i].rid = x

DeliveredOnce ==
    \A r \in Replicas :
        \A i, j \in 1..Len(delivered[r]) :
            delivered[r][i].rid = delivered[r][j].rid => i = j

DeliveryInv ==
    /\ DeliveryTypeOK
    /\ SeenIsProcessed
    /\ DeliveredFirstCommit
    /\ DeliveredSeen
    /\ SeenDelivered
    /\ DeliveredOnce

THEOREM DeliveryInit == Init => DeliveryInv
<1> SUFFICES ASSUME Init
             PROVE  DeliveryInv
  OBVIOUS
<1>1. /\ consensusLog = <<>>
      /\ processed = [replica \in Replicas |-> 0]
      /\ delivered = [replica \in Replicas |-> <<>>]
      /\ seen = [replica \in Replicas |-> {}]
  BY DEF Init
<1>2. DeliveryTypeOK
  BY <1>1 DEF DeliveryTypeOK
<1>3. SeenIsProcessed
  BY <1>1 DEF SeenIsProcessed
<1>4. DeliveredFirstCommit
  BY <1>1 DEF DeliveredFirstCommit
<1>5. DeliveredSeen
  BY <1>1 DEF DeliveredSeen
<1>6. SeenDelivered
  BY <1>1 DEF SeenDelivered
<1>7. DeliveredOnce
  BY <1>1 DEF DeliveredOnce
<1> QED
  BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF DeliveryInv

(***************************************************************************
A step that leaves the agreed log and every replica's delivery state alone
preserves the invariant.
***************************************************************************)
LEMMA DeliveryUnchanged ==
    ASSUME DeliveryInv,
           UNCHANGED <<consensusLog, processed, delivered, seen>>
    PROVE  DeliveryInv'
BY DEF DeliveryInv, DeliveryTypeOK, SeenIsProcessed, DeliveredFirstCommit,
       DeliveredSeen, SeenDelivered, DeliveredOnce, FirstCommit, Earlier

(***************************************************************************
Consensus agrees on one more batch. Existing indexes keep their batches,
and the invariant only mentions indexes a replica has already processed.
***************************************************************************)
LEMMA DeliveryDecide ==
    ASSUME DeliveryInv,
           NEW batch \in Seq(ResponseItems),
           consensusLog' = Append(consensusLog, batch),
           UNCHANGED <<processed, delivered, seen>>
    PROVE  DeliveryInv'
<1>1. /\ consensusLog \in Seq(Seq(ResponseItems))
      /\ processed \in [Replicas -> Nat]
      /\ \A r \in Replicas : processed[r] <= Len(consensusLog)
      /\ delivered \in [Replicas -> Seq(ResponseItems)]
      /\ seen \in [Replicas -> SUBSET RequestIds]
  BY DEF DeliveryInv, DeliveryTypeOK
<1>2. /\ consensusLog' \in Seq(Seq(ResponseItems))
      /\ Len(consensusLog') = Len(consensusLog) + 1
      /\ \A s \in 1..Len(consensusLog) : consensusLog'[s] = consensusLog[s]
  BY <1>1
<1>3. /\ processed' = processed
      /\ delivered' = delivered
      /\ seen' = seen
  OBVIOUS
<1>4. \A r \in Replicas :
        \A s \in 1..processed[r] :
            /\ s \in 1..Len(consensusLog)
            /\ consensusLog'[s] = consensusLog[s]
  BY <1>1, <1>2
<1>5. DeliveryTypeOK'
  BY <1>1, <1>2, <1>3 DEF DeliveryTypeOK
<1>6. SeenIsProcessed'
  <2>1. SeenIsProcessed
    BY DEF DeliveryInv
  <2> QED
    BY <2>1, <1>3, <1>4 DEF SeenIsProcessed
<1>7. DeliveredFirstCommit'
  <2> SUFFICES ASSUME NEW r \in Replicas,
                      NEW i \in 1..Len(delivered[r])
               PROVE  \E s \in 1..processed[r] :
                        \E k \in 1..Len(consensusLog'[s]) :
                            /\ delivered[r][i] = consensusLog'[s][k]
                            /\ FirstCommit(s, k)'
    BY <1>3 DEF DeliveredFirstCommit
  <2>1. PICK s \in 1..processed[r] :
            \E k \in 1..Len(consensusLog[s]) :
                /\ delivered[r][i] = consensusLog[s][k]
                /\ FirstCommit(s, k)
    BY DEF DeliveryInv, DeliveredFirstCommit
  <2>2. PICK k \in 1..Len(consensusLog[s]) :
            /\ delivered[r][i] = consensusLog[s][k]
            /\ FirstCommit(s, k)
    BY <2>1
  <2>3. /\ consensusLog'[s] = consensusLog[s]
        /\ \A s2 \in 1..s : consensusLog'[s2] = consensusLog[s2]
    BY <1>1, <1>2
  <2>4. FirstCommit(s, k)'
    BY <2>2, <2>3 DEF FirstCommit, Earlier
  <2> QED
    BY <2>2, <2>3, <2>4
<1>8. DeliveredSeen'
  BY <1>3 DEF DeliveryInv, DeliveredSeen
<1>9. SeenDelivered'
  BY <1>3 DEF DeliveryInv, SeenDelivered
<1>10. DeliveredOnce'
  BY <1>3 DEF DeliveryInv, DeliveredOnce
<1> QED
  BY <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF DeliveryInv

(***************************************************************************
A replica processes its next learned index. This is the heart of the
paper's Theorem 1 argument: a newly delivered entry carries a request id
that is neither in the deduplication state (so, by SeenIsProcessed, at no
earlier index) nor earlier in the same batch, hence it is the first agreed
entry for that request id.
***************************************************************************)
LEMMA DeliveryProcess ==
    ASSUME DeliveryInv,
           ~MutantNoDedup,
           NEW r0 \in Replicas,
           ProcessContiguous(r0)
    PROVE  DeliveryInv'
<1> DEFINE n == processed[r0] + 1
           items == consensusLog[n]
           sn == seen[r0]
           out == delivered[r0]
           result == ApplyItems(items, sn, out)
<1>1. /\ consensusLog \in Seq(Seq(ResponseItems))
      /\ processed \in [Replicas -> Nat]
      /\ \A r \in Replicas : processed[r] <= Len(consensusLog)
      /\ delivered \in [Replicas -> Seq(ResponseItems)]
      /\ seen \in [Replicas -> SUBSET RequestIds]
  BY DEF DeliveryInv, DeliveryTypeOK
<1>2. /\ n \in 1..Len(consensusLog)
      /\ processed' = [processed EXCEPT ![r0] = n]
      /\ seen' = [seen EXCEPT ![r0] = result.seen]
      /\ delivered' = [delivered EXCEPT ![r0] = result.output]
      /\ consensusLog' = consensusLog
  BY DEF ProcessContiguous
<1>3. /\ processed[r0] \in Nat
      /\ n \in Nat
      /\ processed[r0] = n - 1
      /\ items \in Seq(ResponseItems)
      /\ out \in Seq(ResponseItems)
      /\ sn \subseteq RequestIds
  BY <1>1, <1>2
<1>4. AppliedCorrectly(ResponseItems, items, sn, out, result)
  BY <1>3, ApplyItemsCorrect
<1> HIDE DEF result
<1>5. /\ result.seen = sn \union {items[k].rid : k \in 1..Len(items)}
      /\ result.output \in Seq(ResponseItems)
      /\ Len(out) <= Len(result.output)
      /\ \A i \in 1..Len(out) : result.output[i] = out[i]
  BY <1>4 DEF AppliedCorrectly
<1>6. \A i \in (Len(out) + 1)..Len(result.output) :
         \E k \in 1..Len(items) :
            /\ result.output[i] = items[k]
            /\ items[k].rid \notin sn
            /\ \A j \in 1..(k - 1) : items[j].rid # items[k].rid
  BY <1>4 DEF AppliedCorrectly
<1>7. \A i, j \in (Len(out) + 1)..Len(result.output) :
         result.output[i].rid = result.output[j].rid => i = j
  BY <1>4 DEF AppliedCorrectly
<1>8. \A k \in 1..Len(items) :
         items[k].rid \notin sn =>
            \E i \in (Len(out) + 1)..Len(result.output) :
                result.output[i].rid = items[k].rid
  BY <1>4 DEF AppliedCorrectly
<1>9. /\ processed'[r0] = n
      /\ seen'[r0] = result.seen
      /\ delivered'[r0] = result.output
      /\ \A r \in Replicas : r # r0 =>
            /\ processed'[r] = processed[r]
            /\ seen'[r] = seen[r]
            /\ delivered'[r] = delivered[r]
  BY <1>1, <1>2
<1>10. /\ Len(out) \in Nat
       /\ Len(result.output) \in Nat
       /\ Len(items) \in Nat
       /\ \A k \in 1..Len(items) : items[k] \in ResponseItems
       /\ \A k \in 1..Len(items) : items[k].rid \in RequestIds
  BY <1>3, <1>5 DEF ResponseItems
<1> HIDE DEF n, items, sn, out
<1>11. DeliveryTypeOK'
  <2>1. processed' \in [Replicas -> Nat]
    BY <1>1, <1>2, <1>3
  <2>2. \A r \in Replicas : processed'[r] <= Len(consensusLog')
    BY <1>1, <1>2, <1>3, <1>9
  <2>3. delivered' \in [Replicas -> Seq(ResponseItems)]
    BY <1>1, <1>2, <1>5
  <2>4. result.seen \in SUBSET RequestIds
    BY <1>3, <1>5, <1>10
  <2>5. seen' \in [Replicas -> SUBSET RequestIds]
    BY <1>1, <1>2, <2>4
  <2> QED
    BY <1>1, <1>2, <2>1, <2>2, <2>3, <2>5 DEF DeliveryTypeOK
<1>12. SeenIsProcessed
  BY DEF DeliveryInv
<1>13. /\ \A x \in sn :
            \E s \in 1..(n - 1) :
                \E k \in 1..Len(consensusLog[s]) :
                    consensusLog[s][k].rid = x
       /\ \A s \in 1..(n - 1) :
            \A k \in 1..Len(consensusLog[s]) :
                consensusLog[s][k].rid \in sn
  BY <1>12, <1>3 DEF SeenIsProcessed, sn
<1>14. SeenIsProcessed'
  <2> SUFFICES ASSUME NEW r \in Replicas
               PROVE  /\ \A x \in seen'[r] :
                            \E s \in 1..processed'[r] :
                                \E k \in 1..Len(consensusLog[s]) :
                                    consensusLog[s][k].rid = x
                      /\ \A s \in 1..processed'[r] :
                            \A k \in 1..Len(consensusLog[s]) :
                                consensusLog[s][k].rid \in seen'[r]
    BY <1>2 DEF SeenIsProcessed
  <2>1. CASE r # r0
    BY <2>1, <1>9, <1>12 DEF SeenIsProcessed
  <2>2. CASE r = r0
    <3>1. \A x \in result.seen :
            \E s \in 1..n :
                \E k \in 1..Len(consensusLog[s]) :
                    consensusLog[s][k].rid = x
      <4> TAKE x \in result.seen
      <4>1. CASE x \in sn
        <5>1. PICK s \in 1..(n - 1) :
                \E k \in 1..Len(consensusLog[s]) :
                    consensusLog[s][k].rid = x
          BY <4>1, <1>13
        <5>2. s \in 1..n
          BY <1>3
        <5> QED
          BY <5>1, <5>2
      <4>2. CASE x \notin sn
        <5>1. PICK k \in 1..Len(items) : x = items[k].rid
          BY <4>2, <1>5
        <5>2. n \in 1..n
          BY <1>2, <1>3
        <5> QED
          BY <5>1, <5>2 DEF items
      <4> QED
        BY <4>1, <4>2
    <3>2. \A s \in 1..n :
            \A k \in 1..Len(consensusLog[s]) :
                consensusLog[s][k].rid \in result.seen
      <4> TAKE s \in 1..n
      <4> TAKE k \in 1..Len(consensusLog[s])
      <4>1. CASE s = n
        BY <4>1, <1>5 DEF items
      <4>2. CASE s # n
        <5>1. s \in 1..(n - 1)
          BY <4>2, <1>3
        <5> QED
          BY <5>1, <1>13, <1>5
      <4> QED
        BY <4>1, <4>2
    <3> QED
      BY <2>2, <3>1, <3>2, <1>9
  <2> QED
    BY <2>1, <2>2
<1>15. \A s, k : FirstCommit(s, k)' <=> FirstCommit(s, k)
  BY <1>2 DEF FirstCommit, Earlier
<1>16. DeliveredFirstCommit'
  <2> SUFFICES ASSUME NEW r \in Replicas,
                      NEW i \in 1..Len(delivered'[r])
               PROVE  \E s \in 1..processed'[r] :
                        \E k \in 1..Len(consensusLog[s]) :
                            /\ delivered'[r][i] = consensusLog[s][k]
                            /\ FirstCommit(s, k)
    BY <1>2, <1>15 DEF DeliveredFirstCommit
  <2>1. DeliveredFirstCommit
    BY DEF DeliveryInv
  <2>2. CASE r # r0
    BY <2>1, <2>2, <1>9 DEF DeliveredFirstCommit
  <2>3. CASE r = r0
    <3>1. i \in 1..Len(result.output)
      BY <2>3, <1>9
    <3>2. CASE i <= Len(out)
      <4>1. /\ i \in 1..Len(delivered[r0])
            /\ delivered'[r][i] = delivered[r0][i]
        BY <3>1, <3>2, <2>3, <1>5, <1>9, <1>10 DEF out
      <4>2. PICK s \in 1..processed[r0] :
                \E k \in 1..Len(consensusLog[s]) :
                    /\ delivered[r0][i] = consensusLog[s][k]
                    /\ FirstCommit(s, k)
        BY <4>1, <2>1 DEF DeliveredFirstCommit
      <4>3. s \in 1..processed'[r]
        BY <2>3, <1>3, <1>9
      <4> QED
        BY <4>1, <4>2, <4>3
    <3>3. CASE ~(i <= Len(out))
      <4>1. i \in (Len(out) + 1)..Len(result.output)
        BY <3>1, <3>3, <1>10
      <4>2. PICK k \in 1..Len(items) :
                /\ result.output[i] = items[k]
                /\ items[k].rid \notin sn
                /\ \A j \in 1..(k - 1) : items[j].rid # items[k].rid
        BY <4>1, <1>6
      <4>3. n \in 1..processed'[r]
        BY <2>3, <1>2, <1>3, <1>9
      <4>4. FirstCommit(n, k)
        <5> SUFFICES ASSUME NEW s2 \in 1..n,
                            NEW k2 \in 1..Len(consensusLog[s2]),
                            Earlier(s2, k2, n, k)
                     PROVE  consensusLog[s2][k2].rid # consensusLog[n][k].rid
          BY DEF FirstCommit
        <5>1. CASE s2 = n
          <6>1. k2 \in 1..(k - 1)
            BY <5>1, <1>3, <1>10 DEF Earlier
          <6> QED
            BY <6>1, <5>1, <4>2 DEF items
        <5>2. CASE s2 # n
          <6>1. s2 \in 1..(n - 1)
            BY <5>2, <1>3
          <6>2. consensusLog[s2][k2].rid \in sn
            BY <6>1, <1>13
          <6> QED
            BY <6>2, <4>2 DEF items
        <5> QED
          BY <5>1, <5>2
      <4>5. delivered'[r][i] = consensusLog[n][k]
        BY <2>3, <4>2, <1>9 DEF items
      <4>6. k \in 1..Len(consensusLog[n])
        BY DEF items
      <4> QED
        BY <4>3, <4>4, <4>5, <4>6
    <3> QED
      BY <3>2, <3>3
  <2> QED
    BY <2>2, <2>3
<1>17. DeliveredSeen
  BY DEF DeliveryInv
<1>18. \A i \in 1..Len(out) : out[i].rid \in sn
  BY <1>17 DEF DeliveredSeen, out, sn
<1>19. DeliveredSeen'
  <2> SUFFICES ASSUME NEW r \in Replicas,
                      NEW i \in 1..Len(delivered'[r])
               PROVE  delivered'[r][i].rid \in seen'[r]
    BY DEF DeliveredSeen
  <2>1. CASE r # r0
    BY <2>1, <1>9, <1>17 DEF DeliveredSeen
  <2>2. CASE r = r0
    <3>1. i \in 1..Len(result.output)
      BY <2>2, <1>9
    <3>2. CASE i <= Len(out)
      <4>1. i \in 1..Len(out)
        BY <3>1, <3>2, <1>10
      <4> QED
        BY <4>1, <1>5, <1>9, <1>18, <2>2
    <3>3. CASE ~(i <= Len(out))
      <4>1. i \in (Len(out) + 1)..Len(result.output)
        BY <3>1, <3>3, <1>10
      <4>2. PICK k \in 1..Len(items) : result.output[i] = items[k]
        BY <4>1, <1>6
      <4> QED
        BY <4>2, <1>5, <1>9, <2>2
    <3> QED
      BY <3>2, <3>3
  <2> QED
    BY <2>1, <2>2
<1>20. SeenDelivered
  BY DEF DeliveryInv
<1>21. SeenDelivered'
  <2> SUFFICES ASSUME NEW r \in Replicas,
                      NEW x \in seen'[r]
               PROVE  \E i \in 1..Len(delivered'[r]) : delivered'[r][i].rid = x
    BY DEF SeenDelivered
  <2>1. CASE r # r0
    BY <2>1, <1>9, <1>20 DEF SeenDelivered
  <2>2. CASE r = r0
    <3>1. x \in result.seen
      BY <2>2, <1>9
    <3>2. CASE x \in sn
      <4>1. PICK i \in 1..Len(out) : out[i].rid = x
        BY <3>2, <1>20 DEF SeenDelivered, out, sn
      <4>2. /\ i \in 1..Len(result.output)
            /\ result.output[i].rid = x
        BY <4>1, <1>5, <1>10
      <4> QED
        BY <4>2, <1>9, <2>2
    <3>3. CASE x \notin sn
      <4>1. PICK k \in 1..Len(items) : x = items[k].rid
        BY <3>1, <3>3, <1>5
      <4>2. PICK i \in (Len(out) + 1)..Len(result.output) :
                result.output[i].rid = items[k].rid
        BY <4>1, <3>3, <1>8
      <4>3. i \in 1..Len(result.output)
        BY <1>10
      <4> QED
        BY <4>1, <4>2, <4>3, <1>9, <2>2
    <3> QED
      BY <3>2, <3>3
  <2> QED
    BY <2>1, <2>2
<1>22. DeliveredOnce
  BY DEF DeliveryInv
<1>23. DeliveredOnce'
  <2> SUFFICES ASSUME NEW r \in Replicas,
                      NEW i \in 1..Len(delivered'[r]),
                      NEW j \in 1..Len(delivered'[r]),
                      delivered'[r][i].rid = delivered'[r][j].rid
               PROVE  i = j
    BY DEF DeliveredOnce
  <2>1. CASE r # r0
    BY <2>1, <1>9, <1>22 DEF DeliveredOnce
  <2>2. CASE r = r0
    <3>1. /\ i \in 1..Len(result.output)
          /\ j \in 1..Len(result.output)
          /\ result.output[i].rid = result.output[j].rid
      BY <2>2, <1>9
    <3>2. \A a \in 1..Len(result.output) :
            a <= Len(out) =>
                /\ a \in 1..Len(out)
                /\ result.output[a] = out[a]
                /\ result.output[a].rid \in sn
      BY <1>5, <1>10, <1>18
    <3>3. \A a \in 1..Len(result.output) :
            ~(a <= Len(out)) =>
                /\ a \in (Len(out) + 1)..Len(result.output)
                /\ result.output[a].rid \notin sn
      <4> TAKE a \in 1..Len(result.output)
      <4> HAVE ~(a <= Len(out))
      <4>1. a \in (Len(out) + 1)..Len(result.output)
        BY <1>10
      <4>2. PICK k \in 1..Len(items) :
                /\ result.output[a] = items[k]
                /\ items[k].rid \notin sn
        BY <4>1, <1>6
      <4> QED
        BY <4>1, <4>2
    <3>4. CASE i <= Len(out) /\ j <= Len(out)
      <4>1. /\ i \in 1..Len(delivered[r0])
            /\ j \in 1..Len(delivered[r0])
            /\ delivered[r0][i].rid = delivered[r0][j].rid
        BY <3>1, <3>2, <3>4 DEF out
      <4> QED
        BY <4>1, <1>22 DEF DeliveredOnce
    <3>5. CASE ~(i <= Len(out)) /\ ~(j <= Len(out))
      BY <3>1, <3>3, <3>5, <1>7
    <3>6. CASE i <= Len(out) /\ ~(j <= Len(out))
      BY <3>1, <3>2, <3>3, <3>6
    <3>7. CASE ~(i <= Len(out)) /\ j <= Len(out)
      BY <3>1, <3>2, <3>3, <3>7
    <3> QED
      BY <3>4, <3>5, <3>6, <3>7
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>11, <1>14, <1>16, <1>19, <1>21, <1>23 DEF DeliveryInv

THEOREM DeliveryStep ==
    ASSUME StrictDelivery
    PROVE  DeliveryInv /\ [Next]_vars => DeliveryInv'
<1> SUFFICES ASSUME DeliveryInv, [Next]_vars
             PROVE  DeliveryInv'
  OBVIOUS
<1> USE DEF StrictDelivery
<1>1. CASE SubmitVoteAction
  BY <1>1, DeliveryUnchanged DEF SubmitVoteAction, SubmitVote
<1>2. CASE SelectAction
  BY <1>2, DeliveryUnchanged DEF SelectAction, SelectByQuorum, TimeoutSelect
<1>3. CASE DispatchAction
  BY <1>3, DeliveryUnchanged DEF DispatchAction, Dispatch
<1>4. CASE ExternalRespondAction
  BY <1>4, DeliveryUnchanged DEF ExternalRespondAction, ExternalRespond
<1>5. CASE ProposeResponseAction
  BY <1>5, DeliveryUnchanged DEF ProposeResponseAction, ProposeResponse
<1>6. CASE DecideAction
  <2>1. ASSUME NEW item \in ResponseItems, DecideOne(item)
        PROVE  DeliveryInv'
    <3>1. <<item>> \in Seq(ResponseItems)
      OBVIOUS
    <3>2. /\ consensusLog' = Append(consensusLog, <<item>>)
          /\ UNCHANGED <<processed, delivered, seen>>
      BY <2>1 DEF DecideOne
    <3> QED
      BY <3>1, <3>2, DeliveryDecide
  <2>2. ASSUME NEW first \in ResponseItems,
               NEW second \in ResponseItems,
               DecidePair(first, second)
        PROVE  DeliveryInv'
    <3>1. <<first, second>> \in Seq(ResponseItems)
      OBVIOUS
    <3>2. /\ consensusLog' = Append(consensusLog, <<first, second>>)
          /\ UNCHANGED <<processed, delivered, seen>>
      BY <2>2 DEF DecidePair
    <3> QED
      BY <3>1, <3>2, DeliveryDecide
  <2> QED
    BY <1>6, <2>1, <2>2 DEF DecideAction
<1>7. CASE LearnAction
  BY <1>7, DeliveryUnchanged DEF LearnAction, LearnSlot
<1>8. CASE ProcessAction
  BY <1>8, DeliveryProcess DEF ProcessAction
<1>9. CASE \E replica \in Replicas, slot \in 1..MaxSlots :
              ProcessNonContiguous(replica, slot)
  BY <1>9 DEF ProcessNonContiguous
<1>10. CASE \E replica \in Replicas, item \in ResponseItems :
               DeliverBeforeConsensus(replica, item)
  BY <1>10 DEF DeliverBeforeConsensus
<1>11. CASE \E replica \in Replicas : Crash(replica)
  BY <1>11, DeliveryUnchanged DEF Crash
<1>12. CASE \E replica \in Replicas : Recover(replica)
  BY <1>12, DeliveryUnchanged DEF Recover
<1>13. CASE \E replica \in Replicas : Elect(replica)
  BY <1>13, DeliveryUnchanged DEF Elect
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
  BY <1>16, DeliveryUnchanged DEF vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
     <1>11, <1>12, <1>13, <1>14, <1>15, <1>16 DEF Next

THEOREM DeliveryInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []DeliveryInv
<1>1. Init => DeliveryInv
  BY DeliveryInit
<1>2. DeliveryInv /\ [Next]_vars => DeliveryInv'
  BY DeliveryStep
<1> QED
  BY <1>1, <1>2, PTL DEF Spec
=============================================================================

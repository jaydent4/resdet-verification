------------------------ MODULE ResdetPaperTheorems ------------------------
(***************************************************************************
TLAPS proofs about ResdetPaper.tla, part 5 of 5: Theorem 2.

Theorem 2 (Liveness). Under CG2-CG3 and L1-L4, for every logical request
with request id x submitted, every non-faulty replica eventually delivers
a response for x.

  Theorem2 ==
      LiveSpec /\ StableLeader(l) /\ NonFaulty(r)
          => (x \in submitted ~> Delivers(r, x))

for any request id x and replicas l and r. LiveSpec carries L1-L4,
CG3(2) and CG3(3) as fairness; StableLeader(l) is CG3(1) in the form the
proof needs; NonFaulty(r) says r never crashes; CG1 and CG2 are properties
of the consensus box in ResdetPaper.tla. Theorem2Paper states it with
"some replica is eventually the leader for good".

The proof is the paper's: by Lemma 3 an entry for x is eventually agreed
at some index i; by Lemma 4 the replica eventually learns every index
through i; by Lemma 5 it then has delivered or eventually delivers a
response for x. The index i is chosen by the behavior, at the moment the
entry is agreed; AgreedDeliversPoint is where the proof picks it.
***************************************************************************)
EXTENDS ResdetPaperLemma3, ResdetPaperLemma45

LEMMA AgreedAtIndex ==
    ASSUME NEW x \in Rids, NEW i \in Nat
    PROVE  AgreedAt(x, i) => i \in 1..Len(agreed)
BY DEF AgreedAt

(* Lemmas 4 and 5 for an entry agreed at a fixed index i. *)
LEMMA AgreedDeliversAt ==
    ASSUME NEW r \in Replicas, NEW x \in Rids, NEW i \in Nat
    PROVE  LiveHyp /\ NonFaulty(r)
           => [](AgreedAt(x, i) => <>Delivers(r, x))
<1>1. LiveHyp /\ NonFaulty(r)
      => (i \in 1..Len(agreed) ~> LearnedThrough(r, i))
  BY Lemma4Core
<1>2. LiveHyp /\ NonFaulty(r)
      => ((LearnedThrough(r, i) /\ AgreedAt(x, i)) ~> Delivers(r, x))
  BY Lemma5Core
<1>3. LiveState /\ AgreedAt(x, i) /\ [Next]_vars => AgreedAt(x, i)'
  <2>1. \A k \in Nat :
            LiveState /\ AgreedAt(x, k) /\ [Next]_vars => AgreedAt(x, k)'
    BY AgreedAtStable
  <2> QED
    BY <2>1
<1>4. AgreedAt(x, i) => i \in 1..Len(agreed)
  BY AgreedAtIndex
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, PTL DEF LiveHyp, NonFaulty

(* The same when the index is whatever index the entry was agreed at. *)
LEMMA AgreedDeliversPoint ==
    ASSUME NEW r \in Replicas, NEW x \in Rids
    PROVE  LiveHyp /\ NonFaulty(r) => (Agreed(x) => <>Delivers(r, x))
<1> SUFFICES ASSUME LiveHyp, NonFaulty(r), Agreed(x)
             PROVE  <>Delivers(r, x)
  OBVIOUS
<1>1. LiveState
  BY PTL DEF LiveHyp
<1>2. PICK i \in Nat : AgreedAt(x, i)
  <2>1. agreed \in Seq(Entries)
    BY <1>1 DEF LiveState, PaperInv, PaperTypeOK
  <2>2. PICK j \in 1..Len(agreed) : agreed[j].rid = x
    BY DEF Agreed
  <2>3. j \in Nat
    BY <2>1
  <2> QED
    BY <2>2, <2>3 DEF AgreedAt
<1>3. LiveHyp /\ NonFaulty(r) => [](AgreedAt(x, i) => <>Delivers(r, x))
  BY AgreedDeliversAt
<1> QED
  BY <1>2, <1>3, PTL

(***************************************************************************
Theorem 2 (Liveness).
***************************************************************************)
THEOREM Theorem2Core ==
    ASSUME NEW x \in Rids, NEW l \in Replicas, NEW r \in Replicas
    PROVE  LiveHyp /\ StableLeader(l) /\ NonFaulty(r)
           => (x \in submitted ~> Delivers(r, x))
<1>1. LiveHyp /\ StableLeader(l) => (x \in submitted ~> Agreed(x))
  BY Lemma3Core
<1>2. LiveHyp /\ NonFaulty(r) => (Agreed(x) => <>Delivers(r, x))
  BY AgreedDeliversPoint, PTL
<1> QED
  BY <1>1, <1>2, PTL DEF LiveHyp, NonFaulty

THEOREM Theorem2 ==
    ASSUME NEW x \in Rids, NEW l \in Replicas, NEW r \in Replicas
    PROVE  LiveSpec /\ StableLeader(l) /\ NonFaulty(r)
           => (x \in submitted ~> Delivers(r, x))
BY Theorem2Core, LiveSpecHyp, PTL

(* With CG3(1) as "some replica is eventually the leader for good". *)
THEOREM Theorem2Paper ==
    ASSUME NEW x \in Rids, NEW r \in Replicas
    PROVE  LiveSpec /\ (\E l \in Replicas : StableLeader(l)) /\ NonFaulty(r)
           => (x \in submitted ~> Delivers(r, x))
<1> SUFFICES ASSUME LiveSpec,
                    \E l \in Replicas : StableLeader(l),
                    NonFaulty(r)
             PROVE  x \in submitted ~> Delivers(r, x)
  OBVIOUS
<1>1. PICK l \in Replicas : StableLeader(l)
  OBVIOUS
<1>2. LiveSpec /\ StableLeader(l) /\ NonFaulty(r)
      => (x \in submitted ~> Delivers(r, x))
  BY Theorem2
<1> QED
  BY <1>1, <1>2, PTL
=============================================================================

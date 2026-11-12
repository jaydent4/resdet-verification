-------------------------- MODULE ResdetLiveProgress --------------------------
(***************************************************************************
TLAPS liveness proof, part 2 of 5: a reachable state that is not Done can
still take a step of some fair action.

This is the state-level core of the paper's Lemmas 3-5 read backwards: if
no fair action can step, then every replica has submitted every request,
every request is selected, dispatched, answered, proposed and agreed, and
every replica has learned and processed the whole log, so every replica
has delivered a response for every request.
***************************************************************************)
EXTENDS ResdetLiveInv

(***************************************************************************
A subset of a finite set that is at least as large as the set is the set.
***************************************************************************)
LEMMA FullSubset ==
    ASSUME NEW S, IsFiniteSet(S), NEW T \in SUBSET S,
           NEW bound \in Nat,
           bound >= Cardinality(S), bound <= Cardinality(T)
    PROVE  T = S
<1>1. /\ IsFiniteSet(T)
      /\ Cardinality(T) <= Cardinality(S)
      /\ Cardinality(S) = Cardinality(T) => S = T
  BY FS_Subset
<1>2. Cardinality(S) \in Nat /\ Cardinality(T) \in Nat
  BY <1>1, FS_CardinalityType
<1>3. Cardinality(S) = Cardinality(T)
  BY <1>1, <1>2
<1> QED
  BY <1>1, <1>3

THEOREM Progress ==
    ASSUME LivenessAssumptions
    PROVE  LiveState /\ ~Done => CanStep
<1> SUFFICES ASSUME LiveState, ~CanStep
             PROVE  Done
  OBVIOUS
<1>inv. /\ LiveInv
        /\ ValidityInv
        /\ DeliveryInv
  BY DEF LiveState
<1>can. /\ ~CanVote
        /\ ~CanSelect
        /\ ~CanDispatch
        /\ ~CanRespond
        /\ ~CanPropose
        /\ ~CanDecide
        /\ ~CanLearn
        /\ ~CanProcess
  BY DEF CanStep
<1>ty. /\ leader \in Replicas
       /\ seen \in [Replicas -> SUBSET RequestIds]
       /\ Len(consensusLog) <= MaxSlots
       /\ consensusLog \in Seq(Seq(ResponseItems))
       /\ processed \in [Replicas -> Nat]
       /\ Len(consensusLog) \in Nat
       /\ MaxSlots \in Nat
  <2>1. consensusLog \in Seq(Seq(ResponseItems))
    BY <1>inv DEF ValidityInv, ValidityTypeOK
  <2>2. Len(consensusLog) \in Nat
    BY <2>1
  <2>3. MaxSlots \in Nat
    BY ConstantAssumptions
  <2> QED
    BY <1>inv, <2>1, <2>2, <2>3 DEF LiveInv, ValidityInv, ValidityTypeOK

(* 1. Every replica has submitted every request. *)
<1>1. \A q \in RequestIds : AllVoted(q)
  BY <1>can DEF CanVote, AllVoted

(* 2. Every request is selected. *)
<1>2. \A q \in RequestIds : selected[q] # NoValue
  BY <1>can, <1>1 DEF CanSelect

(* 3. The leader has dispatched every request. *)
<1>3. \A q \in RequestIds : leader \in dispatchers[q]
  <2> TAKE q \in RequestIds
  <2>1. dispatchers[q] # {}
    BY <1>can, <1>2 DEF CanDispatch
  <2>2. dispatchers[q] \subseteq {leader}
    BY <1>inv DEF LiveInv, LeaderOnly
  <2> QED
    BY <2>1, <2>2

(* 4. The leader has a response for every request. *)
<1>4. \A q \in RequestIds : execResponse[q][leader] # NoValue
  BY <1>can, <1>3 DEF CanRespond

(* 5. The leader's response for every request is proposed. *)
<1>5. \A q \in RequestIds :
        ObservedItem(q, execResponse[q][leader]) \in proposed
  BY <1>can, <1>3, <1>4 DEF CanPropose

(* 6. Every request id occurs in the agreed log. *)
<1>6. LogRids = RequestIds
  <2>1. LogRids \in SUBSET RequestIds
    BY DEF LogRids
  <2>2. CASE Len(consensusLog) < MaxSlots
    <3>1. \A item \in proposed : item.rid \in LogRids
      BY <1>can, <2>2 DEF CanDecide
    <3>2. \A q \in RequestIds : q \in LogRids
      <4> TAKE q \in RequestIds
      <4> DEFINE item == ObservedItem(q, execResponse[q][leader])
      <4>1. item \in proposed
        BY <1>5
      <4>2. item.rid = q
        BY DEF ObservedItem
      <4>3. item.rid \in LogRids
        BY <3>1, <4>1
      <4> QED
        BY <4>2, <4>3
    <3> QED
      BY <2>1, <3>2
  <2>3. CASE Len(consensusLog) = MaxSlots
    <3>1. CASE LogRids = RequestIds
      BY <3>1
    <3>2. CASE Len(consensusLog) <= Cardinality(LogRids)
      <4>1. IsFiniteSet(RequestIds)
        BY DEF LivenessAssumptions
      <4>2. MaxSlots >= Cardinality(RequestIds)
        BY DEF LivenessAssumptions
      <4>3. MaxSlots <= Cardinality(LogRids)
        BY <2>3, <3>2
      <4> QED
        BY <1>ty, <2>1, <4>1, <4>2, <4>3, FullSubset
    <3> QED
      BY <1>inv, <3>1, <3>2 DEF LiveInv, SlotsCount
  <2> QED
    BY <1>ty, <2>2, <2>3

(* 7. Every replica has learned every agreed index. *)
<1>7. \A r \in Replicas :
        \A s \in 1..Len(consensusLog) : s \in learned[r]
  BY <1>can DEF CanLearn

(* 8. Every replica has processed the whole log. *)
<1>8. \A r \in Replicas : processed[r] = Len(consensusLog)
  <2> TAKE r \in Replicas
  <2>1. processed[r] \in Nat
    BY <1>ty
  <2>2. processed[r] <= Len(consensusLog)
    BY <1>inv DEF ValidityInv, ProcessedWithinLog
  <2>3. ~(processed[r] < Len(consensusLog))
    <3> SUFFICES ASSUME processed[r] < Len(consensusLog)
                 PROVE  FALSE
      OBVIOUS
    <3>1. processed[r] + 1 \in 1..Len(consensusLog)
      BY <1>ty, <2>1
    <3>2. processed[r] + 1 \in learned[r]
      BY <1>7, <3>1
    <3> QED
      BY <1>can, <3>2 DEF CanProcess
  <2> QED
    BY <1>ty, <2>1, <2>2, <2>3

(* 9. So every replica has recorded every request id. *)
<1>9. \A r \in Replicas : seen[r] = RequestIds
  <2> TAKE r \in Replicas
  <2>1. seen[r] \in SUBSET RequestIds
    BY <1>ty
  <2>2. \A s \in 1..processed[r] :
          \A k \in 1..Len(consensusLog[s]) :
              consensusLog[s][k].rid \in seen[r]
    BY <1>inv DEF DeliveryInv, SeenIsProcessed
  <2>3. \A q \in RequestIds : q \in seen[r]
    <3> TAKE q \in RequestIds
    <3>1. q \in LogRids
      BY <1>6
    <3>2. PICK s \in 1..Len(consensusLog) :
            \E k \in 1..Len(consensusLog[s]) :
                consensusLog[s][k].rid = q
      BY <3>1 DEF LogRids
    <3>3. PICK k \in 1..Len(consensusLog[s]) :
            consensusLog[s][k].rid = q
      BY <3>2
    <3>4. s \in 1..processed[r]
      BY <1>8
    <3> QED
      BY <2>2, <3>3, <3>4
  <2> QED
    BY <2>1, <2>3
<1> QED
  BY <1>9 DEF Done
=============================================================================

--------------------------- MODULE ResdetRequests ---------------------------
(***************************************************************************
TLAPS proofs of the invariants on the request side of the protocol and of
the full type invariant. With these, every invariant that the passing TLC
configurations check has a TLAPS proof for unbounded parameters.

Each theorem assumes StrictDelivery plus only the switches its invariant
really depends on.
***************************************************************************)
EXTENDS ResdetTheorems

(***************************************************************************
What one step of the strict protocol can do to the request-side variables.
Each of the remaining invariants reads one or two of them, so this single
case analysis over Next serves all five.
***************************************************************************)
LEMMA StepEffects ==
    ASSUME StrictDelivery, [Next]_vars
    PROVE  /\ earlyDelivery' = earlyDelivery
           /\ \/ UNCHANGED <<dispatchers, unauthorizedDispatch>>
              \/ \E replica \in Replicas, request \in RequestIds :
                    Dispatch(replica, request)
           /\ \/ UNCHANGED <<votes, selected, selectedByFallback>>
              \/ \E replica \in Replicas, request \in RequestIds,
                    payload \in Payloads :
                    SubmitVote(replica, request, payload)
              \/ \E replica \in Replicas, request \in RequestIds,
                    payload \in Payloads :
                    SelectByQuorum(replica, request, payload)
              \/ \E replica \in Replicas, request \in RequestIds,
                    payload \in Payloads :
                    TimeoutSelect(replica, request, payload)
<1> USE DEF StrictDelivery
<1> DEFINE Goal ==
           /\ earlyDelivery' = earlyDelivery
           /\ \/ UNCHANGED <<dispatchers, unauthorizedDispatch>>
              \/ \E replica \in Replicas, request \in RequestIds :
                    Dispatch(replica, request)
           /\ \/ UNCHANGED <<votes, selected, selectedByFallback>>
              \/ \E replica \in Replicas, request \in RequestIds,
                    payload \in Payloads :
                    SubmitVote(replica, request, payload)
              \/ \E replica \in Replicas, request \in RequestIds,
                    payload \in Payloads :
                    SelectByQuorum(replica, request, payload)
              \/ \E replica \in Replicas, request \in RequestIds,
                    payload \in Payloads :
                    TimeoutSelect(replica, request, payload)
<1> SUFFICES Goal
  OBVIOUS
<1>1. CASE SubmitVoteAction
  <2>1. PICK replica \in Replicas, request \in RequestIds,
             payload \in Payloads :
             SubmitVote(replica, request, payload)
    BY <1>1 DEF SubmitVoteAction
  <2>2. UNCHANGED <<dispatchers, unauthorizedDispatch, earlyDelivery>>
    BY <2>1 DEF SubmitVote
  <2> QED
    BY <2>1, <2>2
<1>2. CASE SelectAction
  <2>1. \/ \E replica \in Replicas, request \in RequestIds,
              payload \in Payloads :
              SelectByQuorum(replica, request, payload)
        \/ \E replica \in Replicas, request \in RequestIds,
              payload \in Payloads :
              TimeoutSelect(replica, request, payload)
    BY <1>2 DEF SelectAction
  <2>2. UNCHANGED <<dispatchers, unauthorizedDispatch, earlyDelivery>>
    BY <2>1 DEF SelectByQuorum, TimeoutSelect
  <2> QED
    BY <2>1, <2>2
<1>3. CASE DispatchAction
  <2>1. PICK replica \in Replicas, request \in RequestIds :
            Dispatch(replica, request)
    BY <1>3 DEF DispatchAction
  <2>2. UNCHANGED <<votes, selected, selectedByFallback, earlyDelivery>>
    BY <2>1 DEF Dispatch
  <2> QED
    BY <2>1, <2>2
<1>4. CASE ExternalRespondAction
  BY <1>4 DEF ExternalRespondAction, ExternalRespond
<1>5. CASE ProposeResponseAction
  BY <1>5 DEF ProposeResponseAction, ProposeResponse
<1>6. CASE DecideAction
  BY <1>6 DEF DecideAction, DecideOne, DecidePair
<1>7. CASE LearnAction
  BY <1>7 DEF LearnAction, LearnSlot
<1>8. CASE ProcessAction
  BY <1>8 DEF ProcessAction, ProcessContiguous
<1>9. CASE \E replica \in Replicas, slot \in 1..MaxSlots :
              ProcessNonContiguous(replica, slot)
  BY <1>9 DEF ProcessNonContiguous
<1>10. CASE \E replica \in Replicas, item \in ResponseItems :
               DeliverBeforeConsensus(replica, item)
  BY <1>10 DEF DeliverBeforeConsensus
<1>11. CASE \E replica \in Replicas : Crash(replica)
  BY <1>11 DEF Crash
<1>12. CASE \E replica \in Replicas : Recover(replica)
  BY <1>12 DEF Recover
<1>13. CASE \E replica \in Replicas : Elect(replica)
  BY <1>13 DEF Elect
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
  BY <1>16 DEF vars
<1> HIDE DEF Goal
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
     <1>11, <1>12, <1>13, <1>14, <1>15, <1>16 DEF Next

(***************************************************************************
Types of the three request-side functions. This is the part of TypeOK the
invariants below need; proving it here keeps them independent of the full
type invariant.
***************************************************************************)
RequestTypeOK ==
    /\ votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
    /\ selected \in [RequestIds -> Payloads \union {NoValue}]
    /\ dispatchers \in [RequestIds -> SUBSET Replicas]

LEMMA RequestTypeInit == Init => RequestTypeOK
BY DEF Init, RequestTypeOK

LEMMA RequestTypeStep ==
    ASSUME StrictDelivery
    PROVE  RequestTypeOK /\ [Next]_vars => RequestTypeOK'
<1> SUFFICES ASSUME RequestTypeOK, [Next]_vars
             PROVE  RequestTypeOK'
  OBVIOUS
<1>t. /\ votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
      /\ selected \in [RequestIds -> Payloads \union {NoValue}]
      /\ dispatchers \in [RequestIds -> SUBSET Replicas]
  BY DEF RequestTypeOK
<1>1. /\ votes' \in [RequestIds -> [Payloads -> SUBSET Replicas]]
      /\ selected' \in [RequestIds -> Payloads \union {NoValue}]
  <2>1. CASE UNCHANGED <<votes, selected, selectedByFallback>>
    BY <2>1, <1>t
  <2>2. ASSUME NEW replica \in Replicas, NEW request \in RequestIds,
               NEW payload \in Payloads,
               SubmitVote(replica, request, payload)
        PROVE  /\ votes' \in [RequestIds -> [Payloads -> SUBSET Replicas]]
               /\ selected' \in [RequestIds -> Payloads \union {NoValue}]
    <3>1. /\ votes' =
                [votes EXCEPT ![request][payload] = @ \union {replica}]
          /\ selected' = selected
      BY <2>2 DEF SubmitVote
    <3> QED
      BY <3>1, <1>t
  <2>3. ASSUME NEW replica \in Replicas, NEW request \in RequestIds,
               NEW payload \in Payloads,
               \/ SelectByQuorum(replica, request, payload)
               \/ TimeoutSelect(replica, request, payload)
        PROVE  /\ votes' \in [RequestIds -> [Payloads -> SUBSET Replicas]]
               /\ selected' \in [RequestIds -> Payloads \union {NoValue}]
    <3>1. /\ selected' = [selected EXCEPT ![request] = payload]
          /\ votes' = votes
      BY <2>3 DEF SelectByQuorum, TimeoutSelect
    <3> QED
      BY <3>1, <1>t
  <2> QED
    BY <2>1, <2>2, <2>3, StepEffects
<1>2. dispatchers' \in [RequestIds -> SUBSET Replicas]
  <2>1. CASE UNCHANGED <<dispatchers, unauthorizedDispatch>>
    BY <2>1, <1>t
  <2>2. ASSUME NEW replica \in Replicas, NEW request \in RequestIds,
               Dispatch(replica, request)
        PROVE  dispatchers' \in [RequestIds -> SUBSET Replicas]
    <3>1. dispatchers' =
              [dispatchers EXCEPT ![request] = @ \union {replica}]
      BY <2>2 DEF Dispatch
    <3> QED
      BY <3>1, <1>t
  <2> QED
    BY <2>1, <2>2, StepEffects
<1> QED
  BY <1>1, <1>2 DEF RequestTypeOK

LEMMA RequestTypeInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []RequestTypeOK
BY RequestTypeInit, RequestTypeStep, PTL DEF Spec

(***************************************************************************
Selection is justified by the callers' submissions.
***************************************************************************)
VotesFinite ==
    \A request \in RequestIds, payload \in Payloads :
        IsFiniteSet(votes[request][payload])

(* A request recorded as selected by fallback is selected. *)
FallbackSelected ==
    \A request \in RequestIds :
        request \in selectedByFallback => selected[request] # NoValue

SelectionInv ==
    /\ VotesFinite
    /\ FallbackSelected
    /\ SelectionJustified

LEMMA SelectionInit == Init => SelectionInv
<1> SUFFICES ASSUME Init PROVE SelectionInv
  OBVIOUS
<1>1. VotesFinite
  BY FS_EmptySet DEF Init, VotesFinite
<1>2. FallbackSelected
  BY DEF Init, FallbackSelected
<1>3. SelectionJustified
  BY DEF Init, SelectionJustified
<1> QED
  BY <1>1, <1>2, <1>3 DEF SelectionInv

(* Adding an element to a finite set does not shrink it. *)
LEMMA AddKeepsCardinality ==
    ASSUME NEW T, IsFiniteSet(T), NEW x
    PROVE  /\ IsFiniteSet(T \union {x})
           /\ Cardinality(T) \in Nat
           /\ Cardinality(T \union {x}) \in Nat
           /\ Cardinality(T \union {x}) >= Cardinality(T)
<1>1. Cardinality(T) \in Nat
  BY FS_CardinalityType
<1>2. /\ IsFiniteSet(T \union {x})
      /\ Cardinality(T \union {x}) =
            IF x \in T THEN Cardinality(T) ELSE Cardinality(T) + 1
  BY FS_AddElement
<1> QED
  BY <1>1, <1>2

(* A non-empty finite set has at least one element. *)
LEMMA NonEmptyCardinality ==
    ASSUME NEW T, IsFiniteSet(T), T # {}
    PROVE  Cardinality(T) >= 1
<1>1. Cardinality(T) \in Nat
  BY FS_CardinalityType
<1>2. Cardinality(T) # 0
  BY FS_EmptySet
<1> QED
  BY <1>1, <1>2

LEMMA QuorumIsNumber == Quorum \in Int
BY ConstantAssumptions

LEMMA SelectionStep ==
    ASSUME StrictDelivery, ~MutantNoQuorum
    PROVE  RequestTypeOK /\ SelectionInv /\ [Next]_vars => SelectionInv'
<1> SUFFICES ASSUME RequestTypeOK, SelectionInv, [Next]_vars
             PROVE  SelectionInv'
  OBVIOUS
<1>t. /\ votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
      /\ selected \in [RequestIds -> Payloads \union {NoValue}]
  BY DEF RequestTypeOK
<1>i. /\ VotesFinite
      /\ FallbackSelected
      /\ SelectionJustified
  BY DEF SelectionInv
<1>n. NoValue \notin Payloads
  BY ConstantAssumptions
<1>1. CASE UNCHANGED <<votes, selected, selectedByFallback>>
  BY <1>1, <1>i
     DEF SelectionInv, VotesFinite, FallbackSelected, SelectionJustified
<1>2. ASSUME NEW replica \in Replicas, NEW request \in RequestIds,
             NEW payload \in Payloads,
             SubmitVote(replica, request, payload)
      PROVE  SelectionInv'
  <2>1. /\ votes' = [votes EXCEPT ![request][payload] = @ \union {replica}]
        /\ selected' = selected
        /\ selectedByFallback' = selectedByFallback
    BY <1>2 DEF SubmitVote
  <2>2. \A q \in RequestIds, p \in Payloads :
            votes'[q][p] =
                IF q = request /\ p = payload
                THEN votes[q][p] \union {replica}
                ELSE votes[q][p]
    BY <2>1, <1>t
  <2>3. \A q \in RequestIds, p \in Payloads :
            /\ IsFiniteSet(votes'[q][p])
            /\ Cardinality(votes[q][p]) \in Nat
            /\ Cardinality(votes'[q][p]) \in Nat
            /\ Cardinality(votes'[q][p]) >= Cardinality(votes[q][p])
    <3> TAKE q \in RequestIds, p \in Payloads
    <3>1. IsFiniteSet(votes[q][p])
      BY <1>i DEF VotesFinite
    <3>2. CASE q = request /\ p = payload
      <4>1. votes'[q][p] = votes[q][p] \union {replica}
        BY <2>2, <3>2
      <4> QED
        BY <3>1, <4>1, AddKeepsCardinality
    <3>3. CASE ~(q = request /\ p = payload)
      <4>1. votes'[q][p] = votes[q][p]
        BY <2>2, <3>3
      <4>2. Cardinality(votes[q][p]) \in Nat
        BY <3>1, FS_CardinalityType
      <4> QED
        BY <3>1, <4>1, <4>2
    <3> QED
      BY <3>2, <3>3
  <2>4. VotesFinite'
    BY <2>3 DEF VotesFinite
  <2>5. FallbackSelected'
    BY <2>1, <1>i DEF FallbackSelected
  <2>6. SelectionJustified'
    <3> SUFFICES ASSUME NEW q \in RequestIds, selected[q] # NoValue
                 PROVE  IF q \in selectedByFallback
                        THEN Cardinality(votes'[q][selected[q]]) >= 1
                        ELSE Cardinality(votes'[q][selected[q]]) >= Quorum
      BY <2>1 DEF SelectionJustified
    <3>1. selected[q] \in Payloads
      BY <1>t
    <3>2. IF q \in selectedByFallback
          THEN Cardinality(votes[q][selected[q]]) >= 1
          ELSE Cardinality(votes[q][selected[q]]) >= Quorum
      BY <1>i DEF SelectionJustified
    <3>3. /\ Cardinality(votes[q][selected[q]]) \in Nat
          /\ Cardinality(votes'[q][selected[q]]) \in Nat
          /\ Cardinality(votes'[q][selected[q]]) >=
                Cardinality(votes[q][selected[q]])
      BY <2>3, <3>1
    <3> QED
      BY <3>2, <3>3, QuorumIsNumber
  <2> QED
    BY <2>4, <2>5, <2>6 DEF SelectionInv
<1>3. ASSUME NEW replica \in Replicas, NEW request \in RequestIds,
             NEW payload \in Payloads,
             SelectByQuorum(replica, request, payload)
      PROVE  SelectionInv'
  <2>1. /\ selected[request] = NoValue
        /\ Cardinality(votes[request][payload]) >= Quorum
        /\ selected' = [selected EXCEPT ![request] = payload]
        /\ votes' = votes
        /\ selectedByFallback' = selectedByFallback
    BY <1>3 DEF SelectByQuorum
  <2>2. \A q \in RequestIds :
            selected'[q] = IF q = request THEN payload ELSE selected[q]
    BY <2>1, <1>t
  <2>3. request \notin selectedByFallback
    BY <2>1, <1>i DEF FallbackSelected
  <2>4. VotesFinite'
    BY <2>1, <1>i DEF VotesFinite
  <2>5. FallbackSelected'
    BY <2>1, <2>2, <1>i, <1>n DEF FallbackSelected
  <2>6. SelectionJustified'
    <3> SUFFICES ASSUME NEW q \in RequestIds, selected'[q] # NoValue
                 PROVE  IF q \in selectedByFallback
                        THEN Cardinality(votes[q][selected'[q]]) >= 1
                        ELSE Cardinality(votes[q][selected'[q]]) >= Quorum
      BY <2>1 DEF SelectionJustified
    <3>1. CASE q = request
      BY <3>1, <2>1, <2>2, <2>3
    <3>2. CASE q # request
      <4>1. selected'[q] = selected[q]
        BY <3>2, <2>2
      <4> QED
        BY <4>1, <1>i DEF SelectionJustified
    <3> QED
      BY <3>1, <3>2
  <2> QED
    BY <2>4, <2>5, <2>6 DEF SelectionInv
<1>4. ASSUME NEW replica \in Replicas, NEW request \in RequestIds,
             NEW payload \in Payloads,
             TimeoutSelect(replica, request, payload)
      PROVE  SelectionInv'
  <2>1. /\ selected[request] = NoValue
        /\ votes[request][payload] # {}
        /\ selected' = [selected EXCEPT ![request] = payload]
        /\ selectedByFallback' = selectedByFallback \union {request}
        /\ votes' = votes
    BY <1>4 DEF TimeoutSelect
  <2>2. \A q \in RequestIds :
            selected'[q] = IF q = request THEN payload ELSE selected[q]
    BY <2>1, <1>t
  <2>3. Cardinality(votes[request][payload]) >= 1
    <3>1. IsFiniteSet(votes[request][payload])
      BY <1>i DEF VotesFinite
    <3> QED
      BY <3>1, <2>1, NonEmptyCardinality
  <2>4. VotesFinite'
    BY <2>1, <1>i DEF VotesFinite
  <2>5. FallbackSelected'
    BY <2>1, <2>2, <1>i, <1>n DEF FallbackSelected
  <2>6. SelectionJustified'
    <3> SUFFICES ASSUME NEW q \in RequestIds, selected'[q] # NoValue
                 PROVE  IF q \in selectedByFallback'
                        THEN Cardinality(votes[q][selected'[q]]) >= 1
                        ELSE Cardinality(votes[q][selected'[q]]) >= Quorum
      BY <2>1 DEF SelectionJustified
    <3>1. CASE q = request
      BY <3>1, <2>1, <2>2, <2>3
    <3>2. CASE q # request
      <4>1. selected'[q] = selected[q]
        BY <3>2, <2>2
      <4>2. q \in selectedByFallback' <=> q \in selectedByFallback
        BY <3>2, <2>1
      <4> QED
        BY <4>1, <4>2, <1>i DEF SelectionJustified
    <3> QED
      BY <3>1, <3>2
  <2> QED
    BY <2>4, <2>5, <2>6 DEF SelectionInv
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, StepEffects

THEOREM SelectionJustifiedInvariant ==
    ASSUME StrictDelivery, ~MutantNoQuorum
    PROVE  Spec => []SelectionJustified
<1>1. Init => SelectionInv
  BY SelectionInit
<1>2. RequestTypeOK /\ SelectionInv /\ [Next]_vars => SelectionInv'
  BY SelectionStep
<1>3. Spec => []RequestTypeOK
  BY RequestTypeInvariant
<1>4. SelectionInv => SelectionJustified
  BY DEF SelectionInv
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

(***************************************************************************
With the timeout fallback off, every selection has a quorum.
***************************************************************************)
THEOREM StrictQuorumOnlyInvariant ==
    ASSUME StrictDelivery, ~EnableTimeoutFallback
    PROVE  Spec => []StrictQuorumOnly
<1>1. Init => StrictQuorumOnly
  BY DEF Init, StrictQuorumOnly
<1>2. StrictQuorumOnly /\ [Next]_vars => StrictQuorumOnly'
  <2> SUFFICES ASSUME StrictQuorumOnly, [Next]_vars
               PROVE  StrictQuorumOnly'
    OBVIOUS
  <2>1. \/ UNCHANGED <<votes, selected, selectedByFallback>>
        \/ \E replica \in Replicas, request \in RequestIds,
              payload \in Payloads :
              SubmitVote(replica, request, payload)
        \/ \E replica \in Replicas, request \in RequestIds,
              payload \in Payloads :
              SelectByQuorum(replica, request, payload)
        \/ \E replica \in Replicas, request \in RequestIds,
              payload \in Payloads :
              TimeoutSelect(replica, request, payload)
    BY StepEffects
  <2>2. selectedByFallback' = selectedByFallback
    BY <2>1 DEF SubmitVote, SelectByQuorum, TimeoutSelect
  <2> QED
    BY <2>2 DEF StrictQuorumOnly
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************
Only the leader dispatches (paper Section 4.2).
***************************************************************************)
THEOREM OnlyAuthorizedDispatchInvariant ==
    ASSUME StrictDelivery, ~MutantAllDispatch
    PROVE  Spec => []OnlyAuthorizedDispatch
<1>1. Init => OnlyAuthorizedDispatch
  BY DEF Init, OnlyAuthorizedDispatch
<1>2. OnlyAuthorizedDispatch /\ [Next]_vars => OnlyAuthorizedDispatch'
  <2> SUFFICES ASSUME OnlyAuthorizedDispatch, [Next]_vars
               PROVE  OnlyAuthorizedDispatch'
    OBVIOUS
  <2>1. \/ UNCHANGED <<dispatchers, unauthorizedDispatch>>
        \/ \E replica \in Replicas, request \in RequestIds :
              Dispatch(replica, request)
    BY StepEffects
  <2>2. CASE UNCHANGED <<dispatchers, unauthorizedDispatch>>
    BY <2>2 DEF OnlyAuthorizedDispatch
  <2>3. ASSUME NEW replica \in Replicas, NEW request \in RequestIds,
               Dispatch(replica, request)
        PROVE  OnlyAuthorizedDispatch'
    <3>1. /\ replica = leader
          /\ unauthorizedDispatch' =
                (unauthorizedDispatch \/ (replica # leader))
      BY <2>3 DEF Dispatch
    <3> QED
      BY <3>1 DEF OnlyAuthorizedDispatch
  <2> QED
    BY <2>1, <2>2, <2>3
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************
At-most-once physical dispatch while the leader is stable.
***************************************************************************)
SingleDispatch ==
    \A request \in RequestIds :
        \A a, b \in dispatchers[request] : a = b

THEOREM AtMostOnePhysicalDispatchInvariant ==
    ASSUME StrictDelivery, ~MutantAllDispatch, ~EnableCrashes
    PROVE  Spec => []AtMostOnePhysicalDispatch
<1>1. Init => SingleDispatch
  BY DEF Init, SingleDispatch
<1>2. RequestTypeOK /\ SingleDispatch /\ [Next]_vars => SingleDispatch'
  <2> SUFFICES ASSUME RequestTypeOK, SingleDispatch, [Next]_vars
               PROVE  SingleDispatch'
    OBVIOUS
  <2>1. dispatchers \in [RequestIds -> SUBSET Replicas]
    BY DEF RequestTypeOK
  <2>2. CASE UNCHANGED <<dispatchers, unauthorizedDispatch>>
    BY <2>2 DEF SingleDispatch
  <2>3. ASSUME NEW replica \in Replicas, NEW request \in RequestIds,
               Dispatch(replica, request)
        PROVE  SingleDispatch'
    <3>1. /\ dispatchers[request] = {}
          /\ dispatchers' =
                [dispatchers EXCEPT ![request] = @ \union {replica}]
      BY <2>3 DEF Dispatch
    <3>2. \A q \in RequestIds :
              dispatchers'[q] =
                  IF q = request THEN {replica} ELSE dispatchers[q]
      BY <3>1, <2>1
    <3> QED
      BY <3>2 DEF SingleDispatch
  <2> QED
    BY <2>2, <2>3, StepEffects
<1>3. Spec => []RequestTypeOK
  BY RequestTypeInvariant
<1>4. SingleDispatch => AtMostOnePhysicalDispatch
  <2> SUFFICES ASSUME SingleDispatch, NEW request \in RequestIds
               PROVE  Cardinality(dispatchers[request]) <= 1
    BY DEF AtMostOnePhysicalDispatch
  <2>1. \A a, b \in dispatchers[request] : a = b
    BY DEF SingleDispatch
  <2> QED
    BY <2>1, AtMostOneElement
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

(***************************************************************************
No response is delivered before consensus agrees on it.
***************************************************************************)
THEOREM NoEarlyDeliveryInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []NoEarlyDelivery
<1>1. Init => NoEarlyDelivery
  BY DEF Init, NoEarlyDelivery
<1>2. NoEarlyDelivery /\ [Next]_vars => NoEarlyDelivery'
  BY StepEffects DEF NoEarlyDelivery
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************
Type invariant.
***************************************************************************)
LEMMA BatchTypes ==
    /\ \A item \in ResponseItems : <<item>> \in BatchType
    /\ EnableBatching =>
         \A first, second \in ResponseItems :
            <<first, second>> \in BatchType
    /\ BatchType \subseteq Seq(ResponseItems)
<1>1. \A item \in ResponseItems : <<item>> \in BatchType
  BY DEF BatchType, SingleBatches
<1>2. EnableBatching =>
        \A first, second \in ResponseItems :
            <<first, second>> \in BatchType
  <2> SUFFICES ASSUME EnableBatching,
                      NEW first \in ResponseItems,
                      NEW second \in ResponseItems
               PROVE  <<first, second>> \in BatchType
    OBVIOUS
  <2>1. <<first, second>> \in DoubleBatches
    BY DEF DoubleBatches
  <2>2. BatchType = SingleBatches \union DoubleBatches
    BY DEF BatchType
  <2> QED
    BY <2>1, <2>2
<1>3. BatchType \subseteq Seq(ResponseItems)
  <2>1. SingleBatches \subseteq Seq(ResponseItems)
    BY DEF SingleBatches
  <2>2. DoubleBatches \subseteq Seq(ResponseItems)
    <3>1. \A first, second \in ResponseItems :
              <<first, second>> \in Seq(ResponseItems)
      OBVIOUS
    <3> SUFFICES ASSUME NEW batch \in DoubleBatches
                 PROVE  batch \in Seq(ResponseItems)
      OBVIOUS
    <3>2. PICK first \in ResponseItems, second \in ResponseItems :
              batch = <<first, second>>
      BY DEF DoubleBatches
    <3> QED
      BY <3>1, <3>2
  <2> QED
    BY <2>1, <2>2 DEF BatchType
<1> QED
  BY <1>1, <1>2, <1>3

LEMMA TypeInit == Init => TypeOK
<1> SUFFICES ASSUME Init PROVE TypeOK
  OBVIOUS
<1>1. MaxSlots \in Nat
  BY ConstantAssumptions
<1>2. consensusLog \in Seq(BatchType) /\ Len(consensusLog) <= MaxSlots
  BY <1>1 DEF Init
<1>3. processed \in [Replicas -> 0..MaxSlots]
  BY <1>1 DEF Init
<1> QED
  BY <1>2, <1>3 DEF Init, TypeOK

LEMMA TypeStep ==
    ASSUME StrictDelivery
    PROVE  TypeOK /\ [Next]_vars => TypeOK'
<1> SUFFICES ASSUME TypeOK, [Next]_vars
             PROVE  TypeOK'
  OBVIOUS
<1> USE DEF StrictDelivery
<1>t. /\ leader \in Replicas \union {NoNode}
      /\ up \subseteq Replicas
      /\ votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
      /\ selected \in [RequestIds -> Payloads \union {NoValue}]
      /\ selectedByFallback \subseteq RequestIds
      /\ dispatchers \in [RequestIds -> SUBSET Replicas]
      /\ execResponse \in
            [RequestIds -> [Replicas -> Responses \union {NoValue}]]
      /\ observed \subseteq ResponseItems
      /\ proposed \subseteq ResponseItems
      /\ consensusLog \in Seq(BatchType)
      /\ Len(consensusLog) <= MaxSlots
      /\ learned \in [Replicas -> SUBSET (1..MaxSlots)]
      /\ processed \in [Replicas -> 0..MaxSlots]
      /\ delivered \in [Replicas -> Seq(ResponseItems)]
      /\ seen \in [Replicas -> SUBSET RequestIds]
      /\ unauthorizedDispatch \in BOOLEAN
      /\ earlyDelivery \in BOOLEAN
  BY DEF TypeOK
<1>m. MaxSlots \in Nat
  BY ConstantAssumptions
<1>1. CASE SubmitVoteAction
  <2>1. PICK replica \in Replicas, request \in RequestIds,
             payload \in Payloads :
             SubmitVote(replica, request, payload)
    BY <1>1 DEF SubmitVoteAction
  <2>2. votes' = [votes EXCEPT ![request][payload] = @ \union {replica}]
    BY <2>1 DEF SubmitVote
  <2>3. votes' \in [RequestIds -> [Payloads -> SUBSET Replicas]]
    BY <2>2, <1>t
  <2>4. UNCHANGED <<leader, up, selected, selectedByFallback, dispatchers,
                    execResponse, observed, proposed, consensusLog,
                    learned, processed, delivered, seen,
                    unauthorizedDispatch, earlyDelivery>>
    BY <2>1 DEF SubmitVote
  <2> QED
    BY <2>3, <2>4, <1>t DEF TypeOK
<1>2. CASE SelectAction
  <2>1. PICK request \in RequestIds, payload \in Payloads :
            /\ selected' = [selected EXCEPT ![request] = payload]
            /\ \/ selectedByFallback' = selectedByFallback
               \/ selectedByFallback' = selectedByFallback \union {request}
            /\ UNCHANGED <<leader, up, votes, dispatchers, execResponse,
                           observed, proposed, consensusLog, learned,
                           processed, delivered, seen,
                           unauthorizedDispatch, earlyDelivery>>
    BY <1>2 DEF SelectAction, SelectByQuorum, TimeoutSelect
  <2>2. selected' \in [RequestIds -> Payloads \union {NoValue}]
    BY <2>1, <1>t
  <2>3. selectedByFallback' \subseteq RequestIds
    BY <2>1, <1>t
  <2> QED
    BY <2>1, <2>2, <2>3, <1>t DEF TypeOK
<1>3. CASE DispatchAction
  <2>1. PICK replica \in Replicas, request \in RequestIds :
            Dispatch(replica, request)
    BY <1>3 DEF DispatchAction
  <2>2. dispatchers' = [dispatchers EXCEPT ![request] = @ \union {replica}]
    BY <2>1 DEF Dispatch
  <2>3. dispatchers' \in [RequestIds -> SUBSET Replicas]
    BY <2>2, <1>t
  <2>4. unauthorizedDispatch' \in BOOLEAN
    BY <2>1, <1>t DEF Dispatch
  <2>5. UNCHANGED <<leader, up, votes, selected, selectedByFallback,
                    execResponse, observed, proposed, consensusLog,
                    learned, processed, delivered, seen, earlyDelivery>>
    BY <2>1 DEF Dispatch
  <2> QED
    BY <2>3, <2>4, <2>5, <1>t DEF TypeOK
<1>4. CASE ExternalRespondAction
  <2>1. PICK replica \in Replicas, request \in RequestIds,
             responseValue \in Responses :
             ExternalRespond(replica, request, responseValue)
    BY <1>4 DEF ExternalRespondAction
  <2>2. execResponse' =
            [execResponse EXCEPT ![request][replica] = responseValue]
    BY <2>1 DEF ExternalRespond
  <2>3. execResponse' \in
            [RequestIds -> [Replicas -> Responses \union {NoValue}]]
    BY <2>2, <1>t
  <2>4. ObservedItem(request, responseValue) \in ResponseItems
    BY DEF ObservedItem, ResponseItems
  <2>5. observed' \subseteq ResponseItems
    BY <2>1, <2>4, <1>t DEF ExternalRespond
  <2>6. UNCHANGED <<leader, up, votes, selected, selectedByFallback,
                    dispatchers, proposed, consensusLog, learned,
                    processed, delivered, seen, unauthorizedDispatch,
                    earlyDelivery>>
    BY <2>1 DEF ExternalRespond
  <2> QED
    BY <2>3, <2>5, <2>6, <1>t DEF TypeOK
<1>5. CASE ProposeResponseAction
  <2>1. PICK replica \in Replicas, request \in RequestIds,
             responseValue \in Responses :
             ProposeResponse(replica, request, responseValue)
    BY <1>5 DEF ProposeResponseAction
  <2>2. ObservedItem(request, responseValue) \in ResponseItems
    BY DEF ObservedItem, ResponseItems
  <2>3. proposed' \subseteq ResponseItems
    BY <2>1, <2>2, <1>t DEF ProposeResponse
  <2>4. UNCHANGED <<leader, up, votes, selected, selectedByFallback,
                    dispatchers, execResponse, observed, consensusLog,
                    learned, processed, delivered, seen,
                    unauthorizedDispatch, earlyDelivery>>
    BY <2>1 DEF ProposeResponse
  <2> QED
    BY <2>3, <2>4, <1>t DEF TypeOK
<1>6. CASE DecideAction
  <2>1. PICK batch \in BatchType :
            /\ Len(consensusLog) < MaxSlots
            /\ consensusLog' = Append(consensusLog, batch)
            /\ UNCHANGED <<leader, up, votes, selected, selectedByFallback,
                           dispatchers, execResponse, observed, proposed,
                           learned, processed, delivered, seen,
                           unauthorizedDispatch, earlyDelivery>>
    <3>1. ASSUME NEW item \in ResponseItems, DecideOne(item)
          PROVE  \E batch \in BatchType :
                    /\ Len(consensusLog) < MaxSlots
                    /\ consensusLog' = Append(consensusLog, batch)
                    /\ UNCHANGED <<leader, up, votes, selected,
                                   selectedByFallback, dispatchers,
                                   execResponse, observed, proposed,
                                   learned, processed, delivered, seen,
                                   unauthorizedDispatch, earlyDelivery>>
      <4>1. <<item>> \in BatchType
        BY BatchTypes
      <4> QED
        BY <3>1, <4>1 DEF DecideOne
    <3>2. ASSUME NEW first \in ResponseItems, NEW second \in ResponseItems,
                 DecidePair(first, second)
          PROVE  \E batch \in BatchType :
                    /\ Len(consensusLog) < MaxSlots
                    /\ consensusLog' = Append(consensusLog, batch)
                    /\ UNCHANGED <<leader, up, votes, selected,
                                   selectedByFallback, dispatchers,
                                   execResponse, observed, proposed,
                                   learned, processed, delivered, seen,
                                   unauthorizedDispatch, earlyDelivery>>
      <4>1. <<first, second>> \in BatchType
        BY <3>2, BatchTypes DEF DecidePair
      <4> QED
        BY <3>2, <4>1 DEF DecidePair
    <3> QED
      BY <1>6, <3>1, <3>2 DEF DecideAction
  <2>2. Len(consensusLog) \in Nat
    BY <1>t
  <2>3. /\ consensusLog' \in Seq(BatchType)
        /\ Len(consensusLog') = Len(consensusLog) + 1
    BY <2>1, <1>t
  <2>4. Len(consensusLog') <= MaxSlots
    BY <2>1, <2>2, <2>3, <1>m
  <2> QED
    BY <2>1, <2>3, <2>4, <1>t DEF TypeOK
<1>7. CASE LearnAction
  <2>1. PICK replica \in Replicas, slot \in 1..MaxSlots :
            LearnSlot(replica, slot)
    BY <1>7 DEF LearnAction
  <2>2. learned' = [learned EXCEPT ![replica] = @ \union {slot}]
    BY <2>1 DEF LearnSlot
  <2>3. learned' \in [Replicas -> SUBSET (1..MaxSlots)]
    BY <2>2, <1>t
  <2>4. UNCHANGED <<leader, up, votes, selected, selectedByFallback,
                    dispatchers, execResponse, observed, proposed,
                    consensusLog, processed, delivered, seen,
                    unauthorizedDispatch, earlyDelivery>>
    BY <2>1 DEF LearnSlot
  <2> QED
    BY <2>3, <2>4, <1>t DEF TypeOK
<1>8. CASE ProcessAction
  <2>1. PICK replica \in Replicas : ProcessContiguous(replica)
    BY <1>8 DEF ProcessAction
  <2> DEFINE slot == processed[replica] + 1
             batch == consensusLog[slot]
             result == ApplyItems(batch, seen[replica], delivered[replica])
  <2>2. /\ slot \in 1..Len(consensusLog)
        /\ processed' = [processed EXCEPT ![replica] = slot]
        /\ seen' = [seen EXCEPT ![replica] = result.seen]
        /\ delivered' = [delivered EXCEPT ![replica] = result.output]
        /\ UNCHANGED <<leader, up, votes, selected, selectedByFallback,
                       dispatchers, execResponse, observed, proposed,
                       consensusLog, learned, unauthorizedDispatch,
                       earlyDelivery>>
    BY <2>1 DEF ProcessContiguous
  <2>3. Len(consensusLog) \in Nat
    BY <1>t
  <2>4. batch \in BatchType
    BY <2>2, <2>3, <1>t
  <2>5. batch \in Seq(ResponseItems)
    BY <2>4, BatchTypes
  <2>6. delivered[replica] \in Seq(ResponseItems)
    BY <1>t
  <2>7. AppliedCorrectly(ResponseItems, batch, seen[replica],
                         delivered[replica], result)
    BY <2>5, <2>6, ApplyItemsCorrect
  <2>8. result.output \in Seq(ResponseItems)
    BY <2>7 DEF AppliedCorrectly
  <2>9. result.seen =
            seen[replica] \union {batch[k].rid : k \in 1..Len(batch)}
    BY <2>7 DEF AppliedCorrectly
  <2>10. \A k \in 1..Len(batch) : batch[k].rid \in RequestIds
    BY <2>5 DEF ResponseItems
  <2>11. result.seen \subseteq RequestIds
    BY <2>9, <2>10, <1>t
  <2>12. slot \in 0..MaxSlots
    BY <2>2, <2>3, <1>t, <1>m
  <2> HIDE DEF slot, batch, result
  <2>13. processed' \in [Replicas -> 0..MaxSlots]
    BY <2>2, <2>12, <1>t
  <2>14. seen' \in [Replicas -> SUBSET RequestIds]
    BY <2>2, <2>11, <1>t
  <2>15. delivered' \in [Replicas -> Seq(ResponseItems)]
    BY <2>2, <2>8, <1>t
  <2> QED
    BY <2>2, <2>13, <2>14, <2>15, <1>t DEF TypeOK
<1>9. CASE \E replica \in Replicas, slot \in 1..MaxSlots :
              ProcessNonContiguous(replica, slot)
  BY <1>9 DEF ProcessNonContiguous
<1>10. CASE \E replica \in Replicas, item \in ResponseItems :
               DeliverBeforeConsensus(replica, item)
  BY <1>10 DEF DeliverBeforeConsensus
<1>11. CASE \E replica \in Replicas : Crash(replica)
  <2>1. PICK replica \in Replicas : Crash(replica)
    BY <1>11
  <2>2. /\ up' = up \ {replica}
        /\ leader' = IF leader = replica THEN NoNode ELSE leader
        /\ UNCHANGED <<votes, selected, selectedByFallback, dispatchers,
                       execResponse, observed, proposed, consensusLog,
                       learned, processed, delivered, seen,
                       unauthorizedDispatch, earlyDelivery>>
    BY <2>1 DEF Crash
  <2>3. up' \subseteq Replicas /\ leader' \in Replicas \union {NoNode}
    BY <2>2, <1>t
  <2> QED
    BY <2>2, <2>3, <1>t DEF TypeOK
<1>12. CASE \E replica \in Replicas : Recover(replica)
  <2>1. PICK replica \in Replicas : Recover(replica)
    BY <1>12
  <2>2. /\ up' = up \union {replica}
        /\ UNCHANGED <<leader, votes, selected, selectedByFallback,
                       dispatchers, execResponse, observed, proposed,
                       consensusLog, learned, processed, delivered, seen,
                       unauthorizedDispatch, earlyDelivery>>
    BY <2>1 DEF Recover
  <2>3. up' \subseteq Replicas
    BY <2>2, <1>t
  <2> QED
    BY <2>2, <2>3, <1>t DEF TypeOK
<1>13. CASE \E replica \in Replicas : Elect(replica)
  <2>1. PICK replica \in Replicas : Elect(replica)
    BY <1>13
  <2>2. /\ leader' = replica
        /\ UNCHANGED <<up, votes, selected, selectedByFallback,
                       dispatchers, execResponse, observed, proposed,
                       consensusLog, learned, processed, delivered, seen,
                       unauthorizedDispatch, earlyDelivery>>
    BY <2>1 DEF Elect
  <2> QED
    BY <2>2, <1>t DEF TypeOK
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
  BY <1>16, <1>t DEF vars, TypeOK
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
     <1>11, <1>12, <1>13, <1>14, <1>15, <1>16 DEF Next

THEOREM TypeOKInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []TypeOK
BY TypeInit, TypeStep, PTL DEF Spec
=============================================================================

------------------------- MODULE ResdetLiveTermination -------------------------
(***************************************************************************
TLAPS liveness proof, part 4 of 5: every behavior eventually stops
changing.

Under LivenessAssumptions each step of Spec does one unit of work that is
never undone (a vote, a selection, a dispatch, a response, a proposal, an
agreed slot, a learned index, a processed index), and the total amount of
work is bounded by the constants. So only finitely many steps change the
state. This uses no fairness.
***************************************************************************)
EXTENDS ResdetLiveInv

(***************************************************************************
The work done so far, as eight sets. Each is a subset of a constant finite
universe in every state, by its definition alone.
***************************************************************************)
PairVR == Replicas \X RequestIds
PairQR == RequestIds \X Replicas
SlotSet == 1..MaxSlots
PairRS == Replicas \X SlotSet

VotedPairs == {p \in PairVR : HasVoted(p[1], p[2])}
SelectedRids == {q \in RequestIds : selected[q] # NoValue}
DispatchedRids == {q \in RequestIds : dispatchers[q] # {}}
RespondedPairs == {p \in PairQR : execResponse[p[1]][p[2]] # NoValue}
ProposedRids == {q \in RequestIds : \E item \in proposed : item.rid = q}
UsedSlots == {s \in SlotSet : s <= Len(consensusLog)}
LearnedPairs == {p \in PairRS : p[2] \in learned[p[1]]}
ProcessedPairs == {p \in PairRS : p[2] <= processed[p[1]]}

Sum8(d1, d2, d3, d4, d5, d6, d7, d8) ==
    Cardinality(d1) + Cardinality(d2) + Cardinality(d3) + Cardinality(d4)
    + Cardinality(d5) + Cardinality(d6) + Cardinality(d7) + Cardinality(d8)

Work ==
    Sum8(VotedPairs, SelectedRids, DispatchedRids, RespondedPairs,
         ProposedRids, UsedSlots, LearnedPairs, ProcessedPairs)

(* A constant: the most work any behavior can do. *)
WorkBound ==
    Sum8(PairVR, RequestIds, RequestIds, PairQR,
         RequestIds, SlotSet, PairRS, PairRS)

Remaining == WorkBound - Work

(***************************************************************************
Counting facts.
***************************************************************************)
LEMMA SubCard ==
    ASSUME NEW E, IsFiniteSet(E), NEW D, D \subseteq E
    PROVE  /\ Cardinality(D) \in Nat
           /\ Cardinality(E) \in Nat
           /\ Cardinality(D) <= Cardinality(E)
           /\ D # E => Cardinality(D) < Cardinality(E)
<1>1. D \in SUBSET E
  OBVIOUS
<1>2. IsFiniteSet(D)
  BY <1>1, FS_Subset
<1>3. Cardinality(D) \in Nat /\ Cardinality(E) \in Nat
  BY <1>2, FS_CardinalityType
<1>4. /\ Cardinality(D) <= Cardinality(E)
      /\ Cardinality(E) = Cardinality(D) => E = D
  BY <1>1, FS_Subset
<1> QED
  BY <1>3, <1>4

(* Arithmetic only: adding one more pair of naturals keeps the order. *)
LEMMA AddMono ==
    ASSUME NEW s \in Nat, NEW t \in Nat, NEW a \in Nat, NEW b \in Nat,
           s <= t, a <= b
    PROVE  /\ s + a \in Nat
           /\ t + b \in Nat
           /\ s + a <= t + b
           /\ (s < t \/ a < b) => s + a < t + b
OBVIOUS

(* Eight naturals, each at most its partner. *)
LEMMA SumArith ==
    ASSUME NEW a1 \in Nat, NEW a2 \in Nat, NEW a3 \in Nat, NEW a4 \in Nat,
           NEW a5 \in Nat, NEW a6 \in Nat, NEW a7 \in Nat, NEW a8 \in Nat,
           NEW b1 \in Nat, NEW b2 \in Nat, NEW b3 \in Nat, NEW b4 \in Nat,
           NEW b5 \in Nat, NEW b6 \in Nat, NEW b7 \in Nat, NEW b8 \in Nat,
           a1 <= b1, a2 <= b2, a3 <= b3, a4 <= b4,
           a5 <= b5, a6 <= b6, a7 <= b7, a8 <= b8
    PROVE  /\ a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 \in Nat
           /\ b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 \in Nat
           /\ a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8
                <= b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8
           /\ (\/ a1 < b1 \/ a2 < b2 \/ a3 < b3 \/ a4 < b4
               \/ a5 < b5 \/ a6 < b6 \/ a7 < b7 \/ a8 < b8)
                => a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8
                     < b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8
<1> DEFINE s2 == a1 + a2   t2 == b1 + b2
           s3 == s2 + a3   t3 == t2 + b3
           s4 == s3 + a4   t4 == t3 + b4
           s5 == s4 + a5   t5 == t4 + b5
           s6 == s5 + a6   t6 == t5 + b6
           s7 == s6 + a7   t7 == t6 + b7
           s8 == s7 + a8   t8 == t7 + b8
<1>2. /\ s2 \in Nat /\ t2 \in Nat /\ s2 <= t2
      /\ (a1 < b1 \/ a2 < b2) => s2 < t2
  BY AddMono
<1> HIDE DEF s2, t2
<1>3. /\ s3 \in Nat /\ t3 \in Nat /\ s3 <= t3
      /\ (s2 < t2 \/ a3 < b3) => s3 < t3
  BY <1>2, AddMono
<1> HIDE DEF s3, t3
<1>4. /\ s4 \in Nat /\ t4 \in Nat /\ s4 <= t4
      /\ (s3 < t3 \/ a4 < b4) => s4 < t4
  BY <1>3, AddMono
<1> HIDE DEF s4, t4
<1>5. /\ s5 \in Nat /\ t5 \in Nat /\ s5 <= t5
      /\ (s4 < t4 \/ a5 < b5) => s5 < t5
  BY <1>4, AddMono
<1> HIDE DEF s5, t5
<1>6. /\ s6 \in Nat /\ t6 \in Nat /\ s6 <= t6
      /\ (s5 < t5 \/ a6 < b6) => s6 < t6
  BY <1>5, AddMono
<1> HIDE DEF s6, t6
<1>7. /\ s7 \in Nat /\ t7 \in Nat /\ s7 <= t7
      /\ (s6 < t6 \/ a7 < b7) => s7 < t7
  BY <1>6, AddMono
<1> HIDE DEF s7, t7
<1>8. /\ s8 \in Nat /\ t8 \in Nat /\ s8 <= t8
      /\ (s7 < t7 \/ a8 < b8) => s8 < t8
  BY <1>7, AddMono
<1> HIDE DEF s8, t8
<1>9. /\ s8 \in Nat /\ t8 \in Nat /\ s8 <= t8
      /\ (\/ a1 < b1 \/ a2 < b2 \/ a3 < b3 \/ a4 < b4
          \/ a5 < b5 \/ a6 < b6 \/ a7 < b7 \/ a8 < b8) => s8 < t8
  BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
<1> QED
  BY <1>9 DEF s2, t2, s3, t3, s4, t4, s5, t5, s6, t6, s7, t7, s8, t8

LEMMA Sum8Mono ==
    ASSUME NEW d1, NEW d2, NEW d3, NEW d4, NEW d5, NEW d6, NEW d7, NEW d8,
           NEW e1, NEW e2, NEW e3, NEW e4, NEW e5, NEW e6, NEW e7, NEW e8,
           IsFiniteSet(e1), IsFiniteSet(e2), IsFiniteSet(e3),
           IsFiniteSet(e4), IsFiniteSet(e5), IsFiniteSet(e6),
           IsFiniteSet(e7), IsFiniteSet(e8),
           d1 \subseteq e1, d2 \subseteq e2, d3 \subseteq e3,
           d4 \subseteq e4, d5 \subseteq e5, d6 \subseteq e6,
           d7 \subseteq e7, d8 \subseteq e8
    PROVE  /\ Sum8(d1, d2, d3, d4, d5, d6, d7, d8) \in Nat
           /\ Sum8(e1, e2, e3, e4, e5, e6, e7, e8) \in Nat
           /\ Sum8(d1, d2, d3, d4, d5, d6, d7, d8)
                <= Sum8(e1, e2, e3, e4, e5, e6, e7, e8)
           /\ (\/ d1 # e1 \/ d2 # e2 \/ d3 # e3 \/ d4 # e4
               \/ d5 # e5 \/ d6 # e6 \/ d7 # e7 \/ d8 # e8)
                => Sum8(d1, d2, d3, d4, d5, d6, d7, d8)
                     < Sum8(e1, e2, e3, e4, e5, e6, e7, e8)
<1> DEFINE a1 == Cardinality(d1)  b1 == Cardinality(e1)
           a2 == Cardinality(d2)  b2 == Cardinality(e2)
           a3 == Cardinality(d3)  b3 == Cardinality(e3)
           a4 == Cardinality(d4)  b4 == Cardinality(e4)
           a5 == Cardinality(d5)  b5 == Cardinality(e5)
           a6 == Cardinality(d6)  b6 == Cardinality(e6)
           a7 == Cardinality(d7)  b7 == Cardinality(e7)
           a8 == Cardinality(d8)  b8 == Cardinality(e8)
<1>1. a1 \in Nat /\ b1 \in Nat /\ a1 <= b1 /\ (d1 # e1 => a1 < b1)
  BY SubCard
<1>2. a2 \in Nat /\ b2 \in Nat /\ a2 <= b2 /\ (d2 # e2 => a2 < b2)
  BY SubCard
<1>3. a3 \in Nat /\ b3 \in Nat /\ a3 <= b3 /\ (d3 # e3 => a3 < b3)
  BY SubCard
<1>4. a4 \in Nat /\ b4 \in Nat /\ a4 <= b4 /\ (d4 # e4 => a4 < b4)
  BY SubCard
<1>5. a5 \in Nat /\ b5 \in Nat /\ a5 <= b5 /\ (d5 # e5 => a5 < b5)
  BY SubCard
<1>6. a6 \in Nat /\ b6 \in Nat /\ a6 <= b6 /\ (d6 # e6 => a6 < b6)
  BY SubCard
<1>7. a7 \in Nat /\ b7 \in Nat /\ a7 <= b7 /\ (d7 # e7 => a7 < b7)
  BY SubCard
<1>8. a8 \in Nat /\ b8 \in Nat /\ a8 <= b8 /\ (d8 # e8 => a8 < b8)
  BY SubCard
<1>9. /\ Sum8(d1, d2, d3, d4, d5, d6, d7, d8)
           = a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8
      /\ Sum8(e1, e2, e3, e4, e5, e6, e7, e8)
           = b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8
  BY DEF Sum8
<1> HIDE DEF a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8
<1>10. /\ a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 \in Nat
       /\ b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 \in Nat
       /\ a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8
            <= b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8
       /\ (\/ a1 < b1 \/ a2 < b2 \/ a3 < b3 \/ a4 < b4
           \/ a5 < b5 \/ a6 < b6 \/ a7 < b7 \/ a8 < b8)
            => a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8
                 < b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, SumArith
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

LEMMA UniversesFinite ==
    ASSUME LivenessAssumptions
    PROVE  /\ IsFiniteSet(PairVR)
           /\ IsFiniteSet(RequestIds)
           /\ IsFiniteSet(PairQR)
           /\ IsFiniteSet(SlotSet)
           /\ IsFiniteSet(PairRS)
<1>1. IsFiniteSet(Replicas) /\ IsFiniteSet(RequestIds)
  BY DEF LivenessAssumptions
<1>2. IsFiniteSet(SlotSet)
  BY ConstantAssumptions, FS_Interval DEF SlotSet
<1>3. IsFiniteSet(PairVR)
  BY <1>1, FS_Product DEF PairVR
<1>4. IsFiniteSet(PairQR)
  BY <1>1, FS_Product DEF PairQR
<1>5. IsFiniteSet(PairRS)
  BY <1>1, <1>2, FS_Product DEF PairRS
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

(* In any state the work done is a natural number within the bound. *)
LEMMA WorkBounded ==
    ASSUME LivenessAssumptions
    PROVE  /\ Work \in Nat
           /\ WorkBound \in Nat
           /\ Work <= WorkBound
<1>1. /\ IsFiniteSet(PairVR)
      /\ IsFiniteSet(RequestIds)
      /\ IsFiniteSet(PairQR)
      /\ IsFiniteSet(SlotSet)
      /\ IsFiniteSet(PairRS)
  BY UniversesFinite
<1>2. /\ VotedPairs \in SUBSET PairVR
      /\ SelectedRids \in SUBSET RequestIds
      /\ DispatchedRids \in SUBSET RequestIds
      /\ RespondedPairs \in SUBSET PairQR
      /\ ProposedRids \in SUBSET RequestIds
      /\ UsedSlots \in SUBSET SlotSet
      /\ LearnedPairs \in SUBSET PairRS
      /\ ProcessedPairs \in SUBSET PairRS
  BY DEF VotedPairs, SelectedRids, DispatchedRids, RespondedPairs,
         ProposedRids, UsedSlots, LearnedPairs, ProcessedPairs
<1> HIDE DEF VotedPairs, SelectedRids, DispatchedRids, RespondedPairs,
             ProposedRids, UsedSlots, LearnedPairs, ProcessedPairs
<1>3. /\ VotedPairs \subseteq PairVR
      /\ SelectedRids \subseteq RequestIds
      /\ DispatchedRids \subseteq RequestIds
      /\ RespondedPairs \subseteq PairQR
      /\ ProposedRids \subseteq RequestIds
      /\ UsedSlots \subseteq SlotSet
      /\ LearnedPairs \subseteq PairRS
      /\ ProcessedPairs \subseteq PairRS
  BY <1>2
<1>4. /\ Sum8(VotedPairs, SelectedRids, DispatchedRids, RespondedPairs,
              ProposedRids, UsedSlots, LearnedPairs, ProcessedPairs) \in Nat
      /\ Sum8(PairVR, RequestIds, RequestIds, PairQR,
              RequestIds, SlotSet, PairRS, PairRS) \in Nat
      /\ Sum8(VotedPairs, SelectedRids, DispatchedRids, RespondedPairs,
              ProposedRids, UsedSlots, LearnedPairs, ProcessedPairs)
           <= Sum8(PairVR, RequestIds, RequestIds, PairQR,
                   RequestIds, SlotSet, PairRS, PairRS)
  BY <1>1, <1>3, Sum8Mono
<1> QED
  BY <1>4 DEF Work, WorkBound

(***************************************************************************
A step that only adds to the eight sets, and adds something to at least
one of them, lowers Remaining.
***************************************************************************)
LEMMA GrowStep ==
    ASSUME LivenessAssumptions,
           VotedPairs \subseteq VotedPairs',
           SelectedRids \subseteq SelectedRids',
           DispatchedRids \subseteq DispatchedRids',
           RespondedPairs \subseteq RespondedPairs',
           ProposedRids \subseteq ProposedRids',
           UsedSlots \subseteq UsedSlots',
           LearnedPairs \subseteq LearnedPairs',
           ProcessedPairs \subseteq ProcessedPairs',
           \/ VotedPairs # VotedPairs'
           \/ SelectedRids # SelectedRids'
           \/ DispatchedRids # DispatchedRids'
           \/ RespondedPairs # RespondedPairs'
           \/ ProposedRids # ProposedRids'
           \/ UsedSlots # UsedSlots'
           \/ LearnedPairs # LearnedPairs'
           \/ ProcessedPairs # ProcessedPairs'
    PROVE  Remaining' < Remaining
<1>1. /\ IsFiniteSet(PairVR)
      /\ IsFiniteSet(RequestIds)
      /\ IsFiniteSet(PairQR)
      /\ IsFiniteSet(SlotSet)
      /\ IsFiniteSet(PairRS)
  BY UniversesFinite
<1>2. /\ VotedPairs \in SUBSET PairVR
      /\ SelectedRids \in SUBSET RequestIds
      /\ DispatchedRids \in SUBSET RequestIds
      /\ RespondedPairs \in SUBSET PairQR
      /\ ProposedRids \in SUBSET RequestIds
      /\ UsedSlots \in SUBSET SlotSet
      /\ LearnedPairs \in SUBSET PairRS
      /\ ProcessedPairs \in SUBSET PairRS
  BY DEF VotedPairs, SelectedRids, DispatchedRids, RespondedPairs,
         ProposedRids, UsedSlots, LearnedPairs, ProcessedPairs
<1>3. /\ VotedPairs' \in SUBSET PairVR
      /\ SelectedRids' \in SUBSET RequestIds
      /\ DispatchedRids' \in SUBSET RequestIds
      /\ RespondedPairs' \in SUBSET PairQR
      /\ ProposedRids' \in SUBSET RequestIds
      /\ UsedSlots' \in SUBSET SlotSet
      /\ LearnedPairs' \in SUBSET PairRS
      /\ ProcessedPairs' \in SUBSET PairRS
  BY DEF VotedPairs, SelectedRids, DispatchedRids, RespondedPairs,
         ProposedRids, UsedSlots, LearnedPairs, ProcessedPairs,
         PairVR, PairQR, SlotSet, PairRS
<1>4. Work' =
        Sum8(VotedPairs', SelectedRids', DispatchedRids', RespondedPairs',
             ProposedRids', UsedSlots', LearnedPairs', ProcessedPairs')
  BY DEF Work, Sum8
<1>5. WorkBound' = WorkBound
  BY DEF WorkBound, Sum8, PairVR, PairQR, SlotSet, PairRS
<1>6. Work \in Nat /\ WorkBound \in Nat
  BY WorkBounded
<1> HIDE DEF VotedPairs, SelectedRids, DispatchedRids, RespondedPairs,
             ProposedRids, UsedSlots, LearnedPairs, ProcessedPairs
<1>fin. /\ IsFiniteSet(VotedPairs')
        /\ IsFiniteSet(SelectedRids')
        /\ IsFiniteSet(DispatchedRids')
        /\ IsFiniteSet(RespondedPairs')
        /\ IsFiniteSet(ProposedRids')
        /\ IsFiniteSet(UsedSlots')
        /\ IsFiniteSet(LearnedPairs')
        /\ IsFiniteSet(ProcessedPairs')
  BY <1>1, <1>3, FS_Subset
<1>7. /\ Sum8(VotedPairs', SelectedRids', DispatchedRids', RespondedPairs',
              ProposedRids', UsedSlots', LearnedPairs', ProcessedPairs')
           \in Nat
      /\ Sum8(VotedPairs, SelectedRids, DispatchedRids, RespondedPairs,
              ProposedRids, UsedSlots, LearnedPairs, ProcessedPairs)
           < Sum8(VotedPairs', SelectedRids', DispatchedRids',
                  RespondedPairs', ProposedRids', UsedSlots',
                  LearnedPairs', ProcessedPairs')
  BY <1>fin, Sum8Mono
<1>8. Work' \in Nat /\ Work < Work'
  BY <1>4, <1>7 DEF Work
<1>9. Remaining' = WorkBound - Work'
  BY <1>5 DEF Remaining
<1> QED
  BY <1>6, <1>8, <1>9 DEF Remaining

LEMMA RemainingUnchanged ==
    ASSUME UNCHANGED vars
    PROVE  Remaining' = Remaining
BY DEF vars, Remaining, Work, WorkBound, Sum8, VotedPairs, SelectedRids,
       DispatchedRids, RespondedPairs, ProposedRids, UsedSlots,
       LearnedPairs, ProcessedPairs, HasVoted, PairVR, PairQR, SlotSet,
       PairRS

(***************************************************************************
Each of the eight sets depends on one variable.
***************************************************************************)
LEMMA SameSets ==
    /\ votes' = votes => VotedPairs' = VotedPairs
    /\ selected' = selected => SelectedRids' = SelectedRids
    /\ dispatchers' = dispatchers => DispatchedRids' = DispatchedRids
    /\ execResponse' = execResponse => RespondedPairs' = RespondedPairs
    /\ proposed' = proposed => ProposedRids' = ProposedRids
    /\ consensusLog' = consensusLog => UsedSlots' = UsedSlots
    /\ learned' = learned => LearnedPairs' = LearnedPairs
    /\ processed' = processed => ProcessedPairs' = ProcessedPairs
BY DEF VotedPairs, SelectedRids, DispatchedRids, RespondedPairs,
       ProposedRids, UsedSlots, LearnedPairs, ProcessedPairs, HasVoted,
       PairVR, PairQR, SlotSet, PairRS

(***************************************************************************
Every step either leaves the state alone or lowers Remaining.
***************************************************************************)
LEMMA RemainingStep ==
    ASSUME LivenessAssumptions
    PROVE  LiveState /\ [Next]_vars =>
               (Remaining' < Remaining \/ UNCHANGED vars)
<1> SUFFICES ASSUME LiveState, [Next]_vars
             PROVE  Remaining' < Remaining \/ UNCHANGED vars
  OBVIOUS
<1> USE DEF LivenessAssumptions, StrictDelivery
<1>t. /\ votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
      /\ selected \in [RequestIds -> Payloads \union {NoValue}]
      /\ dispatchers \in [RequestIds -> SUBSET Replicas]
      /\ execResponse \in
            [RequestIds -> [Replicas -> Responses \union {NoValue}]]
      /\ proposed \subseteq ResponseItems
      /\ consensusLog \in Seq(Seq(ResponseItems))
      /\ Len(consensusLog) <= MaxSlots
      /\ learned \in [Replicas -> SUBSET (1..MaxSlots)]
      /\ processed \in [Replicas -> Nat]
      /\ leader \in Replicas
      /\ ProposedFromLeader
  BY DEF LiveState, LiveInv, ValidityInv, ValidityTypeOK
<1>c. /\ MaxSlots \in Nat
      /\ NoValue \notin Payloads
      /\ NoValue \notin Responses
  BY ConstantAssumptions
<1>1. CASE SubmitVoteAction
  <2>1. PICK replica \in Replicas, request \in RequestIds,
             payload \in Payloads : SubmitVote(replica, request, payload)
    BY <1>1 DEF SubmitVoteAction
  <2>2. /\ ~HasVoted(replica, request)
        /\ votes' = [votes EXCEPT ![request][payload] = @ \union {replica}]
        /\ UNCHANGED <<selected, dispatchers, execResponse, proposed,
                       consensusLog, learned, processed>>
    BY <2>1 DEF SubmitVote
  <2>3. \A q \in RequestIds, p \in Payloads : votes[q][p] \subseteq votes'[q][p]
    BY <1>t, <2>2
  <2>4. replica \in votes'[request][payload]
    BY <1>t, <2>2
  <2>5. \A r \in Replicas, q \in RequestIds :
            HasVoted(r, q) => HasVoted(r, q)'
    BY <2>3 DEF HasVoted
  <2>6. HasVoted(replica, request)'
    BY <2>4 DEF HasVoted
  <2>7. VotedPairs \subseteq VotedPairs'
    BY <2>5 DEF VotedPairs, PairVR
  <2>8. /\ <<replica, request>> \in VotedPairs'
        /\ <<replica, request>> \notin VotedPairs
    BY <2>2, <2>6 DEF VotedPairs, PairVR
  <2>9. VotedPairs # VotedPairs'
    BY <2>8
  <2>10. /\ SelectedRids' = SelectedRids
         /\ DispatchedRids' = DispatchedRids
         /\ RespondedPairs' = RespondedPairs
         /\ ProposedRids' = ProposedRids
         /\ UsedSlots' = UsedSlots
         /\ LearnedPairs' = LearnedPairs
         /\ ProcessedPairs' = ProcessedPairs
    BY <2>2, SameSets
  <2> QED
    BY <2>7, <2>9, <2>10, GrowStep
<1>2. CASE SelectAction
  <2>1. PICK request \in RequestIds, payload \in Payloads :
            /\ selected[request] = NoValue
            /\ selected' = [selected EXCEPT ![request] = payload]
            /\ UNCHANGED <<votes, dispatchers, execResponse, proposed,
                           consensusLog, learned, processed>>
    BY <1>2 DEF SelectAction, SelectByQuorum, TimeoutSelect
  <2>2. /\ selected'[request] = payload
        /\ \A q \in RequestIds : q # request => selected'[q] = selected[q]
    BY <1>t, <2>1
  <2>3. SelectedRids \subseteq SelectedRids'
    BY <2>1, <2>2 DEF SelectedRids
  <2>4. request \in SelectedRids' /\ request \notin SelectedRids
    BY <1>c, <2>1, <2>2 DEF SelectedRids
  <2>5. SelectedRids # SelectedRids'
    BY <2>4
  <2>6. /\ VotedPairs' = VotedPairs
        /\ DispatchedRids' = DispatchedRids
        /\ RespondedPairs' = RespondedPairs
        /\ ProposedRids' = ProposedRids
        /\ UsedSlots' = UsedSlots
        /\ LearnedPairs' = LearnedPairs
        /\ ProcessedPairs' = ProcessedPairs
    BY <2>1, SameSets
  <2> QED
    BY <2>3, <2>5, <2>6, GrowStep
<1>3. CASE DispatchAction
  <2>1. PICK replica \in Replicas, request \in RequestIds :
            Dispatch(replica, request)
    BY <1>3 DEF DispatchAction
  <2>2. /\ dispatchers[request] = {}
        /\ dispatchers' =
              [dispatchers EXCEPT ![request] = @ \union {replica}]
        /\ UNCHANGED <<votes, selected, execResponse, proposed,
                       consensusLog, learned, processed>>
    BY <2>1 DEF Dispatch
  <2>3. /\ replica \in dispatchers'[request]
        /\ \A q \in RequestIds : q # request =>
              dispatchers'[q] = dispatchers[q]
    BY <1>t, <2>2
  <2>4. DispatchedRids \subseteq DispatchedRids'
    BY <2>2, <2>3 DEF DispatchedRids
  <2>5. request \in DispatchedRids' /\ request \notin DispatchedRids
    BY <2>2, <2>3 DEF DispatchedRids
  <2>6. DispatchedRids # DispatchedRids'
    BY <2>5
  <2>7. /\ VotedPairs' = VotedPairs
        /\ SelectedRids' = SelectedRids
        /\ RespondedPairs' = RespondedPairs
        /\ ProposedRids' = ProposedRids
        /\ UsedSlots' = UsedSlots
        /\ LearnedPairs' = LearnedPairs
        /\ ProcessedPairs' = ProcessedPairs
    BY <2>2, SameSets
  <2> QED
    BY <2>4, <2>6, <2>7, GrowStep
<1>4. CASE ExternalRespondAction
  <2>1. PICK replica \in Replicas, request \in RequestIds,
             responseValue \in Responses :
            ExternalRespond(replica, request, responseValue)
    BY <1>4 DEF ExternalRespondAction
  <2>2. /\ execResponse[request][replica] = NoValue
        /\ execResponse' =
              [execResponse EXCEPT ![request][replica] = responseValue]
        /\ UNCHANGED <<votes, selected, dispatchers, proposed,
                       consensusLog, learned, processed>>
    BY <2>1 DEF ExternalRespond
  <2>3. /\ execResponse'[request][replica] = responseValue
        /\ \A q \in RequestIds, r \in Replicas :
              (q # request \/ r # replica) =>
                  execResponse'[q][r] = execResponse[q][r]
    BY <1>t, <2>2
  <2>4. RespondedPairs \subseteq RespondedPairs'
    BY <2>2, <2>3 DEF RespondedPairs, PairQR
  <2>5. /\ <<request, replica>> \in RespondedPairs'
        /\ <<request, replica>> \notin RespondedPairs
    BY <1>c, <2>2, <2>3 DEF RespondedPairs, PairQR
  <2>6. RespondedPairs # RespondedPairs'
    BY <2>5
  <2>7. /\ VotedPairs' = VotedPairs
        /\ SelectedRids' = SelectedRids
        /\ DispatchedRids' = DispatchedRids
        /\ ProposedRids' = ProposedRids
        /\ UsedSlots' = UsedSlots
        /\ LearnedPairs' = LearnedPairs
        /\ ProcessedPairs' = ProcessedPairs
    BY <2>2, SameSets
  <2> QED
    BY <2>4, <2>6, <2>7, GrowStep
<1>5. CASE ProposeResponseAction
  <2>1. PICK replica \in Replicas, request \in RequestIds,
             responseValue \in Responses :
            ProposeResponse(replica, request, responseValue)
    BY <1>5 DEF ProposeResponseAction
  <2> DEFINE item == ObservedItem(request, responseValue)
  <2>2. /\ replica = leader
        /\ execResponse[request][replica] = responseValue
        /\ item \notin proposed
        /\ proposed' = proposed \union {item}
        /\ UNCHANGED <<votes, selected, dispatchers, execResponse,
                       consensusLog, learned, processed>>
    BY <2>1 DEF ProposeResponse
  <2>3. item.rid = request
    BY DEF ObservedItem
  <2>4. \A other \in proposed : other.rid # request
    <3> SUFFICES ASSUME NEW other \in proposed, other.rid = request
                 PROVE  FALSE
      OBVIOUS
    <3>1. other = ObservedItem(request, execResponse[request][leader])
      BY <1>t DEF ProposedFromLeader
    <3> QED
      BY <2>2, <3>1
  <2> HIDE DEF item
  <2>5. ProposedRids \subseteq ProposedRids'
    BY <2>2 DEF ProposedRids
  <2>6. request \in ProposedRids' /\ request \notin ProposedRids
    BY <2>2, <2>3, <2>4 DEF ProposedRids
  <2>7. ProposedRids # ProposedRids'
    BY <2>6
  <2>8. /\ VotedPairs' = VotedPairs
        /\ SelectedRids' = SelectedRids
        /\ DispatchedRids' = DispatchedRids
        /\ RespondedPairs' = RespondedPairs
        /\ UsedSlots' = UsedSlots
        /\ LearnedPairs' = LearnedPairs
        /\ ProcessedPairs' = ProcessedPairs
    BY <2>2, SameSets
  <2> QED
    BY <2>5, <2>7, <2>8, GrowStep
<1>6. CASE DecideAction
  <2>1. PICK batch :
            /\ Len(consensusLog) < MaxSlots
            /\ consensusLog' = Append(consensusLog, batch)
            /\ UNCHANGED <<votes, selected, dispatchers, execResponse,
                           proposed, learned, processed>>
    BY <1>6 DEF DecideAction, DecideOne, DecidePair
  <2>2. /\ Len(consensusLog) \in Nat
        /\ Len(consensusLog') = Len(consensusLog) + 1
    BY <1>t, <2>1
  <2>3. UsedSlots \subseteq UsedSlots'
    BY <2>2 DEF UsedSlots, SlotSet
  <2>4. /\ Len(consensusLog) + 1 \in UsedSlots'
        /\ Len(consensusLog) + 1 \notin UsedSlots
    BY <1>c, <2>1, <2>2 DEF UsedSlots, SlotSet
  <2>5. UsedSlots # UsedSlots'
    BY <2>4
  <2>6. /\ VotedPairs' = VotedPairs
        /\ SelectedRids' = SelectedRids
        /\ DispatchedRids' = DispatchedRids
        /\ RespondedPairs' = RespondedPairs
        /\ ProposedRids' = ProposedRids
        /\ LearnedPairs' = LearnedPairs
        /\ ProcessedPairs' = ProcessedPairs
    BY <2>1, SameSets
  <2> QED
    BY <2>3, <2>5, <2>6, GrowStep
<1>7. CASE LearnAction
  <2>1. PICK replica \in Replicas, slot \in 1..MaxSlots :
            LearnSlot(replica, slot)
    BY <1>7 DEF LearnAction
  <2>2. /\ slot \notin learned[replica]
        /\ learned' = [learned EXCEPT ![replica] = @ \union {slot}]
        /\ UNCHANGED <<votes, selected, dispatchers, execResponse,
                       proposed, consensusLog, processed>>
    BY <2>1 DEF LearnSlot
  <2>3. /\ slot \in learned'[replica]
        /\ \A r \in Replicas : learned[r] \subseteq learned'[r]
    BY <1>t, <2>2
  <2>4. LearnedPairs \subseteq LearnedPairs'
    BY <2>3 DEF LearnedPairs, PairRS, SlotSet
  <2>5. /\ <<replica, slot>> \in LearnedPairs'
        /\ <<replica, slot>> \notin LearnedPairs
    BY <2>2, <2>3 DEF LearnedPairs, PairRS, SlotSet
  <2>6. LearnedPairs # LearnedPairs'
    BY <2>5
  <2>7. /\ VotedPairs' = VotedPairs
        /\ SelectedRids' = SelectedRids
        /\ DispatchedRids' = DispatchedRids
        /\ RespondedPairs' = RespondedPairs
        /\ ProposedRids' = ProposedRids
        /\ UsedSlots' = UsedSlots
        /\ ProcessedPairs' = ProcessedPairs
    BY <2>2, SameSets
  <2> QED
    BY <2>4, <2>6, <2>7, GrowStep
<1>8. CASE ProcessAction
  <2>1. PICK replica \in Replicas : ProcessContiguous(replica)
    BY <1>8 DEF ProcessAction
  <2> DEFINE slot == processed[replica] + 1
  <2>2. /\ slot \in 1..Len(consensusLog)
        /\ processed' = [processed EXCEPT ![replica] = slot]
        /\ UNCHANGED <<votes, selected, dispatchers, execResponse,
                       proposed, consensusLog, learned>>
    BY <2>1 DEF ProcessContiguous
  <2>3. /\ processed[replica] \in Nat
        /\ slot \in Nat
        /\ slot = processed[replica] + 1
        /\ slot \in 1..MaxSlots
        /\ Len(consensusLog) \in Nat
    BY <1>t, <1>c, <2>2
  <2>4. /\ processed'[replica] = slot
        /\ \A r \in Replicas : r # replica => processed'[r] = processed[r]
    BY <1>t, <2>2
  <2> HIDE DEF slot
  <2>5. \A r \in Replicas : processed[r] \in Nat /\ processed'[r] \in Nat
                             /\ processed[r] <= processed'[r]
    BY <1>t, <2>3, <2>4
  <2>6. ProcessedPairs \subseteq ProcessedPairs'
    BY <2>5 DEF ProcessedPairs, PairRS, SlotSet
  <2>7. /\ <<replica, slot>> \in ProcessedPairs'
        /\ <<replica, slot>> \notin ProcessedPairs
    BY <2>3, <2>4 DEF ProcessedPairs, PairRS, SlotSet
  <2>8. ProcessedPairs # ProcessedPairs'
    BY <2>7
  <2>9. /\ VotedPairs' = VotedPairs
        /\ SelectedRids' = SelectedRids
        /\ DispatchedRids' = DispatchedRids
        /\ RespondedPairs' = RespondedPairs
        /\ ProposedRids' = ProposedRids
        /\ UsedSlots' = UsedSlots
        /\ LearnedPairs' = LearnedPairs
    BY <2>2, SameSets
  <2> QED
    BY <2>6, <2>8, <2>9, GrowStep
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
  BY <1>16
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
     <1>11, <1>12, <1>13, <1>14, <1>15, <1>16 DEF Next

(***************************************************************************
Remaining is a natural number that no step raises and every state-changing
step lowers, so by induction on its value the state eventually stops
changing.
***************************************************************************)
Halted == <>[][FALSE]_vars
HaltsBelow(n) ==
    []LiveState /\ [][Next]_vars => [](Remaining < n => Halted)

THEOREM Termination ==
    ASSUME LivenessAssumptions
    PROVE  Spec => <>[][FALSE]_vars
<1>0. /\ WorkBound \in Nat
      /\ Remaining \in Int
      /\ ~(Remaining < 0)
      /\ Remaining < WorkBound + 1
  BY WorkBounded DEF Remaining
<1>1. HaltsBelow(0)
  <2>1. LiveState => ~(Remaining < 0)
    BY <1>0
  <2> QED
    BY <2>1, PTL DEF HaltsBelow, Halted
<1>2. \A n \in Nat : HaltsBelow(n) => HaltsBelow(n + 1)
  <2> TAKE n \in Nat
  <2>1. LiveState /\ Remaining < n + 1 => (Remaining < n \/ Remaining = n)
    BY <1>0
  <2>2. LiveState /\ Remaining = n /\ [Next]_vars =>
            ((Remaining < n)' \/ ((Remaining = n)' /\ UNCHANGED vars))
    BY RemainingStep, RemainingUnchanged
  <2> QED
    BY <2>1, <2>2, PTL DEF HaltsBelow, Halted
<1>3. \A n \in Nat : HaltsBelow(n)
  <2> HIDE DEF HaltsBelow
  <2> QED
    BY <1>1, <1>2, NatInduction
<1>4. HaltsBelow(WorkBound + 1)
  BY <1>0, <1>3
<1>5. LiveState => Remaining < WorkBound + 1
  BY <1>0
<1> QED
  BY <1>4, <1>5, LiveStateInvariant, PTL DEF HaltsBelow, Halted, Spec
=============================================================================

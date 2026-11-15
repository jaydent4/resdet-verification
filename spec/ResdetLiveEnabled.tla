--------------------------- MODULE ResdetLiveEnabled ---------------------------
(***************************************************************************
TLAPS liveness proof, part 3 of 5: in a reachable state with a leader
and with the replicas in U up (StableOn(U)), each enabling condition
implies that the corresponding fair action of FairSpec is enabled and
changes the state. These are the only places where the proof reasons
about ENABLED.

The module has two layers.

The "Step" lemmas say: if one instance of an action (a replica, a request,
a value) satisfies the action's guards, and the instance's update really
changes a variable, then the quantified action that FairSpec is fair to
is enabled. Their hypotheses repeat the guards of Resdet.tla literally,
and nothing else.

The "Enabled" theorems pick the instance from the enabling condition and
establish those guards from LiveState, StableOn(U) and
LivenessAssumptions. The instance is always the leader or a replica in U,
which StableOn(U) says are up, so crashes of other replicas do not matter.
They use no ENABLED reasoning of their own.
***************************************************************************)
EXTENDS ResdetLiveInv

(***************************************************************************
How the Step lemmas are checked.

ExpandENABLED turns ENABLED <<A>>_vars into: there exist values for the
sixteen primed variables that satisfy A and are not all equal to the
current values. For a quantified action the witnesses are the instance's
arguments and the values its update assigns.

The default backends do not find them reliably. The primed variables
occur only in equations, so the SMT solvers have nothing to match on and
fall back to model-based instantiation, which succeeded or timed out
depending on bound-variable names and on unrelated definitions in scope.
Zenon and Isabelle's automatic tactics time out.

Each Step lemma therefore gives Isabelle a fixed script that builds the
proof by construction and involves no search:

  (rule_tac exI)+            unknowns for the sixteen primed variables
  rule_tac conjI             split "A holds" from "the state changes"
  rule_tac disjI1 / disjI2   (Select, Decide) the disjunct of the action
  (rule_tac bExI,
   erule_tac asm_rl)+        the instance's arguments, read off the
                             hypotheses r \in Replicas, q \in RequestIds, ...
  (rule_tac conjI,
   (rule_tac refl |
    erule_tac asm_rl |
    simp))+ ...              conjunct by conjunct: an update x' = e fixes
                             the unknown for x' by reflexivity; a guard is
                             one of the hypotheses verbatim
  rule_tac notI,
  (erule_tac conjE)+,
  erule_tac notE,
  erule_tac asm_rl           if no variable changed, the changed variable
                             would equal its old value, contradicting the
                             last hypothesis

The script is repeated inline because TLAPS accepts a backend pragma only
when it is written out in the BY clause. The _tac forms are used because
TLAPS passes every hypothesis to Isabelle as a chained fact, which the
plain rule and assumption methods would try to consume.
***************************************************************************)
LEMMA VoteStep ==
    ASSUME NEW r \in Replicas, NEW q \in RequestIds, NEW p \in Payloads,
           r \in up,
           ~HasVoted(r, q),
           [votes EXCEPT ![q][p] = @ \union {r}] # votes
    PROVE  ENABLED <<SubmitVoteAction>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac bExI, erule_tac asm_rl)+, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF SubmitVoteAction, SubmitVote, vars
LEMMA SelectByQuorumStep ==
    ASSUME NEW r \in Replicas, NEW q \in RequestIds, NEW p \in Payloads,
           r = leader,
           r \in up,
           selected[q] = NoValue,
           Cardinality(votes[q][p]) >= (IF MutantNoQuorum THEN 1 ELSE Quorum),
           [selected EXCEPT ![q] = p] # selected
    PROVE  ENABLED <<SelectAction>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, rule_tac disjI1, (rule_tac bExI, erule_tac asm_rl)+, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF SelectAction, SelectByQuorum, TimeoutSelect, vars
LEMMA TimeoutSelectStep ==
    ASSUME NEW r \in Replicas, NEW q \in RequestIds, NEW p \in Payloads,
           EnableTimeoutFallback,
           r = leader,
           r \in up,
           selected[q] = NoValue,
           votes[q][p] # {},
           [selected EXCEPT ![q] = p] # selected
    PROVE  ENABLED <<SelectAction>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, rule_tac disjI2, (rule_tac bExI, erule_tac asm_rl)+, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF SelectAction, SelectByQuorum, TimeoutSelect, vars
LEMMA DispatchStep ==
    ASSUME NEW r \in Replicas, NEW q \in RequestIds,
           selected[q] # NoValue,
           r \in up,
           IF MutantAllDispatch THEN TRUE ELSE r = leader,
           r \notin dispatchers[q],
           MutantAllDispatch \/ EnableCrashes \/ dispatchers[q] = {},
           [dispatchers EXCEPT ![q] = @ \union {r}] # dispatchers
    PROVE  ENABLED <<DispatchAction>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac bExI, erule_tac asm_rl)+, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF DispatchAction, Dispatch, vars
LEMMA RespondStep ==
    ASSUME NEW r \in Replicas, NEW q \in RequestIds, NEW v \in Responses,
           r \in dispatchers[q],
           execResponse[q][r] = NoValue,
           [execResponse EXCEPT ![q][r] = v] # execResponse
    PROVE  ENABLED <<ExternalRespondAction>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac bExI, erule_tac asm_rl)+, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF ExternalRespondAction, ExternalRespond, vars
LEMMA ProposeStep ==
    ASSUME NEW r \in Replicas, NEW q \in RequestIds, NEW v \in Responses,
           r = leader,
           r \in up,
           r \in dispatchers[q],
           execResponse[q][r] = v,
           ObservedItem(q, v) \notin proposed,
           proposed \union {ObservedItem(q, v)} # proposed
    PROVE  ENABLED <<ProposeResponseAction>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac bExI, erule_tac asm_rl)+, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF ProposeResponseAction, ProposeResponse, vars
LEMMA DecideOneStep ==
    ASSUME NEW item \in ResponseItems,
           Len(consensusLog) < MaxSlots,
           item \in EligibleProposalItems,
           Append(consensusLog, <<item>>) # consensusLog
    PROVE  ENABLED <<DecideAction>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, rule_tac disjI1, (rule_tac bExI, erule_tac asm_rl)+, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF DecideAction, DecideOne, DecidePair, vars
LEMMA LearnStep ==
    ASSUME NEW r \in Replicas, NEW s \in 1..MaxSlots,
           r \in up,
           s \in 1..Len(consensusLog),
           s \notin learned[r],
           [learned EXCEPT ![r] = @ \union {s}] # learned
    PROVE  ENABLED <<LearnAction>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac bExI, erule_tac asm_rl)+, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF LearnAction, LearnSlot, vars
LEMMA ProcessStep ==
    ASSUME NEW r \in Replicas,
           r \in up,
           processed[r] + 1 \in 1..Len(consensusLog),
           processed[r] + 1 \in learned[r],
           [processed EXCEPT ![r] = processed[r] + 1] # processed
    PROVE  ENABLED <<ProcessAction>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac bExI, erule_tac asm_rl)+, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF ProcessAction, ProcessContiguous, vars
(***************************************************************************
What StableOn(U) gives in a reachable state: the leader is a replica and
is up, and so is every replica in U.
***************************************************************************)
LEMMA StableFacts ==
    ASSUME NEW U \in SUBSET Replicas, LiveState, StableOn(U)
    PROVE  /\ leader \in Replicas
           /\ leader \in up
           /\ \A replica \in U : replica \in Replicas /\ replica \in up
BY DEF LiveState, LiveInv, LeaderUp, StableOn

(***************************************************************************
L1: a replica in U that has not submitted a request can submit it.
***************************************************************************)
THEOREM EnabledVote ==
    ASSUME LivenessAssumptions, NEW U \in SUBSET Replicas
    PROVE  LiveState /\ StableOn(U) /\ CanVote(U)
              => ENABLED <<SubmitVoteAction>>_vars
<1> SUFFICES ASSUME LiveState, StableOn(U), CanVote(U)
             PROVE  ENABLED <<SubmitVoteAction>>_vars
  OBVIOUS
<1>1. PICK r0 \in U, q \in RequestIds : ~HasVoted(r0, q)
  BY DEF CanVote
<1>2. PICK r \in Replicas : r = r0 /\ r \in up
  BY <1>1, StableFacts
<1>3. PICK p \in Payloads : TRUE
  BY ConstantAssumptions
<1>4. votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
  BY DEF LiveState, LiveInv
<1>5. ~HasVoted(r, q)
  BY <1>1, <1>2
<1>6. r \notin votes[q][p]
  BY <1>5 DEF HasVoted
<1>7. [votes EXCEPT ![q][p] = @ \union {r}] # votes
  BY <1>4, <1>6
<1> QED
  BY <1>2, <1>5, <1>7, VoteStep

(***************************************************************************
The leader can select a request that every replica in U has submitted.
This is where VotersSuffice(U) is used.
***************************************************************************)
THEOREM EnabledSelect ==
    ASSUME LivenessAssumptions, NEW U \in SUBSET Replicas,
           U # {}, VotersSuffice(U)
    PROVE  LiveState /\ StableOn(U) /\ CanSelect(U)
              => ENABLED <<SelectAction>>_vars
<1> SUFFICES ASSUME LiveState, StableOn(U), CanSelect(U)
             PROVE  ENABLED <<SelectAction>>_vars
  OBVIOUS
<1>1. PICK q \in RequestIds :
        /\ selected[q] = NoValue
        /\ \A replica \in U : HasVoted(replica, q)
  BY DEF CanSelect
<1>2. PICK voter \in U : TRUE
  OBVIOUS
<1>3. PICK p \in Payloads : voter \in votes[q][p]
  BY <1>1, <1>2 DEF HasVoted
<1>4. /\ leader \in Replicas
      /\ leader \in up
      /\ votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
      /\ selected \in [RequestIds -> Payloads \union {NoValue}]
  BY StableFacts DEF LiveState, LiveInv, ValidityInv, ValidityTypeOK
<1>5. PICK r \in Replicas : r = leader /\ r \in up
  BY <1>4
<1>6. p # NoValue
  BY ConstantAssumptions
<1>7. [selected EXCEPT ![q] = p] # selected
  BY <1>1, <1>4, <1>6
<1>8. votes[q][p] # {} /\ votes[q][p] \subseteq Replicas
  BY <1>3, <1>4
<1>fin. IsFiniteSet(votes[q][p])
  <2>1. IsFiniteSet(Replicas)
    BY DEF LivenessAssumptions
  <2> QED
    BY <1>8, <2>1, FS_Subset
<1>9. CASE EnableTimeoutFallback
  BY <1>1, <1>5, <1>7, <1>8, <1>9, TimeoutSelectStep
<1>10. ASSUME Cardinality(votes[q][p]) >= Quorum
       PROVE  ENABLED <<SelectAction>>_vars
  <2>1. ~MutantNoQuorum
    BY DEF LivenessAssumptions
  <2>2. Cardinality(votes[q][p]) >= (IF MutantNoQuorum THEN 1 ELSE Quorum)
    BY <1>10, <2>1
  <2> QED
    BY <1>1, <1>5, <1>7, <2>2, SelectByQuorumStep
<1>11. CASE Quorum = 1
  <2>1. Cardinality(votes[q][p]) \in Nat
    BY <1>fin, FS_CardinalityType
  <2>2. Cardinality(votes[q][p]) # 0
    BY <1>8, <1>fin, FS_EmptySet
  <2>3. Cardinality(votes[q][p]) >= Quorum
    BY <2>1, <2>2, <1>11
  <2> QED
    BY <2>3, <1>10
<1>12. CASE /\ \E payload \in Payloads : Payloads = {payload}
            /\ Cardinality(U) >= Quorum
  <2>1. \A replica \in U : replica \in votes[q][p]
    <3> TAKE replica \in U
    <3>1. PICK p2 \in Payloads : replica \in votes[q][p2]
      BY <1>1 DEF HasVoted
    <3>2. p2 = p
      BY <1>12
    <3> QED
      BY <3>1, <3>2
  <2>2. U \subseteq votes[q][p]
    BY <2>1
  <2>3. /\ IsFiniteSet(U)
        /\ Cardinality(U) <= Cardinality(votes[q][p])
    BY <2>2, <1>fin, FS_Subset
  <2>4. /\ Cardinality(U) \in Nat
        /\ Cardinality(votes[q][p]) \in Nat
    BY <2>3, <1>fin, FS_CardinalityType
  <2>5. Quorum \in Nat
    <3>1. IsFiniteSet(Replicas)
      BY DEF LivenessAssumptions
    <3>2. Cardinality(Replicas) \in Nat
      BY <3>1, FS_CardinalityType
    <3>3. Quorum \in 1..Cardinality(Replicas)
      BY ConstantAssumptions
    <3> QED
      BY <3>2, <3>3
  <2>6. Cardinality(votes[q][p]) >= Quorum
    BY <2>3, <2>4, <2>5, <1>12
  <2> QED
    BY <2>6, <1>10
<1> QED
  BY <1>9, <1>11, <1>12 DEF VotersSuffice

(***************************************************************************
L4: the leader issues the nested request once it is selected, unless it
already has. With crashes enabled a new leader may issue it again; without
them only the one leader ever dispatches (SingleDispatcher).
***************************************************************************)
THEOREM EnabledDispatch ==
    ASSUME LivenessAssumptions, NEW U \in SUBSET Replicas
    PROVE  LiveState /\ StableOn(U) /\ CanDispatch
              => ENABLED <<DispatchAction>>_vars
<1> SUFFICES ASSUME LiveState, StableOn(U), CanDispatch
             PROVE  ENABLED <<DispatchAction>>_vars
  OBVIOUS
<1>1. PICK q \in RequestIds :
        selected[q] # NoValue /\ leader \notin dispatchers[q]
  BY DEF CanDispatch
<1>2. /\ leader \in Replicas
      /\ leader \in up
      /\ dispatchers \in [RequestIds -> SUBSET Replicas]
  BY StableFacts DEF LiveState, ValidityInv, ValidityTypeOK
<1>3. PICK r \in Replicas : r = leader /\ r \in up
  BY <1>2
<1>4. r \notin dispatchers[q]
  BY <1>1, <1>3
<1>5. [dispatchers EXCEPT ![q] = @ \union {r}] # dispatchers
  BY <1>2, <1>4
<1>6. IF MutantAllDispatch THEN TRUE ELSE r = leader
  BY <1>3
<1>7. MutantAllDispatch \/ EnableCrashes \/ dispatchers[q] = {}
  <2>1. CASE EnableCrashes
    BY <2>1
  <2>2. CASE ~EnableCrashes
    <3>1. dispatchers[q] \subseteq {leader}
      BY <2>2 DEF LiveState, LiveInv, SingleDispatcher
    <3> QED
      BY <3>1, <1>1
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>3, <1>4, <1>5, <1>6, <1>7, DispatchStep

(***************************************************************************
L3: the downstream service answers the leader's nested request.
***************************************************************************)
THEOREM EnabledRespond ==
    ASSUME LivenessAssumptions, NEW U \in SUBSET Replicas
    PROVE  LiveState /\ StableOn(U) /\ CanRespond
              => ENABLED <<ExternalRespondAction>>_vars
<1> SUFFICES ASSUME LiveState, StableOn(U), CanRespond
             PROVE  ENABLED <<ExternalRespondAction>>_vars
  OBVIOUS
<1>1. PICK q \in RequestIds :
        /\ leader \in dispatchers[q]
        /\ execResponse[q][leader] = NoValue
  BY DEF CanRespond
<1>2. PICK v \in Responses : TRUE
  BY ConstantAssumptions
<1>3. /\ leader \in Replicas
      /\ execResponse \in
            [RequestIds -> [Replicas -> Responses \union {NoValue}]]
  BY StableFacts DEF LiveState, ValidityInv, ValidityTypeOK
<1>4. PICK r \in Replicas : r = leader
  BY <1>3
<1>5. v # NoValue
  BY ConstantAssumptions
<1>6. [execResponse EXCEPT ![q][r] = v] # execResponse
  BY <1>1, <1>3, <1>4, <1>5
<1>7. /\ r \in dispatchers[q]
      /\ execResponse[q][r] = NoValue
  BY <1>1, <1>4
<1> QED
  BY <1>6, <1>7, RespondStep

(***************************************************************************
L4: the leader proposes the response it received.
***************************************************************************)
THEOREM EnabledPropose ==
    ASSUME LivenessAssumptions, NEW U \in SUBSET Replicas
    PROVE  LiveState /\ StableOn(U) /\ CanPropose
              => ENABLED <<ProposeResponseAction>>_vars
<1> SUFFICES ASSUME LiveState, StableOn(U), CanPropose
             PROVE  ENABLED <<ProposeResponseAction>>_vars
  OBVIOUS
<1>1. PICK q \in RequestIds :
        /\ leader \in dispatchers[q]
        /\ execResponse[q][leader] # NoValue
        /\ ObservedItem(q, execResponse[q][leader]) \notin proposed
  BY DEF CanPropose
<1>2. /\ leader \in Replicas
      /\ leader \in up
      /\ execResponse \in
            [RequestIds -> [Replicas -> Responses \union {NoValue}]]
  BY StableFacts DEF LiveState, ValidityInv, ValidityTypeOK
<1>3. PICK r \in Replicas : r = leader /\ r \in up
  BY <1>2
<1>4. PICK v \in Responses : v = execResponse[q][r]
  BY <1>1, <1>2, <1>3
<1>5. /\ r \in dispatchers[q]
      /\ execResponse[q][r] = v
      /\ ObservedItem(q, v) \notin proposed
  BY <1>1, <1>3, <1>4
<1>6. proposed \union {ObservedItem(q, v)} # proposed
  BY <1>5
<1> QED
  BY <1>3, <1>5, <1>6, ProposeStep

(***************************************************************************
CG3(2): consensus agrees on a proposed entry for a request that has no
agreed entry yet, while the log has room.
***************************************************************************)
THEOREM EnabledDecide ==
    ASSUME LivenessAssumptions, NEW U \in SUBSET Replicas
    PROVE  LiveState /\ StableOn(U) /\ CanDecide
              => ENABLED <<DecideAction>>_vars
<1> SUFFICES ASSUME LiveState, StableOn(U), CanDecide
             PROVE  ENABLED <<DecideAction>>_vars
  OBVIOUS
<1>1. Len(consensusLog) < MaxSlots
  BY DEF CanDecide
<1>2. PICK item \in proposed : item.rid \notin LogRids
  BY DEF CanDecide
<1>3. /\ proposed \subseteq ResponseItems
      /\ consensusLog \in Seq(Seq(ResponseItems))
  BY DEF LiveState, ValidityInv, ValidityTypeOK
<1>4. item \in ResponseItems
  BY <1>2, <1>3
<1>5. DecidedRequestIds = LogRids
  BY <1>3, DecidedIsLogRids
<1>6. item \in UndecidedProposals
  BY <1>2, <1>5 DEF UndecidedProposals
<1>7. item \in EligibleProposalItems
  BY <1>6 DEF EligibleProposalItems, LivenessAssumptions
<1>8. Append(consensusLog, <<item>>) # consensusLog
  <2>1. Len(Append(consensusLog, <<item>>)) = Len(consensusLog) + 1
    BY <1>3
  <2>2. Len(consensusLog) \in Nat
    BY <1>3
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>4, <1>7, <1>8, DecideOneStep

(***************************************************************************
CG3(3): a replica in U learns an agreed index it has not learned yet.
***************************************************************************)
THEOREM EnabledLearn ==
    ASSUME LivenessAssumptions, NEW U \in SUBSET Replicas
    PROVE  LiveState /\ StableOn(U) /\ CanLearn(U)
              => ENABLED <<LearnAction>>_vars
<1> SUFFICES ASSUME LiveState, StableOn(U), CanLearn(U)
             PROVE  ENABLED <<LearnAction>>_vars
  OBVIOUS
<1>1. PICK r0 \in U :
        \E slot \in 1..Len(consensusLog) : slot \notin learned[r0]
  BY DEF CanLearn
<1>2. PICK r \in Replicas : r = r0 /\ r \in up
  BY <1>1, StableFacts
<1>3. PICK s \in 1..Len(consensusLog) : s \notin learned[r]
  BY <1>1, <1>2
<1>4. /\ learned \in [Replicas -> SUBSET (1..MaxSlots)]
      /\ Len(consensusLog) <= MaxSlots
      /\ consensusLog \in Seq(Seq(ResponseItems))
  BY DEF LiveState, LiveInv, ValidityInv, ValidityTypeOK
<1>5. s \in 1..MaxSlots
  BY <1>4, ConstantAssumptions
<1>6. [learned EXCEPT ![r] = @ \union {s}] # learned
  BY <1>3, <1>4
<1> QED
  BY <1>2, <1>3, <1>5, <1>6, LearnStep

(***************************************************************************
L4: a replica in U processes the next index once it has learned it.
***************************************************************************)
THEOREM EnabledProcess ==
    ASSUME LivenessAssumptions, NEW U \in SUBSET Replicas
    PROVE  LiveState /\ StableOn(U) /\ CanProcess(U)
              => ENABLED <<ProcessAction>>_vars
<1> SUFFICES ASSUME LiveState, StableOn(U), CanProcess(U)
             PROVE  ENABLED <<ProcessAction>>_vars
  OBVIOUS
<1>1. PICK r0 \in U :
        /\ processed[r0] < Len(consensusLog)
        /\ processed[r0] + 1 \in learned[r0]
  BY DEF CanProcess
<1>2. PICK r \in Replicas : r = r0 /\ r \in up
  BY <1>1, StableFacts
<1>3. /\ processed[r] < Len(consensusLog)
      /\ processed[r] + 1 \in learned[r]
  BY <1>1, <1>2
<1>4. /\ processed \in [Replicas -> Nat]
      /\ consensusLog \in Seq(Seq(ResponseItems))
  BY DEF LiveState, ValidityInv, ValidityTypeOK
<1>5. processed[r] + 1 \in 1..Len(consensusLog)
  BY <1>3, <1>4
<1>6. [processed EXCEPT ![r] = processed[r] + 1] # processed
  BY <1>4
<1> QED
  BY <1>2, <1>3, <1>5, <1>6, ProcessStep
=============================================================================

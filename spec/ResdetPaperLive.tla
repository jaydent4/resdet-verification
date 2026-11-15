-------------------------- MODULE ResdetPaperLive --------------------------
(***************************************************************************
TLAPS proofs about ResdetPaper.tla, part 2 of 5: what the liveness proofs
build on.

  - AcceptedProgress, the invariant that ties a leader's request-
    deduplication state to work that is still under way: a request the
    leader accepted in its current term has a nested call in flight, a
    response waiting to be proposed, a proposal pending, or an agreed
    entry. It is what makes "is_request_duplicate returned true" harmless
    in Lemma 3, and it holds only because that state is cleared when a
    replica becomes leader.
  - One lemma per fairness family, giving the instance for one request id,
    entry, proposal, or index.
  - One lemma per fair action, saying when that instance is enabled.

LiveHyp is what a liveness proof may assume about a behavior from any
point on; unlike LiveSpec it does not mention the initial state.
***************************************************************************)
EXTENDS ResdetPaperSafety

InFlight(l, x) == x \in calling[l]

HasReady(l, x) == \E y \in Responses : Entry(x, y) \in ready[l]

HasPending(l, x) ==
    \E y \in Responses : Proposal(Entry(x, y), l) \in pending

AcceptedProgress ==
    leader # NoLeader =>
        \A x \in accepted[leader] :
            \/ InFlight(leader, x)
            \/ HasReady(leader, x)
            \/ HasPending(leader, x)
            \/ Agreed(x)

LiveState == PaperInv /\ AcceptedProgress

LiveHyp == []LiveState /\ [][Next]_vars /\ []Fairness

(***************************************************************************
AcceptedProgress is an invariant.
***************************************************************************)
LEMMA LiveInit == Init => AcceptedProgress
<1> SUFFICES ASSUME Init, leader # NoLeader, NEW x \in accepted[leader]
             PROVE  FALSE
  BY DEF AcceptedProgress
<1>1. leader \in Replicas
  BY DEF Init
<1>2. accepted[leader] = {}
  BY <1>1 DEF Init
<1> QED
  BY <1>2

(* What AcceptedProgress says about the next state, written out. *)
ProgressAfter(x) ==
    \/ x \in calling'[leader']
    \/ \E y \in Responses : Entry(x, y) \in ready'[leader']
    \/ \E y \in Responses : Proposal(Entry(x, y), leader') \in pending'
    \/ \E i \in 1..Len(agreed') : agreed'[i].rid = x

LEMMA LiveStep ==
    PaperInv /\ PaperInv' /\ AcceptedProgress /\ [Next]_vars
        => AcceptedProgress'
<1> SUFFICES ASSUME PaperInv, PaperInv', AcceptedProgress, [Next]_vars,
                    leader' # NoLeader,
                    NEW x \in accepted'[leader']
             PROVE  ProgressAfter(x)
  BY DEF AcceptedProgress, InFlight, HasReady, HasPending, Agreed,
         ProgressAfter
<1>t. /\ leader \in Replicas \union {NoLeader}
      /\ accepted \in [Replicas -> SUBSET Rids]
      /\ calling \in [Replicas -> SUBSET Rids]
      /\ ready \in [Replicas -> SUBSET Entries]
      /\ pending \subseteq Proposals
      /\ agreed \in Seq(Entries)
  BY DEF PaperInv, PaperTypeOK
<1>n. NoLeader \notin Replicas
  BY PaperAssumptions
(* The current state's disjunct for a request the leader has accepted. *)
<1>old. ASSUME leader # NoLeader, x \in accepted[leader]
        PROVE  \/ x \in calling[leader]
               \/ \E y \in Responses : Entry(x, y) \in ready[leader]
               \/ \E y \in Responses :
                     Proposal(Entry(x, y), leader) \in pending
               \/ \E i \in 1..Len(agreed) : agreed[i].rid = x
  BY <1>old DEF AcceptedProgress, InFlight, HasReady, HasPending, Agreed
(* Nothing the invariant reads changes. *)
<1>same. ASSUME UNCHANGED <<leader, accepted, calling, ready, pending,
                             agreed>>
         PROVE  ProgressAfter(x)
  BY <1>same, <1>old DEF ProgressAfter
<1>1. CASE \E x0 \in Rids : Submit(x0)
  BY <1>1, <1>same DEF Submit
<1>2. CASE \E l \in Replicas : Elect(l)
  <2>1. PICK l \in Replicas : Elect(l)
    BY <1>2
  <2>2. leader' = l /\ accepted' = [accepted EXCEPT ![l] = {}]
    BY <2>1 DEF Elect
  <2>3. accepted'[leader'] = {}
    BY <2>2, <1>t
  <2> QED
    BY <2>3
<1>3. CASE \E r \in Replicas : Crash(r)
  <2>1. PICK r \in Replicas : Crash(r)
    BY <1>3
  <2>2. /\ leader' = IF leader = r THEN NoLeader ELSE leader
        /\ UNCHANGED <<accepted, calling, ready, pending, agreed>>
    BY <2>1 DEF Crash
  <2>3. leader' = leader
    BY <2>2
  <2> QED
    BY <2>2, <2>3, <1>same
<1>4. CASE \E x0 \in Rids : Accept(x0)
  <2>1. PICK x0 \in Rids : Accept(x0)
    BY <1>4
  <2>2. /\ leader # NoLeader
        /\ accepted' = [accepted EXCEPT ![leader] = @ \union {x0}]
        /\ calling' = [calling EXCEPT ![leader] = @ \union {x0}]
        /\ UNCHANGED <<leader, ready, pending, agreed>>
    BY <2>1 DEF Accept
  <2>3. leader \in Replicas
    BY <2>2, <1>t
  <2>4. /\ accepted'[leader] = accepted[leader] \union {x0}
        /\ calling'[leader] = calling[leader] \union {x0}
    BY <2>2, <2>3, <1>t
  <2>5. CASE x = x0
    BY <2>2, <2>4, <2>5 DEF ProgressAfter
  <2>6. CASE x # x0
    <3>1. x \in accepted[leader]
      BY <2>2, <2>4, <2>6
    <3>2. \/ x \in calling[leader]
          \/ \E y \in Responses : Entry(x, y) \in ready[leader]
          \/ \E y \in Responses :
                Proposal(Entry(x, y), leader) \in pending
          \/ \E i \in 1..Len(agreed) : agreed[i].rid = x
      BY <2>2, <3>1, <1>old
    <3> QED
      BY <2>2, <2>4, <3>2 DEF ProgressAfter
  <2> QED
    BY <2>5, <2>6
<1>5. CASE \E l \in Replicas, x0 \in Rids, y0 \in Responses :
              Respond(l, x0, y0)
  <2>1. PICK l \in Replicas, x0 \in Rids, y0 \in Responses :
            Respond(l, x0, y0)
    BY <1>5
  <2>2. /\ calling' = [calling EXCEPT ![l] = @ \ {x0}]
        /\ ready' = [ready EXCEPT ![l] = @ \union {Entry(x0, y0)}]
        /\ UNCHANGED <<leader, accepted, pending, agreed>>
    BY <2>1 DEF Respond
  <2>3. leader # NoLeader /\ leader \in Replicas /\ x \in accepted[leader]
    BY <2>2, <1>t
  <2>4. \/ x \in calling[leader]
        \/ \E y \in Responses : Entry(x, y) \in ready[leader]
        \/ \E y \in Responses : Proposal(Entry(x, y), leader) \in pending
        \/ \E i \in 1..Len(agreed) : agreed[i].rid = x
    BY <2>3, <1>old
  <2>5. /\ calling'[leader] =
              IF leader = l THEN calling[leader] \ {x0} ELSE calling[leader]
        /\ ready'[leader] =
              IF leader = l THEN ready[leader] \union {Entry(x0, y0)}
              ELSE ready[leader]
    BY <2>2, <2>3, <1>t
  <2>6. CASE x \in calling[leader]
    <3>1. CASE leader = l /\ x = x0
      <4>1. Entry(x, y0) \in ready'[leader']
        BY <2>2, <2>5, <3>1
      <4> QED
        BY <4>1 DEF ProgressAfter
    <3>2. CASE ~(leader = l /\ x = x0)
      <4>1. x \in calling'[leader']
        BY <2>2, <2>5, <2>6, <3>2
      <4> QED
        BY <4>1 DEF ProgressAfter
    <3> QED
      BY <3>1, <3>2
  <2>7. CASE \E y \in Responses : Entry(x, y) \in ready[leader]
    <3>1. PICK y \in Responses : Entry(x, y) \in ready[leader]
      BY <2>7
    <3>2. Entry(x, y) \in ready'[leader']
      BY <2>2, <2>5, <3>1
    <3> QED
      BY <3>2 DEF ProgressAfter
  <2>8. CASE \/ \E y \in Responses :
                  Proposal(Entry(x, y), leader) \in pending
             \/ \E i \in 1..Len(agreed) : agreed[i].rid = x
    BY <2>2, <2>8 DEF ProgressAfter
  <2> QED
    BY <2>4, <2>6, <2>7, <2>8
<1>6. CASE \E l \in Replicas, e \in Entries : Propose(l, e)
  <2>1. PICK l \in Replicas, e \in Entries : Propose(l, e)
    BY <1>6
  <2>2. /\ ready' = [ready EXCEPT ![l] = @ \ {e}]
        /\ pending' =
              IF leader = l THEN pending \union {Proposal(e, l)}
              ELSE pending
        /\ UNCHANGED <<leader, accepted, calling, agreed>>
    BY <2>1 DEF Propose
  <2>3. leader # NoLeader /\ leader \in Replicas /\ x \in accepted[leader]
    BY <2>2, <1>t
  <2>4. \/ x \in calling[leader]
        \/ \E y \in Responses : Entry(x, y) \in ready[leader]
        \/ \E y \in Responses : Proposal(Entry(x, y), leader) \in pending
        \/ \E i \in 1..Len(agreed) : agreed[i].rid = x
    BY <2>3, <1>old
  <2>5. ready'[leader] =
            IF leader = l THEN ready[leader] \ {e} ELSE ready[leader]
    BY <2>2, <2>3, <1>t
  <2>6. pending \subseteq pending'
    BY <2>2
  <2>7. CASE \E y \in Responses : Entry(x, y) \in ready[leader]
    <3>1. PICK y \in Responses : Entry(x, y) \in ready[leader]
      BY <2>7
    <3>2. CASE leader = l /\ e = Entry(x, y)
      <4>1. Proposal(Entry(x, y), leader') \in pending'
        BY <2>2, <3>2
      <4> QED
        BY <4>1 DEF ProgressAfter
    <3>3. CASE ~(leader = l /\ e = Entry(x, y))
      <4>1. Entry(x, y) \in ready'[leader']
        BY <2>2, <2>5, <3>1, <3>3
      <4> QED
        BY <4>1 DEF ProgressAfter
    <3> QED
      BY <3>2, <3>3
  <2>8. CASE \E y \in Responses : Proposal(Entry(x, y), leader) \in pending
    <3>1. PICK y \in Responses : Proposal(Entry(x, y), leader) \in pending
      BY <2>8
    <3>2. Proposal(Entry(x, y), leader') \in pending'
      BY <2>2, <2>6, <3>1
    <3> QED
      BY <3>2 DEF ProgressAfter
  <2>9. CASE \/ x \in calling[leader]
             \/ \E i \in 1..Len(agreed) : agreed[i].rid = x
    BY <2>2, <2>9 DEF ProgressAfter
  <2> QED
    BY <2>4, <2>7, <2>8, <2>9
<1>7. CASE \E p \in Proposals : Agree(p)
  <2>1. PICK p \in Proposals : Agree(p)
    BY <1>7
  <2>2. /\ p \in pending
        /\ agreed' = Append(agreed, p.entry)
        /\ pending' = pending \ {p}
        /\ UNCHANGED <<leader, accepted, calling, ready>>
    BY <2>1 DEF Agree
  <2>3. leader # NoLeader /\ leader \in Replicas /\ x \in accepted[leader]
    BY <2>2, <1>t
  <2>4. \/ x \in calling[leader]
        \/ \E y \in Responses : Entry(x, y) \in ready[leader]
        \/ \E y \in Responses : Proposal(Entry(x, y), leader) \in pending
        \/ \E i \in 1..Len(agreed) : agreed[i].rid = x
    BY <2>3, <1>old
  <2>5. /\ Len(agreed) \in Nat
        /\ Len(agreed') = Len(agreed) + 1
        /\ \A i \in 1..Len(agreed) : agreed'[i] = agreed[i]
        /\ agreed'[Len(agreed) + 1] = p.entry
    BY <2>2, <1>t
  <2>6. CASE \E i \in 1..Len(agreed) : agreed[i].rid = x
    <3>1. PICK i \in 1..Len(agreed) : agreed[i].rid = x
      BY <2>6
    <3>2. i \in 1..Len(agreed') /\ agreed'[i].rid = x
      BY <2>5, <3>1
    <3> QED
      BY <3>2 DEF ProgressAfter
  <2>7. CASE \E y \in Responses : Proposal(Entry(x, y), leader) \in pending
    <3>1. PICK y \in Responses : Proposal(Entry(x, y), leader) \in pending
      BY <2>7
    <3>2. CASE p = Proposal(Entry(x, y), leader)
      <4>1. p.entry.rid = x
        BY <3>2 DEF Proposal, Entry
      <4>2. Len(agreed) + 1 \in 1..Len(agreed')
        BY <2>5
      <4>3. agreed'[Len(agreed) + 1].rid = x
        BY <2>5, <4>1
      <4> QED
        BY <4>2, <4>3 DEF ProgressAfter
    <3>3. CASE p # Proposal(Entry(x, y), leader)
      <4>1. Proposal(Entry(x, y), leader') \in pending'
        BY <2>2, <3>1, <3>3
      <4> QED
        BY <4>1 DEF ProgressAfter
    <3> QED
      BY <3>2, <3>3
  <2>8. CASE \/ x \in calling[leader]
             \/ \E y \in Responses : Entry(x, y) \in ready[leader]
    BY <2>2, <2>8 DEF ProgressAfter
  <2> QED
    BY <2>4, <2>6, <2>7, <2>8
<1>8. CASE \E p \in Proposals : Drop(p)
  <2>1. PICK p \in Proposals : Drop(p)
    BY <1>8
  <2>2. /\ p.proposer # leader
        /\ pending' = pending \ {p}
        /\ UNCHANGED <<leader, accepted, calling, ready, agreed>>
    BY <2>1 DEF Drop
  <2>3. leader # NoLeader /\ leader \in Replicas /\ x \in accepted[leader]
    BY <2>2, <1>t
  <2>4. \/ x \in calling[leader]
        \/ \E y \in Responses : Entry(x, y) \in ready[leader]
        \/ \E y \in Responses : Proposal(Entry(x, y), leader) \in pending
        \/ \E i \in 1..Len(agreed) : agreed[i].rid = x
    BY <2>3, <1>old
  <2>5. CASE \E y \in Responses : Proposal(Entry(x, y), leader) \in pending
    <3>1. PICK y \in Responses : Proposal(Entry(x, y), leader) \in pending
      BY <2>5
    <3>2. Proposal(Entry(x, y), leader).proposer = leader
      BY DEF Proposal
    <3>3. Proposal(Entry(x, y), leader') \in pending'
      BY <2>2, <3>1, <3>2
    <3> QED
      BY <3>3 DEF ProgressAfter
  <2>6. CASE \/ x \in calling[leader]
             \/ \E y \in Responses : Entry(x, y) \in ready[leader]
             \/ \E i \in 1..Len(agreed) : agreed[i].rid = x
    BY <2>2, <2>6 DEF ProgressAfter
  <2> QED
    BY <2>4, <2>5, <2>6
<1>9. CASE \E r \in Replicas, k \in Nat : Learn(r, k)
  BY <1>9, <1>same DEF Learn
<1>10. CASE \E r \in Replicas : Process(r)
  BY <1>10, <1>same DEF Process
<1>11. CASE UNCHANGED vars
  BY <1>11, <1>same DEF vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11
     DEF Next

THEOREM LiveStateInvariant == Spec => []LiveState
<1>1. Init => AcceptedProgress
  BY LiveInit
<1>2. PaperInv /\ PaperInv' /\ AcceptedProgress /\ [Next]_vars
          => AcceptedProgress'
  BY LiveStep
<1>3. Spec => []PaperInv
  BY PaperInvariant
<1> QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec, LiveState

(* LiveSpec satisfies LiveHyp, so results proved from LiveHyp hold of it. *)
THEOREM LiveSpecHyp == LiveSpec => LiveHyp
BY LiveStateInvariant, PTL DEF LiveSpec, LiveHyp, Spec

(***************************************************************************
Fairness instances.
***************************************************************************)
LEMMA AcceptFairAt ==
    ASSUME NEW x \in Rids
    PROVE  AcceptFair => WF_vars(Accept(x))
BY DEF AcceptFair

LEMMA RespondFairAt ==
    ASSUME NEW l \in Replicas, NEW x \in Rids
    PROVE  RespondFair => WF_vars(RespondSome(l, x))
BY DEF RespondFair

LEMMA ProposeFairAt ==
    ASSUME NEW l \in Replicas, NEW e \in Entries
    PROVE  ProposeFair => WF_vars(Propose(l, e))
BY DEF ProposeFair

LEMMA AgreeFairAt ==
    ASSUME NEW p \in Proposals
    PROVE  AgreeFair => WF_vars(Agree(p))
BY DEF AgreeFair

LEMMA LearnFairAt ==
    ASSUME NEW r \in Replicas, NEW k \in Nat
    PROVE  LearnFair => WF_vars(Learn(r, k))
BY DEF LearnFair

LEMMA ProcessFairAt ==
    ASSUME NEW r \in Replicas
    PROVE  ProcessFair => WF_vars(Process(r))
BY DEF ProcessFair

(***************************************************************************
Enabledness of each fair action instance.

Each "Step" lemma says: if the guards of one action instance hold, written
exactly as in ResdetPaper.tla, and the instance's update really changes a
variable, then <<A>>_vars is enabled. ExpandENABLED turns that into: there
are values for the twelve primed variables that satisfy A and are not all
equal to the current ones. The default backends do not find those values
reliably, so Isabelle gets a fixed script that builds them with no search:
unknowns for the primed variables, then conjunct by conjunct, an update
x' = e fixes the unknown for x' by reflexivity and a guard is one of the
hypotheses; finally, if nothing had changed, the changed variable would
equal its old value, contradicting the last hypothesis. (RespondSome has a
quantifier, whose witness is read off the hypothesis y \in Responses.
Process updates dset and delivered under an IF, so it has one Step lemma
per branch, with the branch condition as a hypothesis.) The script is
repeated inline because TLAPS accepts a backend pragma only when it is
written out in the BY clause; ResdetLiveEnabled.tla explains it step by
step.

The "Enabled" lemmas establish the guards from LiveState and cite the
Step lemma. They use no ENABLED reasoning of their own.
***************************************************************************)
LEMMA AcceptStep ==
    ASSUME NEW x \in Rids,
           leader # NoLeader,
           x \in submitted,
           x \notin accepted[leader],
           [accepted EXCEPT ![leader] = @ \union {x}] # accepted
    PROVE  ENABLED <<Accept(x)>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF Accept, vars

LEMMA RespondStep ==
    ASSUME NEW l \in Replicas, NEW x \in Rids, NEW y \in Responses,
           l \in up,
           x \in calling[l],
           [calling EXCEPT ![l] = @ \ {x}] # calling
    PROVE  ENABLED <<RespondSome(l, x)>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac bExI, erule_tac asm_rl)+, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF RespondSome, Respond, vars

LEMMA ProposeStep ==
    ASSUME NEW l \in Replicas, NEW e \in Entries,
           l \in up,
           e \in ready[l],
           [ready EXCEPT ![l] = @ \ {e}] # ready
    PROVE  ENABLED <<Propose(l, e)>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF Propose, vars

LEMMA AgreeStep ==
    ASSUME NEW p \in Proposals,
           p \in pending,
           Append(agreed, p.entry) # agreed
    PROVE  ENABLED <<Agree(p)>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF Agree, vars

LEMMA LearnStep ==
    ASSUME NEW r \in Replicas, NEW k \in Nat,
           r \in up,
           k \in 1..Len(agreed),
           k \notin DOMAIN log[r],
           [log EXCEPT ![r] =
               [i \in DOMAIN @ \union {k} |->
                   IF i = k THEN agreed[k] ELSE @[i]]] # log
    PROVE  ENABLED <<Learn(r, k)>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF Learn, vars

LEMMA ProcessStepSeen ==
    ASSUME NEW r \in Replicas,
           r \in up,
           processed[r] + 1 \in DOMAIN log[r],
           log[r][processed[r] + 1].rid \in dset[r],
           [processed EXCEPT ![r] = processed[r] + 1] # processed
    PROVE  ENABLED <<Process(r)>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF Process, vars

LEMMA ProcessStepNew ==
    ASSUME NEW r \in Replicas,
           r \in up,
           processed[r] + 1 \in DOMAIN log[r],
           log[r][processed[r] + 1].rid \notin dset[r],
           [processed EXCEPT ![r] = processed[r] + 1] # processed
    PROVE  ENABLED <<Process(r)>>_vars
BY ExpandENABLED,
   IsaM("((rule_tac exI)+, rule_tac conjI, (rule_tac conjI, (rule_tac refl | erule_tac asm_rl | simp))+, (rule_tac refl | erule_tac asm_rl | simp), rule_tac notI, (erule_tac conjE)+, erule_tac notE, erule_tac asm_rl)")
   DEF Process, vars

LEMMA EnabledAccept ==
    ASSUME NEW x \in Rids
    PROVE  LiveState /\ leader # NoLeader /\ x \in submitted
               /\ x \notin accepted[leader]
           => ENABLED <<Accept(x)>>_vars
<1> SUFFICES ASSUME LiveState, leader # NoLeader, x \in submitted,
                    x \notin accepted[leader]
             PROVE  ENABLED <<Accept(x)>>_vars
  OBVIOUS
<1>1. /\ leader \in Replicas
      /\ accepted \in [Replicas -> SUBSET Rids]
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. [accepted EXCEPT ![leader] = @ \union {x}][leader] # accepted[leader]
  BY <1>1
<1>3. [accepted EXCEPT ![leader] = @ \union {x}] # accepted
  BY <1>2
<1> QED
  BY <1>3, AcceptStep

LEMMA EnabledRespond ==
    ASSUME NEW l \in Replicas, NEW x \in Rids
    PROVE  LiveState /\ l \in up /\ x \in calling[l]
           => ENABLED <<RespondSome(l, x)>>_vars
<1> SUFFICES ASSUME LiveState, l \in up, x \in calling[l]
             PROVE  ENABLED <<RespondSome(l, x)>>_vars
  OBVIOUS
<1>1. calling \in [Replicas -> SUBSET Rids]
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. PICK y \in Responses : TRUE
  BY PaperAssumptions
<1>3. [calling EXCEPT ![l] = @ \ {x}][l] # calling[l]
  BY <1>1
<1>4. [calling EXCEPT ![l] = @ \ {x}] # calling
  BY <1>3
<1> QED
  BY <1>4, RespondStep

LEMMA EnabledPropose ==
    ASSUME NEW l \in Replicas, NEW e \in Entries
    PROVE  LiveState /\ l \in up /\ e \in ready[l]
           => ENABLED <<Propose(l, e)>>_vars
<1> SUFFICES ASSUME LiveState, l \in up, e \in ready[l]
             PROVE  ENABLED <<Propose(l, e)>>_vars
  OBVIOUS
<1>1. ready \in [Replicas -> SUBSET Entries]
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. [ready EXCEPT ![l] = @ \ {e}][l] # ready[l]
  BY <1>1
<1>3. [ready EXCEPT ![l] = @ \ {e}] # ready
  BY <1>2
<1> QED
  BY <1>3, ProposeStep

LEMMA EnabledAgree ==
    ASSUME NEW p \in Proposals
    PROVE  LiveState /\ p \in pending => ENABLED <<Agree(p)>>_vars
<1> SUFFICES ASSUME LiveState, p \in pending
             PROVE  ENABLED <<Agree(p)>>_vars
  OBVIOUS
<1>1. agreed \in Seq(Entries)
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. Len(agreed) \in Nat /\ Len(Append(agreed, p.entry)) = Len(agreed) + 1
  BY <1>1
<1>3. Append(agreed, p.entry) # agreed
  BY <1>2
<1> QED
  BY <1>3, AgreeStep

LEMMA EnabledLearn ==
    ASSUME NEW r \in Replicas, NEW k \in Nat
    PROVE  LiveState /\ r \in up /\ k \in 1..Len(agreed)
               /\ k \notin DOMAIN log[r]
           => ENABLED <<Learn(r, k)>>_vars
<1> SUFFICES ASSUME LiveState, r \in up, k \in 1..Len(agreed),
                    k \notin DOMAIN log[r]
             PROVE  ENABLED <<Learn(r, k)>>_vars
  OBVIOUS
<1> DEFINE extended == [i \in DOMAIN log[r] \union {k} |->
                           IF i = k THEN agreed[k] ELSE log[r][i]]
<1>1. DOMAIN log = Replicas
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. [log EXCEPT ![r] =
          [i \in DOMAIN @ \union {k} |->
              IF i = k THEN agreed[k] ELSE @[i]]][r] = extended
  BY <1>1
<1>3. k \in DOMAIN extended
  OBVIOUS
<1>4. extended # log[r]
  BY <1>3
<1> HIDE DEF extended
<1>5. [log EXCEPT ![r] =
          [i \in DOMAIN @ \union {k} |->
              IF i = k THEN agreed[k] ELSE @[i]]] # log
  BY <1>2, <1>4
<1> QED
  BY <1>5, LearnStep

LEMMA EnabledProcess ==
    ASSUME NEW r \in Replicas
    PROVE  LiveState /\ r \in up /\ processed[r] + 1 \in DOMAIN log[r]
           => ENABLED <<Process(r)>>_vars
<1> SUFFICES ASSUME LiveState, r \in up, processed[r] + 1 \in DOMAIN log[r]
             PROVE  ENABLED <<Process(r)>>_vars
  OBVIOUS
<1>1. processed \in [Replicas -> Nat]
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. [processed EXCEPT ![r] = processed[r] + 1][r] # processed[r]
  BY <1>1
<1>3. [processed EXCEPT ![r] = processed[r] + 1] # processed
  BY <1>2
<1>4. CASE log[r][processed[r] + 1].rid \in dset[r]
  BY <1>3, <1>4, ProcessStepSeen
<1>5. CASE log[r][processed[r] + 1].rid \notin dset[r]
  BY <1>3, <1>5, ProcessStepNew
<1> QED
  BY <1>4, <1>5
=============================================================================

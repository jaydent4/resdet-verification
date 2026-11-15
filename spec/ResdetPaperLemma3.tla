------------------------- MODULE ResdetPaperLemma3 -------------------------
(***************************************************************************
TLAPS proofs about ResdetPaper.tla, part 3 of 5.

Lemma 3 (Eventual agreement). For every logical request with request id x
submitted, some entry (x, y) is eventually agreed at some index, provided
a leader l is eventually in place for good (CG3(1)).

The proof follows the paper's: the request reaches the leader's handler
(L1, L2, L4); either the handler accepts it or it is a duplicate, and then
by AcceptedProgress it was accepted earlier in the same term; the nested
call returns (L3); the handler proposes (L4); the proposal is agreed
(CG3(2)), since the proposal of a leader that stays is never lost.

How the module is organised. Each stage is a weak-fairness argument for
one action instance, and is proved from three facts about single steps:
the stage's condition persists until its goal holds, a step of the fair
action reaches the goal, and the condition enables the action. Those
facts are separate lemmas over constants only, because the temporal
prover may use a fact at a later point of a behavior only if it was
proved without assuming anything about the current state. Two stages
start from a response or a proposal that is chosen from the state reached
so far; for those, a lemma about a fixed entry or proposal is proved
first, and a second lemma picks the entry from the state.
***************************************************************************)
EXTENDS ResdetPaperLive

(* State predicates of the stages, named so that every fact below refers
   to them in the same form. *)
Led(l) == leader = l

Sub(x) == x \in submitted

Acc(l, x) == x \in accepted[l]

ReadyE(l, e) == e \in ready[l]

PendingE(l, e) == Proposal(e, l) \in pending

InPending(p) == p \in pending

(* From some point on: the usual liveness hypotheses, and l is the leader
   for good. *)
LedHyp(l) == LiveHyp /\ []Led(l)

(***************************************************************************
What a reachable state with leader l provides.
***************************************************************************)
LEMMA LedFacts ==
    ASSUME NEW l \in Replicas
    PROVE  LiveState /\ Led(l) =>
               /\ PaperTypeOK
               /\ leader # NoLeader
               /\ l \in up
               /\ AcceptedProgress
BY PaperAssumptions DEF LiveState, PaperInv, LeaderUp, Led

(***************************************************************************
Stage A: a submitted request is accepted by the leader (L1, L2, L4).
***************************************************************************)
LEMMA SubStable ==
    ASSUME NEW x \in Rids
    PROVE  Sub(x) /\ [Next]_vars => Sub(x)'
<1> SUFFICES ASSUME Sub(x), [Next]_vars
             PROVE  Sub(x)'
  OBVIOUS
<1>1. CASE \E x2 \in Rids : Submit(x2)
  BY <1>1 DEF Submit, Sub
<1>2. CASE \E l2 \in Replicas : Elect(l2)
  BY <1>2 DEF Elect, Sub
<1>3. CASE \E r \in Replicas : Crash(r)
  BY <1>3 DEF Crash, Sub
<1>4. CASE \E x2 \in Rids : Accept(x2)
  BY <1>4 DEF Accept, Sub
<1>5. CASE \E l2 \in Replicas, x2 \in Rids, y2 \in Responses :
              Respond(l2, x2, y2)
  BY <1>5 DEF Respond, Sub
<1>6. CASE \E l2 \in Replicas, e2 \in Entries : Propose(l2, e2)
  BY <1>6 DEF Propose, Sub
<1>7. CASE \E p2 \in Proposals : Agree(p2)
  BY <1>7 DEF Agree, Sub
<1>8. CASE \E p2 \in Proposals : Drop(p2)
  BY <1>8 DEF Drop, Sub
<1>9. CASE \E r \in Replicas, k \in Nat : Learn(r, k)
  BY <1>9 DEF Learn, Sub
<1>10. CASE \E r \in Replicas : Process(r)
  BY <1>10 DEF Process, Sub
<1>11. CASE UNCHANGED vars
  BY <1>11 DEF vars, Sub
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11
     DEF Next

LEMMA AcceptReaches ==
    ASSUME NEW x \in Rids, NEW l \in Replicas
    PROVE  LiveState /\ Led(l) /\ <<Accept(x)>>_vars => Acc(l, x)'
<1> SUFFICES ASSUME LiveState, Led(l), Accept(x)
             PROVE  Acc(l, x)'
  OBVIOUS
<1>1. accepted \in [Replicas -> SUBSET Rids]
  BY LedFacts DEF PaperTypeOK
<1>2. accepted' = [accepted EXCEPT ![l] = @ \union {x}]
  BY DEF Accept, Led
<1> QED
  BY <1>1, <1>2 DEF Acc

LEMMA AcceptEnabled ==
    ASSUME NEW x \in Rids, NEW l \in Replicas
    PROVE  LiveState /\ Led(l) /\ Sub(x) /\ ~Acc(l, x)
           => ENABLED <<Accept(x)>>_vars
<1>1. LiveState /\ Led(l) /\ Sub(x) /\ ~Acc(l, x) =>
          /\ LiveState
          /\ leader # NoLeader
          /\ x \in submitted
          /\ x \notin accepted[leader]
  BY LedFacts DEF Led, Sub, Acc
<1> QED
  BY <1>1, EnabledAccept

LEMMA StageA ==
    ASSUME NEW x \in Rids, NEW l \in Replicas
    PROVE  LedHyp(l) => [](Sub(x) => <>Acc(l, x))
<1>1. Sub(x) /\ [Next]_vars => Sub(x)'
  BY SubStable
<1>2. LiveState /\ Led(l) /\ <<Accept(x)>>_vars => Acc(l, x)'
  BY AcceptReaches
<1>3. LiveState /\ Led(l) /\ Sub(x) /\ ~Acc(l, x)
      => ENABLED <<Accept(x)>>_vars
  BY AcceptEnabled
<1>4. Fairness => WF_vars(Accept(x))
  BY AcceptFairAt DEF Fairness
<1>5. LedHyp(l) => WF_vars(Accept(x))
  BY <1>4, PTL DEF LedHyp, LiveHyp
<1>6. []LiveState /\ [][Next]_vars /\ []Led(l) /\ WF_vars(Accept(x))
      => [](Sub(x) => <>Acc(l, x))
  BY <1>1, <1>2, <1>3, PTL
<1> QED
  BY <1>5, <1>6, PTL DEF LedHyp, LiveHyp

(***************************************************************************
An accepted request is under way: the invariant AcceptedProgress at the
leader l. This is where "is_request_duplicate returned true" is handled.
***************************************************************************)
LEMMA AcceptedUnderWay ==
    ASSUME NEW x \in Rids, NEW l \in Replicas
    PROVE  LiveState /\ Led(l) /\ Acc(l, x) =>
               \/ InFlight(l, x)
               \/ HasReady(l, x)
               \/ HasPending(l, x)
               \/ Agreed(x)
<1> SUFFICES ASSUME LiveState, Led(l), Acc(l, x)
             PROVE  \/ InFlight(l, x)
                    \/ HasReady(l, x)
                    \/ HasPending(l, x)
                    \/ Agreed(x)
  OBVIOUS
<1>1. leader # NoLeader /\ AcceptedProgress
  BY LedFacts
<1>2. x \in accepted[leader]
  BY DEF Led, Acc
<1> QED
  BY <1>1, <1>2 DEF AcceptedProgress, Led

(***************************************************************************
Stage C: the nested call returns (L3).
***************************************************************************)
LEMMA InFlightStep ==
    ASSUME NEW l \in Replicas, NEW x \in Rids
    PROVE  LiveState /\ InFlight(l, x) /\ [Next]_vars
           => InFlight(l, x)' \/ HasReady(l, x)'
<1> SUFFICES ASSUME LiveState, InFlight(l, x), [Next]_vars
             PROVE  InFlight(l, x)' \/ HasReady(l, x)'
  OBVIOUS
<1>0. /\ calling \in [Replicas -> SUBSET Rids]
      /\ ready \in [Replicas -> SUBSET Entries]
      /\ x \in calling[l]
  BY DEF LiveState, PaperInv, PaperTypeOK, InFlight
<1>1. CASE \E x2 \in Rids : Submit(x2)
  BY <1>0, <1>1 DEF Submit, InFlight
<1>2. CASE \E l2 \in Replicas : Elect(l2)
  BY <1>0, <1>2 DEF Elect, InFlight
<1>3. CASE \E r \in Replicas : Crash(r)
  BY <1>0, <1>3 DEF Crash, InFlight
<1>4. CASE \E x2 \in Rids : Accept(x2)
  <2>1. PICK x2 \in Rids : Accept(x2)
    BY <1>4
  <2>2. calling' = [calling EXCEPT ![leader] = @ \union {x2}]
    BY <2>1 DEF Accept
  <2>3. x \in calling'[l]
    BY <1>0, <2>2
  <2> QED
    BY <2>3 DEF InFlight
<1>5. CASE \E l2 \in Replicas, x2 \in Rids, y2 \in Responses :
              Respond(l2, x2, y2)
  <2>1. PICK l2 \in Replicas, x2 \in Rids, y2 \in Responses :
            Respond(l2, x2, y2)
    BY <1>5
  <2>2. /\ calling' = [calling EXCEPT ![l2] = @ \ {x2}]
        /\ ready' = [ready EXCEPT ![l2] = @ \union {Entry(x2, y2)}]
    BY <2>1 DEF Respond
  <2>3. CASE l2 = l /\ x2 = x
    <3>1. Entry(x, y2) \in ready'[l]
      BY <1>0, <2>2, <2>3
    <3> QED
      BY <3>1 DEF HasReady
  <2>4. CASE ~(l2 = l /\ x2 = x)
    <3>1. x \in calling'[l]
      BY <1>0, <2>2, <2>4
    <3> QED
      BY <3>1 DEF InFlight
  <2> QED
    BY <2>3, <2>4
<1>6. CASE \E l2 \in Replicas, e2 \in Entries : Propose(l2, e2)
  BY <1>0, <1>6 DEF Propose, InFlight
<1>7. CASE \E p2 \in Proposals : Agree(p2)
  BY <1>0, <1>7 DEF Agree, InFlight
<1>8. CASE \E p2 \in Proposals : Drop(p2)
  BY <1>0, <1>8 DEF Drop, InFlight
<1>9. CASE \E r \in Replicas, k \in Nat : Learn(r, k)
  BY <1>0, <1>9 DEF Learn, InFlight
<1>10. CASE \E r \in Replicas : Process(r)
  BY <1>0, <1>10 DEF Process, InFlight
<1>11. CASE UNCHANGED vars
  BY <1>0, <1>11 DEF vars, InFlight
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11
     DEF Next

LEMMA RespondReaches ==
    ASSUME NEW l \in Replicas, NEW x \in Rids
    PROVE  LiveState /\ <<RespondSome(l, x)>>_vars => HasReady(l, x)'
<1> SUFFICES ASSUME LiveState, RespondSome(l, x)
             PROVE  HasReady(l, x)'
  OBVIOUS
<1>1. ready \in [Replicas -> SUBSET Entries]
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. PICK y \in Responses : Respond(l, x, y)
  BY DEF RespondSome
<1>3. ready' = [ready EXCEPT ![l] = @ \union {Entry(x, y)}]
  BY <1>2 DEF Respond
<1>4. Entry(x, y) \in ready'[l]
  BY <1>1, <1>3
<1> QED
  BY <1>4 DEF HasReady

LEMMA RespondEnabled ==
    ASSUME NEW l \in Replicas, NEW x \in Rids
    PROVE  LiveState /\ Led(l) /\ InFlight(l, x)
           => ENABLED <<RespondSome(l, x)>>_vars
<1>1. LiveState /\ Led(l) /\ InFlight(l, x) =>
          LiveState /\ l \in up /\ x \in calling[l]
  BY LedFacts DEF InFlight
<1> QED
  BY <1>1, EnabledRespond

LEMMA StageC ==
    ASSUME NEW l \in Replicas, NEW x \in Rids
    PROVE  LedHyp(l) => [](InFlight(l, x) => <>HasReady(l, x))
<1>1. LiveState /\ InFlight(l, x) /\ [Next]_vars
      => InFlight(l, x)' \/ HasReady(l, x)'
  BY InFlightStep
<1>2. LiveState /\ <<RespondSome(l, x)>>_vars => HasReady(l, x)'
  BY RespondReaches
<1>3. LiveState /\ Led(l) /\ InFlight(l, x)
      => ENABLED <<RespondSome(l, x)>>_vars
  BY RespondEnabled
<1>4. Fairness => WF_vars(RespondSome(l, x))
  BY RespondFairAt DEF Fairness
<1>5. LedHyp(l) => WF_vars(RespondSome(l, x))
  BY <1>4, PTL DEF LedHyp, LiveHyp
<1>6. []LiveState /\ [][Next]_vars /\ []Led(l)
          /\ WF_vars(RespondSome(l, x))
      => [](InFlight(l, x) => <>HasReady(l, x))
  BY <1>1, <1>2, <1>3, PTL
<1> QED
  BY <1>5, <1>6, PTL DEF LedHyp, LiveHyp

(***************************************************************************
Stage D, for a fixed entry e: the handler proposes it (L4), and because l
is the leader the proposal is taken.
***************************************************************************)
LEMMA ReadyStep ==
    ASSUME NEW l \in Replicas, NEW e \in Entries
    PROVE  LiveState /\ Led(l) /\ ReadyE(l, e) /\ [Next]_vars
           => ReadyE(l, e)' \/ PendingE(l, e)'
<1> SUFFICES ASSUME LiveState, Led(l), ReadyE(l, e), [Next]_vars
             PROVE  ReadyE(l, e)' \/ PendingE(l, e)'
  OBVIOUS
<1>0. /\ ready \in [Replicas -> SUBSET Entries]
      /\ e \in ready[l]
      /\ leader = l
  BY DEF LiveState, PaperInv, PaperTypeOK, ReadyE, Led
<1>1. CASE \E x2 \in Rids : Submit(x2)
  BY <1>0, <1>1 DEF Submit, ReadyE
<1>2. CASE \E l2 \in Replicas : Elect(l2)
  BY <1>0, <1>2 DEF Elect, ReadyE
<1>3. CASE \E r \in Replicas : Crash(r)
  BY <1>0, <1>3 DEF Crash, ReadyE
<1>4. CASE \E x2 \in Rids : Accept(x2)
  BY <1>0, <1>4 DEF Accept, ReadyE
<1>5. CASE \E l2 \in Replicas, x2 \in Rids, y2 \in Responses :
              Respond(l2, x2, y2)
  <2>1. PICK l2 \in Replicas, x2 \in Rids, y2 \in Responses :
            Respond(l2, x2, y2)
    BY <1>5
  <2>2. ready' = [ready EXCEPT ![l2] = @ \union {Entry(x2, y2)}]
    BY <2>1 DEF Respond
  <2>3. e \in ready'[l]
    BY <1>0, <2>2
  <2> QED
    BY <2>3 DEF ReadyE
<1>6. CASE \E l2 \in Replicas, e2 \in Entries : Propose(l2, e2)
  <2>1. PICK l2 \in Replicas, e2 \in Entries : Propose(l2, e2)
    BY <1>6
  <2>2. /\ ready' = [ready EXCEPT ![l2] = @ \ {e2}]
        /\ pending' =
             IF leader = l2
             THEN pending \union {Proposal(e2, l2)}
             ELSE pending
    BY <2>1 DEF Propose
  <2>3. CASE l2 = l /\ e2 = e
    <3>1. Proposal(e, l) \in pending'
      BY <1>0, <2>2, <2>3
    <3> QED
      BY <3>1 DEF PendingE
  <2>4. CASE ~(l2 = l /\ e2 = e)
    <3>1. e \in ready'[l]
      BY <1>0, <2>2, <2>4
    <3> QED
      BY <3>1 DEF ReadyE
  <2> QED
    BY <2>3, <2>4
<1>7. CASE \E p2 \in Proposals : Agree(p2)
  BY <1>0, <1>7 DEF Agree, ReadyE
<1>8. CASE \E p2 \in Proposals : Drop(p2)
  BY <1>0, <1>8 DEF Drop, ReadyE
<1>9. CASE \E r \in Replicas, k \in Nat : Learn(r, k)
  BY <1>0, <1>9 DEF Learn, ReadyE
<1>10. CASE \E r \in Replicas : Process(r)
  BY <1>0, <1>10 DEF Process, ReadyE
<1>11. CASE UNCHANGED vars
  BY <1>0, <1>11 DEF vars, ReadyE
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11
     DEF Next

LEMMA ProposeReaches ==
    ASSUME NEW l \in Replicas, NEW e \in Entries
    PROVE  Led(l) /\ <<Propose(l, e)>>_vars => PendingE(l, e)'
<1> SUFFICES ASSUME Led(l), Propose(l, e)
             PROVE  PendingE(l, e)'
  OBVIOUS
<1>1. pending' = pending \union {Proposal(e, l)}
  BY DEF Propose, Led
<1> QED
  BY <1>1 DEF PendingE

LEMMA ProposeEnabled ==
    ASSUME NEW l \in Replicas, NEW e \in Entries
    PROVE  LiveState /\ Led(l) /\ ReadyE(l, e)
           => ENABLED <<Propose(l, e)>>_vars
<1>1. LiveState /\ Led(l) /\ ReadyE(l, e) =>
          LiveState /\ l \in up /\ e \in ready[l]
  BY LedFacts DEF ReadyE
<1> QED
  BY <1>1, EnabledPropose

LEMMA StageD ==
    ASSUME NEW l \in Replicas, NEW e \in Entries
    PROVE  LedHyp(l) => [](ReadyE(l, e) => <>PendingE(l, e))
<1>1. LiveState /\ Led(l) /\ ReadyE(l, e) /\ [Next]_vars
      => ReadyE(l, e)' \/ PendingE(l, e)'
  BY ReadyStep
<1>2. Led(l) /\ <<Propose(l, e)>>_vars => PendingE(l, e)'
  BY ProposeReaches
<1>3. LiveState /\ Led(l) /\ ReadyE(l, e)
      => ENABLED <<Propose(l, e)>>_vars
  BY ProposeEnabled
<1>4. Fairness => WF_vars(Propose(l, e))
  BY ProposeFairAt DEF Fairness
<1>5. LedHyp(l) => WF_vars(Propose(l, e))
  BY <1>4, PTL DEF LedHyp, LiveHyp
<1>6. []LiveState /\ [][Next]_vars /\ []Led(l) /\ WF_vars(Propose(l, e))
      => [](ReadyE(l, e) => <>PendingE(l, e))
  BY <1>1, <1>2, <1>3, PTL
<1> QED
  BY <1>5, <1>6, PTL DEF LedHyp, LiveHyp

(***************************************************************************
Stage E, for a fixed proposal p made by l for request id x: consensus
agrees it (CG3(2)). While l is the leader the proposal cannot be lost.
***************************************************************************)
LEMMA AppendAgrees ==
    ASSUME NEW x \in Rids, NEW p \in Proposals, p.entry.rid = x
    PROVE  LiveState /\ agreed' = Append(agreed, p.entry) => Agreed(x)'
<1> SUFFICES ASSUME LiveState, agreed' = Append(agreed, p.entry)
             PROVE  Agreed(x)'
  OBVIOUS
<1>1. agreed \in Seq(Entries)
  BY DEF LiveState, PaperInv, PaperTypeOK
<1>2. p.entry \in Entries
  BY DEF Proposals
<1>3. /\ Len(agreed) \in Nat
      /\ Len(agreed') = Len(agreed) + 1
      /\ agreed'[Len(agreed) + 1] = p.entry
  BY <1>1, <1>2
<1>4. Len(agreed) + 1 \in 1..Len(agreed')
  BY <1>3
<1>5. \E i \in 1..Len(agreed') : agreed'[i].rid = x
  BY <1>3, <1>4
<1> QED
  BY <1>5 DEF Agreed

LEMMA PendingStep ==
    ASSUME NEW l \in Replicas, NEW x \in Rids, NEW p \in Proposals,
           p.proposer = l, p.entry.rid = x
    PROVE  LiveState /\ Led(l) /\ InPending(p) /\ [Next]_vars
           => InPending(p)' \/ Agreed(x)'
<1> SUFFICES ASSUME LiveState, Led(l), InPending(p), [Next]_vars
             PROVE  InPending(p)' \/ Agreed(x)'
  OBVIOUS
<1>0. p \in pending /\ leader = l
  BY DEF InPending, Led
<1>1. CASE \E x2 \in Rids : Submit(x2)
  BY <1>0, <1>1 DEF Submit, InPending
<1>2. CASE \E l2 \in Replicas : Elect(l2)
  BY <1>0, <1>2 DEF Elect, InPending
<1>3. CASE \E r \in Replicas : Crash(r)
  BY <1>0, <1>3 DEF Crash, InPending
<1>4. CASE \E x2 \in Rids : Accept(x2)
  BY <1>0, <1>4 DEF Accept, InPending
<1>5. CASE \E l2 \in Replicas, x2 \in Rids, y2 \in Responses :
              Respond(l2, x2, y2)
  BY <1>0, <1>5 DEF Respond, InPending
<1>6. CASE \E l2 \in Replicas, e2 \in Entries : Propose(l2, e2)
  <2>1. PICK l2 \in Replicas, e2 \in Entries : Propose(l2, e2)
    BY <1>6
  <2>2. pending' =
            IF leader = l2
            THEN pending \union {Proposal(e2, l2)}
            ELSE pending
    BY <2>1 DEF Propose
  <2>3. p \in pending'
    BY <1>0, <2>2
  <2> QED
    BY <2>3 DEF InPending
<1>7. CASE \E p2 \in Proposals : Agree(p2)
  <2>1. PICK p2 \in Proposals : Agree(p2)
    BY <1>7
  <2>2. /\ agreed' = Append(agreed, p2.entry)
        /\ pending' = pending \ {p2}
    BY <2>1 DEF Agree
  <2>3. CASE p2 = p
    BY <2>2, <2>3, AppendAgrees
  <2>4. CASE p2 # p
    <3>1. p \in pending'
      BY <1>0, <2>2, <2>4
    <3> QED
      BY <3>1 DEF InPending
  <2> QED
    BY <2>3, <2>4
<1>8. CASE \E p2 \in Proposals : Drop(p2)
  <2>1. PICK p2 \in Proposals : Drop(p2)
    BY <1>8
  <2>2. /\ p2.proposer # leader
        /\ pending' = pending \ {p2}
    BY <2>1 DEF Drop
  <2>3. p2 # p
    BY <1>0, <2>2
  <2>4. p \in pending'
    BY <1>0, <2>2, <2>3
  <2> QED
    BY <2>4 DEF InPending
<1>9. CASE \E r \in Replicas, k \in Nat : Learn(r, k)
  BY <1>0, <1>9 DEF Learn, InPending
<1>10. CASE \E r \in Replicas : Process(r)
  BY <1>0, <1>10 DEF Process, InPending
<1>11. CASE UNCHANGED vars
  BY <1>0, <1>11 DEF vars, InPending
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11
     DEF Next

LEMMA AgreeReaches ==
    ASSUME NEW x \in Rids, NEW p \in Proposals, p.entry.rid = x
    PROVE  LiveState /\ <<Agree(p)>>_vars => Agreed(x)'
<1> SUFFICES ASSUME LiveState, Agree(p)
             PROVE  Agreed(x)'
  OBVIOUS
<1>1. agreed' = Append(agreed, p.entry)
  BY DEF Agree
<1> QED
  BY <1>1, AppendAgrees

LEMMA AgreeEnabled ==
    ASSUME NEW p \in Proposals
    PROVE  LiveState /\ InPending(p) => ENABLED <<Agree(p)>>_vars
<1>1. LiveState /\ InPending(p) => LiveState /\ p \in pending
  BY DEF InPending
<1> QED
  BY <1>1, EnabledAgree

LEMMA StageE ==
    ASSUME NEW l \in Replicas, NEW x \in Rids, NEW p \in Proposals,
           p.proposer = l, p.entry.rid = x
    PROVE  LedHyp(l) => [](InPending(p) => <>Agreed(x))
<1>1. LiveState /\ Led(l) /\ InPending(p) /\ [Next]_vars
      => InPending(p)' \/ Agreed(x)'
  BY PendingStep
<1>2. LiveState /\ <<Agree(p)>>_vars => Agreed(x)'
  BY AgreeReaches
<1>3. LiveState /\ InPending(p) => ENABLED <<Agree(p)>>_vars
  BY AgreeEnabled
<1>4. Fairness => WF_vars(Agree(p))
  BY AgreeFairAt DEF Fairness
<1>5. LedHyp(l) => WF_vars(Agree(p))
  BY <1>4, PTL DEF LedHyp, LiveHyp
<1>6. []LiveState /\ [][Next]_vars /\ []Led(l) /\ WF_vars(Agree(p))
      => [](InPending(p) => <>Agreed(x))
  BY <1>1, <1>2, <1>3, PTL
<1> QED
  BY <1>5, <1>6, PTL DEF LedHyp, LiveHyp

(***************************************************************************
Stages D and E together, for a fixed entry e with request id x: once e is
waiting to be proposed at l, or already proposed by l, an entry for x is
eventually agreed.
***************************************************************************)
LEMMA EntryAgreed ==
    ASSUME NEW l \in Replicas, NEW x \in Rids, NEW e \in Entries,
           e.rid = x
    PROVE  /\ LedHyp(l) => [](PendingE(l, e) => <>Agreed(x))
           /\ LedHyp(l) => [](ReadyE(l, e) => <>Agreed(x))
<1>1. PICK p \in Proposals : p = Proposal(e, l)
  BY DEF Proposal, Proposals
<1>2. p.proposer = l /\ p.entry.rid = x
  BY <1>1 DEF Proposal
<1>3. LedHyp(l) => [](InPending(p) => <>Agreed(x))
  BY <1>2, StageE
<1>4. PendingE(l, e) => InPending(p)
  BY <1>1 DEF PendingE, InPending
<1>5. LedHyp(l) => [](ReadyE(l, e) => <>PendingE(l, e))
  BY StageD
<1>6. LedHyp(l) => [](PendingE(l, e) => <>Agreed(x))
  BY <1>3, <1>4, PTL
<1>7. LedHyp(l) => [](ReadyE(l, e) => <>Agreed(x))
  BY <1>5, <1>6, PTL
<1> QED
  BY <1>6, <1>7

(***************************************************************************
The same for a response or a proposal chosen from the current state.
***************************************************************************)
LEMMA ReadyPoint ==
    ASSUME NEW l \in Replicas, NEW x \in Rids
    PROVE  LedHyp(l) => (HasReady(l, x) => <>Agreed(x))
<1> SUFFICES ASSUME LedHyp(l), HasReady(l, x)
             PROVE  <>Agreed(x)
  OBVIOUS
<1>1. PICK y \in Responses : Entry(x, y) \in ready[l]
  BY DEF HasReady
<1>2. PICK e \in Entries : e = Entry(x, y)
  BY DEF Entry, Entries
<1>3. e.rid = x
  BY <1>2 DEF Entry
<1>4. ReadyE(l, e)
  BY <1>1, <1>2 DEF ReadyE
<1>5. LedHyp(l) => [](ReadyE(l, e) => <>Agreed(x))
  BY <1>3, EntryAgreed
<1> QED
  BY <1>4, <1>5, PTL

LEMMA PendingPoint ==
    ASSUME NEW l \in Replicas, NEW x \in Rids
    PROVE  LedHyp(l) => (HasPending(l, x) => <>Agreed(x))
<1> SUFFICES ASSUME LedHyp(l), HasPending(l, x)
             PROVE  <>Agreed(x)
  OBVIOUS
<1>1. PICK y \in Responses : Proposal(Entry(x, y), l) \in pending
  BY DEF HasPending
<1>2. PICK e \in Entries : e = Entry(x, y)
  BY DEF Entry, Entries
<1>3. e.rid = x
  BY <1>2 DEF Entry
<1>4. PendingE(l, e)
  BY <1>1, <1>2 DEF PendingE
<1>5. LedHyp(l) => [](PendingE(l, e) => <>Agreed(x))
  BY <1>3, EntryAgreed
<1> QED
  BY <1>4, <1>5, PTL

(***************************************************************************
With l the leader for good, a submitted request is eventually agreed.
***************************************************************************)
LEMMA LedAgreement ==
    ASSUME NEW x \in Rids, NEW l \in Replicas
    PROVE  LedHyp(l) => [](Sub(x) => <>Agreed(x))
<1>1. LedHyp(l) => [](Sub(x) => <>Acc(l, x))
  BY StageA
<1>2. LiveState /\ Led(l) /\ Acc(l, x) =>
          \/ InFlight(l, x)
          \/ HasReady(l, x)
          \/ HasPending(l, x)
          \/ Agreed(x)
  BY AcceptedUnderWay
<1>3. LedHyp(l) => [](InFlight(l, x) => <>HasReady(l, x))
  BY StageC, PTL
<1>4. LedHyp(l) => [](HasReady(l, x) => <>Agreed(x))
  BY ReadyPoint, PTL DEF LedHyp, LiveHyp
<1>5. LedHyp(l) => [](HasPending(l, x) => <>Agreed(x))
  BY PendingPoint, PTL DEF LedHyp, LiveHyp
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL DEF LedHyp, LiveHyp

(***************************************************************************
Lemma 3 (Eventual agreement).
***************************************************************************)
THEOREM Lemma3Core ==
    ASSUME NEW x \in Rids, NEW l \in Replicas
    PROVE  LiveHyp /\ StableLeader(l) => (x \in submitted ~> Agreed(x))
<1>1. LedHyp(l) => [](Sub(x) => <>Agreed(x))
  BY LedAgreement
<1>2. Sub(x) /\ [Next]_vars => Sub(x)'
  BY SubStable
<1> QED
  BY <1>1, <1>2, PTL DEF LedHyp, LiveHyp, StableLeader, Led, Sub

THEOREM Lemma3 ==
    ASSUME NEW x \in Rids, NEW l \in Replicas
    PROVE  LiveSpec /\ StableLeader(l) => (x \in submitted ~> Agreed(x))
BY Lemma3Core, LiveSpecHyp, PTL
=============================================================================

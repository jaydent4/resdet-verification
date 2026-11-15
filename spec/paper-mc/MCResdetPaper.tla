--------------------------- MODULE MCResdetPaper ---------------------------
(***************************************************************************
A finite instance of ResdetPaper.tla for TLC.

ResdetPaper.tla has infinitely many reachable states: leaders can change
forever, and each new leader can accept every submitted request again, so
the agreed log grows without bound. This module makes the state space
finite by restricting two actions, not by a state constraint, so that
TLC's liveness checking is sound for it:

  - elections are counted and stop after MaxElections, unless
    UnboundedElections is TRUE;
  - consensus agrees at most MaxAgreed entries.

The passing configurations set MaxAgreed above any log length they can
reach and check, with the invariant LogBoundNotReached, that the second
restriction never takes effect. The cfg files replace Nat by a finite
range that covers MaxAgreed.

UnboundedElections = TRUE with MaxAgreed = 1 is the leader-flapping
configuration: leaders may be replaced forever, and the log stays finite
because nothing more is agreed once the one request id has an entry, at
which point the property under test already holds.

ClearOnElect = FALSE is a mutant: a replica keeps its request-
deduplication state across leadership terms. TLC then finds a behavior in
which a request is never agreed although a leader is in place for good,
which is why Section 4.1 has to scope that state to a term.
***************************************************************************)
EXTENDS ResdetPaper

CONSTANTS MaxElections, UnboundedElections, MaxAgreed, ClearOnElect

(* The cfg files substitute this for Nat. Six indexes are enough for the
   log lengths these configurations reach. *)
MCNat == 0..6

VARIABLE elections

mcvars == <<vars, elections>>

MCInit == Init /\ elections = 0

MCElect(l) ==
    /\ UnboundedElections \/ elections < MaxElections
    /\ elections' = IF UnboundedElections THEN elections ELSE elections + 1
    /\ l \in up
    /\ leader # l
    /\ leader' = l
    /\ accepted' =
        IF ClearOnElect THEN [accepted EXCEPT ![l] = {}] ELSE accepted
    /\ UNCHANGED
        <<up, submitted, calling, ready, pending, agreed, log, processed,
          done, dset, delivered>>

Same == UNCHANGED elections

MCAgree(p) == Len(agreed) < MaxAgreed /\ Agree(p)

LogBoundNotReached == Len(agreed) < MaxAgreed

MCNext ==
    \/ \E l \in Replicas : MCElect(l)
    \/ Same /\ \E x \in Rids : Submit(x)
    \/ Same /\ \E r \in Replicas : Crash(r)
    \/ Same /\ \E x \in Rids : Accept(x)
    \/ Same /\ \E l \in Replicas, x \in Rids, y \in Responses :
                  Respond(l, x, y)
    \/ Same /\ \E l \in Replicas, e \in Entries : Propose(l, e)
    \/ Same /\ \E p \in Proposals : MCAgree(p)
    \/ Same /\ \E p \in Proposals : Drop(p)
    \/ Same /\ \E r \in Replicas, k \in Nat : Learn(r, k)
    \/ Same /\ \E r \in Replicas : Process(r)

MCFairness ==
    /\ \A x \in Rids : WF_mcvars(Same /\ Accept(x))
    /\ \A l \in Replicas, x \in Rids : WF_mcvars(Same /\ RespondSome(l, x))
    /\ \A l \in Replicas, e \in Entries : WF_mcvars(Same /\ Propose(l, e))
    /\ \A p \in Proposals : WF_mcvars(Same /\ MCAgree(p))
    /\ \A r \in Replicas, k \in Nat : WF_mcvars(Same /\ Learn(r, k))
    /\ \A r \in Replicas : WF_mcvars(Same /\ Process(r))

MCSpec == MCInit /\ [][MCNext]_mcvars

MCFairSpec == MCSpec /\ MCFairness

(* The conjuncts of the proofs' inductive invariants, restated here so
   that this module does not depend on the proof modules. *)
LeaderUp == leader # NoLeader => leader \in up

LearnedIsAgreed ==
    \A r \in Replicas :
        \A k \in DOMAIN log[r] :
            k \in 1..Len(agreed) /\ log[r][k] = agreed[k]

DoneIsProcessed == \A r \in Replicas : done[r] = 1..processed[r]

DsetIsProcessed ==
    \A r \in Replicas :
        /\ \A x \in dset[r] :
             \E j \in 1..processed[r] : log[r][j].rid = x
        /\ \A j \in 1..processed[r] : log[r][j].rid \in dset[r]

DeliveredFirst ==
    \A r \in Replicas :
        \A i \in 1..Len(delivered[r]) :
            \E j \in 1..processed[r] :
                /\ delivered[r][i] = agreed[j]
                /\ \A j2 \in 1..(j - 1) : agreed[j2].rid # agreed[j].rid

DsetDelivered ==
    \A r \in Replicas :
        /\ \A x \in dset[r] : Delivers(r, x)
        /\ \A i \in 1..Len(delivered[r]) : delivered[r][i].rid \in dset[r]

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

ProcessSteps == [][ProcessInOrder]_mcvars

(* Lemma 3, Lemma 4, Lemma 5, Theorem 2. *)
Lemma3 ==
    \A x \in Rids, l \in Replicas :
        StableLeader(l) => (x \in submitted ~> Agreed(x))

(* i ranges over 1..6 rather than Nat: for i = 0 both sides of ~> are the
   constant TRUE, and TLC reports such a trivially true formula as an
   error. *)
Lemma4 ==
    \A r \in Replicas, i \in 1..6 :
        NonFaulty(r) => (i \in 1..Len(agreed) ~> LearnedThrough(r, i))

Lemma5 ==
    \A r \in Replicas, x \in Rids, i \in Nat :
        NonFaulty(r) =>
            ((LearnedThrough(r, i) /\ AgreedAt(x, i)) ~> Delivers(r, x))

Theorem2 ==
    \A x \in Rids, l \in Replicas, r \in Replicas :
        (StableLeader(l) /\ NonFaulty(r)) =>
            (x \in submitted ~> Delivers(r, x))

(***************************************************************************
Negative controls.

Theorem2NoLeader drops the leader premise altogether; it fails when the
leader crashes and nobody is elected.

Lemma3Flapping is Lemma 3 with CG3(1) read literally: no replica ever
crashes and from some point on there is always a leader, but no leader
has to stay. It fails in the leader-flapping configuration: two replicas
alternate as leader, and each finishes its nested call only after it has
been replaced, so its proposal is discarded. This is why the theorems
assume StableLeader(l).
***************************************************************************)
Theorem2NoLeader ==
    \A x \in Rids, r \in Replicas :
        NonFaulty(r) => (x \in submitted ~> Delivers(r, x))

Lemma3Flapping ==
    \A x \in Rids :
        ([](up = Replicas) /\ <>[](leader # NoLeader))
            => (x \in submitted ~> Agreed(x))
=============================================================================

---------------------------- MODULE ResdetPaper ----------------------------
EXTENDS Naturals, Sequences

(***************************************************************************
Resdet at the level of the paper's pseudocode and correctness section.

Resdet.tla is the model the TLC configurations were built around: it has
the Cyclades extensions, the mutants, a bounded log, and one shared log
that every replica reads. This module is a second, smaller specification
of the core protocol only, written so that the paper's lemmas and theorems
can be stated as the paper states them:

  - every replica has its own log of learned entries (the paper's `log`),
    so Lemma 1 is a statement about two replicas' logs;
  - the agreed log is unbounded, and request ids are submitted over time
    from an arbitrary, possibly infinite, set;
  - the leader can be replaced at any time, not only when it crashes, and
    a replaced leader's proposals can be lost;
  - request deduplication is scoped to a leadership term, as the repaired
    proof of Lemma 3 requires;
  - a crashed replica does not return (crash-stop), so "non-faulty" means
    "never crashes".

What stays abstract. Consensus is a box: `pending` holds proposals, Agree
appends one to the single agreed log, and Learn copies an agreed entry
into a replica's log, so CG1 and CG2 hold of the box by construction.
Forwarding and message delivery are folded into Accept: a submitted
request reaches the current leader's handler without a modelled message.
The request body is omitted, since all invocations for a request id carry
the same one.

Pseudocode correspondence:

  handle_request, leader, not a duplicate   Accept (issues the nested call)
  send_and_recv returns                     Respond
  propose((rid, resp))                      Propose
  consensus commits an entry                Agree  (Drop: a lost proposal)
  handle_learn(index, entry)                Learn
  process(), one iteration                  Process
  is_request_duplicate                      accepted
  is_delivery_duplicate                     dset

Two variables are histories, kept only so that the lemmas can be stated:
`done` records which indexes each replica has processed, and `delivered`
records the responses it has delivered, in order.
***************************************************************************)

CONSTANTS
    Replicas,
    Rids,
    Responses,
    NoLeader

ASSUME PaperAssumptions ==
    /\ Replicas # {}
    /\ Responses # {}
    /\ NoLeader \notin Replicas

Entries == [rid : Rids, value : Responses]

Proposals == [entry : Entries, proposer : Replicas]

Entry(x, y) == [rid |-> x, value |-> y]

Proposal(e, l) == [entry |-> e, proposer |-> l]

VARIABLES
    up,         \* replicas that have not crashed
    leader,     \* the consensus module's current leader, or NoLeader
    submitted,  \* request ids that service code has submitted
    accepted,   \* per replica: ids accepted in its current term as leader
    calling,    \* per replica: ids whose nested call is in flight
    ready,      \* per replica: responses received and not yet proposed
    pending,    \* proposals handed to consensus and not yet agreed or lost
    agreed,     \* the agreed log
    log,        \* per replica: the learned entries, by index
    processed,  \* per replica: the highest index processed
    done,       \* per replica: the indexes it has processed (history)
    dset,       \* per replica: ids whose response has been delivered
    delivered   \* per replica: the delivered responses, in order (history)

vars ==
    <<up, leader, submitted, accepted, calling, ready, pending, agreed,
      log, processed, done, dset, delivered>>

Init ==
    /\ up = Replicas
    /\ leader \in Replicas \union {NoLeader}
    /\ submitted = {}
    /\ accepted = [r \in Replicas |-> {}]
    /\ calling = [r \in Replicas |-> {}]
    /\ ready = [r \in Replicas |-> {}]
    /\ pending = {}
    /\ agreed = <<>>
    /\ log = [r \in Replicas |-> <<>>]
    /\ processed = [r \in Replicas |-> 0]
    /\ done = [r \in Replicas |-> {}]
    /\ dset = [r \in Replicas |-> {}]
    /\ delivered = [r \in Replicas |-> <<>>]

(* Service code submits a logical request. Retries reuse the id, so a
   request id is submitted once. *)
Submit(x) ==
    /\ x \notin submitted
    /\ submitted' = submitted \union {x}
    /\ UNCHANGED
        <<up, leader, accepted, calling, ready, pending, agreed, log,
          processed, done, dset, delivered>>

(* Consensus makes l the leader. This can happen at any time and can
   replace a live leader. A replica starts a term with empty
   request-deduplication state. *)
Elect(l) ==
    /\ l \in up
    /\ leader # l
    /\ leader' = l
    /\ accepted' = [accepted EXCEPT ![l] = {}]
    /\ UNCHANGED
        <<up, submitted, calling, ready, pending, agreed, log, processed,
          done, dset, delivered>>

(* Crash-stop: r takes no further step. *)
Crash(r) ==
    /\ r \in up
    /\ up' = up \ {r}
    /\ leader' = IF leader = r THEN NoLeader ELSE leader
    /\ UNCHANGED
        <<submitted, accepted, calling, ready, pending, agreed, log,
          processed, done, dset, delivered>>

(* handle_request at the leader for a request it has not accepted in this
   term: record it and issue the nested call. *)
Accept(x) ==
    /\ leader # NoLeader
    /\ x \in submitted
    /\ x \notin accepted[leader]
    /\ accepted' = [accepted EXCEPT ![leader] = @ \union {x}]
    /\ calling' = [calling EXCEPT ![leader] = @ \union {x}]
    /\ UNCHANGED
        <<up, leader, submitted, ready, pending, agreed, log, processed,
          done, dset, delivered>>

(* The nested call returns some response. *)
Respond(l, x, y) ==
    /\ l \in up
    /\ x \in calling[l]
    /\ calling' = [calling EXCEPT ![l] = @ \ {x}]
    /\ ready' = [ready EXCEPT ![l] = @ \union {Entry(x, y)}]
    /\ UNCHANGED
        <<up, leader, submitted, accepted, pending, agreed, log,
          processed, done, dset, delivered>>

RespondSome(l, x) == \E y \in Responses : Respond(l, x, y)

(* The handler proposes the entry. Consensus takes proposals only from
   the current leader; a proposal by anyone else is discarded. *)
Propose(l, e) ==
    /\ l \in up
    /\ e \in ready[l]
    /\ ready' = [ready EXCEPT ![l] = @ \ {e}]
    /\ pending' =
        IF leader = l THEN pending \union {Proposal(e, l)} ELSE pending
    /\ UNCHANGED
        <<up, leader, submitted, accepted, calling, agreed, log,
          processed, done, dset, delivered>>

(* Consensus agrees a pending proposal at the next index. *)
Agree(p) ==
    /\ p \in pending
    /\ agreed' = Append(agreed, p.entry)
    /\ pending' = pending \ {p}
    /\ UNCHANGED
        <<up, leader, submitted, accepted, calling, ready, log, processed,
          done, dset, delivered>>

(* A proposal whose proposer is no longer the leader may be lost. *)
Drop(p) ==
    /\ p \in pending
    /\ p.proposer # leader
    /\ pending' = pending \ {p}
    /\ UNCHANGED
        <<up, leader, submitted, accepted, calling, ready, agreed, log,
          processed, done, dset, delivered>>

(* handle_learn(k, agreed[k]) at r, for an index r has not recorded. *)
Learn(r, k) ==
    /\ r \in up
    /\ k \in 1..Len(agreed)
    /\ k \notin DOMAIN log[r]
    /\ log' = [log EXCEPT ![r] =
                  [i \in DOMAIN @ \union {k} |->
                      IF i = k THEN agreed[k] ELSE @[i]]]
    /\ UNCHANGED
        <<up, leader, submitted, accepted, calling, ready, pending, agreed,
          processed, done, dset, delivered>>

(* One iteration of process(): advance to the next index if it has been
   learned, and deliver its response unless the id was delivered before. *)
Process(r) ==
    LET next == processed[r] + 1
        entry == log[r][next]
    IN
    /\ r \in up
    /\ next \in DOMAIN log[r]
    /\ processed' = [processed EXCEPT ![r] = next]
    /\ done' = [done EXCEPT ![r] = @ \union {next}]
    /\ IF entry.rid \in dset[r]
       THEN UNCHANGED <<dset, delivered>>
       ELSE /\ dset' = [dset EXCEPT ![r] = @ \union {entry.rid}]
            /\ delivered' = [delivered EXCEPT ![r] = Append(@, entry)]
    /\ UNCHANGED
        <<up, leader, submitted, accepted, calling, ready, pending, agreed,
          log>>

Next ==
    \/ \E x \in Rids : Submit(x)
    \/ \E l \in Replicas : Elect(l)
    \/ \E r \in Replicas : Crash(r)
    \/ \E x \in Rids : Accept(x)
    \/ \E l \in Replicas, x \in Rids, y \in Responses : Respond(l, x, y)
    \/ \E l \in Replicas, e \in Entries : Propose(l, e)
    \/ \E p \in Proposals : Agree(p)
    \/ \E p \in Proposals : Drop(p)
    \/ \E r \in Replicas, k \in Nat : Learn(r, k)
    \/ \E r \in Replicas : Process(r)

Spec == Init /\ [][Next]_vars

(***************************************************************************
The paper's liveness assumptions, as weak fairness of each instance of an
action. Fairness is per request id, per entry, and per index, so no
request can starve behind others.

  AcceptFair    L1, L2, L4: a pending request reaches the leader's handler
  RespondFair   L3: a nested call returns
  ProposeFair   L4: the handler completes and proposes
  AgreeFair     CG3(2): a proposal that is not lost is agreed
  LearnFair     CG3(3), L4: every agreed index is learned
  ProcessFair   L4: process() runs

CG3(1), that a non-faulty leader is eventually elected, is not fairness of
an action here. The liveness theorems take it as a premise, in the form
"some replica is eventually the leader for good" (see StableLeader).
***************************************************************************)
AcceptFair == \A x \in Rids : WF_vars(Accept(x))

RespondFair ==
    \A l \in Replicas, x \in Rids : WF_vars(RespondSome(l, x))

ProposeFair == \A l \in Replicas, e \in Entries : WF_vars(Propose(l, e))

AgreeFair == \A p \in Proposals : WF_vars(Agree(p))

LearnFair == \A r \in Replicas, k \in Nat : WF_vars(Learn(r, k))

ProcessFair == \A r \in Replicas : WF_vars(Process(r))

Fairness ==
    /\ AcceptFair
    /\ RespondFair
    /\ ProposeFair
    /\ AgreeFair
    /\ LearnFair
    /\ ProcessFair

FairSpec == Spec /\ Fairness

(***************************************************************************
The specification the TLAPS liveness theorems are about. []Fairness says
the same as Fairness: every conjunct is a weak-fairness formula, which
holds of a behavior exactly if it holds of all its suffixes, quantified
over constant sets. TLAPS cannot move [] across those quantifiers, so the
theorems state the premise in the form their proofs use. TLC accepts only
the unboxed form, so the configurations use FairSpec.
***************************************************************************)
LiveSpec == Spec /\ []Fairness

(***************************************************************************
Terms of the paper's correctness section.
***************************************************************************)

(* Some entry for request id x is agreed at index i. *)
AgreedAt(x, i) == i \in 1..Len(agreed) /\ agreed[i].rid = x

Agreed(x) == \E i \in 1..Len(agreed) : agreed[i].rid = x

(* Replica r has learned every index through i. *)
LearnedThrough(r, i) == \A k \in 1..i : k \in DOMAIN log[r]

(* Replica r has delivered a response for request id x. *)
Delivers(r, x) ==
    \E j \in 1..Len(delivered[r]) : delivered[r][j].rid = x

(* CG3(1), as the liveness proofs need it: l is eventually the leader for
   good. A leader is up, and a crashed replica does not return, so such an
   l never crashes. *)
StableLeader(l) == <>[](leader = l)

(* r never crashes. *)
NonFaulty(r) == [](r \in up)

(***************************************************************************
An invariant the proofs use: every index up to the processed counter has
been learned.
***************************************************************************)
ProcessedLearned ==
    \A r \in Replicas : \A j \in 1..processed[r] : j \in DOMAIN log[r]

(***************************************************************************
Lemma 1: two replicas that have both processed index i processed the same
entry there.
***************************************************************************)
SameProcessedEntry ==
    \A r, t \in Replicas :
        \A i \in done[r] : i \in done[t] => log[r][i] = log[t][i]

(***************************************************************************
Lemma 2: a replica that has processed index i has processed every index
through i. ProcessInOrder is the step form: the processed index only ever
advances by one.
***************************************************************************)
NoHoleProcessing ==
    \A r \in Replicas : \A i \in done[r] : \A j \in 1..i : j \in done[r]

ProcessInOrder ==
    \A r \in Replicas :
        processed'[r] = processed[r] \/ processed'[r] = processed[r] + 1

(***************************************************************************
Theorem 1: if replicas r and t deliver responses for the same request id,
the responses are equal. delivered[r] is everything r has delivered.
***************************************************************************)
Agreement ==
    \A r, t \in Replicas :
        \A i \in 1..Len(delivered[r]) :
            \A j \in 1..Len(delivered[t]) :
                delivered[r][i].rid = delivered[t][j].rid =>
                    delivered[r][i].value = delivered[t][j].value

(* A replica delivers a request id at most once. *)
DeliveredOnce ==
    \A r \in Replicas :
        \A i, j \in 1..Len(delivered[r]) :
            delivered[r][i].rid = delivered[r][j].rid => i = j

=============================================================================

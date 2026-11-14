# The TLA+ specification and the paper

Source reviewed: the LaTeX source of *Cyclades: Taming Nested-Response
Nondeterminism in Replicated Microservices* as supplied on 2026-11-10
(Section 4, the pseudocode figure, Section 5, and Section 6 for the
extensions). The paper source is not part of this repository and was not
edited.

The TLC checks and the TLAPS proofs ([TLAPS.md](TLAPS.md)) are statements
about `Resdet.tla`. This document is the other half: how `Resdet.tla` relates
to the protocol the paper describes. It records a first action-by-action
review, made by reading both; it is a review, not a proof, and it does not
replace the authors' own.

**Summary.** The delivery path (`handle_learn`, `process`, delivery
deduplication) is modelled faithfully, and that is the part Theorem 1 is
about. Request ingress, leadership, crashes, and consensus are abstracted.
None of those abstractions makes Theorem 1 easier to prove than it is for the
paper's protocol under crash-stop. All of them make Theorem 2 easier.

## Pseudocode to specification

| Paper | `Resdet.tla` | Correspondence |
| --- | --- | --- |
| `log`, the per-replica map from index to learned entry | The shared `consensusLog`, plus `learned[r]`, the set of indexes replica `r` has learned | Abstracted. Replicas have no log of their own, so CG1 and CG2 hold by construction |
| `learned`, the highest index learned | None | Not modelled. It is redundant in the pseudocode: `process` also tests that the next index is in `log` |
| `processed` | `processed[r]` | Faithful |
| The `delivered` set and `is_delivery_duplicate` | `seen[r]` | Faithful. The names differ: the specification's `delivered[r]` is a history of everything `r` delivered, kept for stating properties |
| Step 1, a client submits a root request | None | Out of scope |
| Step 2, service replicas call `handle_request` | `SubmitVote` | Abstracted: each replica records one invocation per request id, with its payload, in the global `votes` |
| Step 3, non-leaders forward | The leader reads `votes` in `SelectByQuorum` | Abstracted: there are no messages, so nothing is delayed or lost |
| `is_leader()` | The single variable `leader` | Abstracted: no replica can hold a stale view of who leads, and two leaders never coexist |
| `is_request_duplicate` | The guards `selected[request] = NoValue` (`SelectByQuorum`) and `replica \notin dispatchers[request]` (`Dispatch`) | Differs. This state is partly global and survives a crash; see below |
| Step 4, `send_and_recv` | `Dispatch`, then `ExternalRespond` with any value in `Responses` | Abstracted: the call is split in two, and the response is arbitrary |
| Step 5, `propose` | `ProposeResponse` | Abstracted: the proposer must still be the leader, and a proposal is never lost |
| Consensus commits an entry | `DecideOne`, `DecidePair` | Abstracted; see below |
| Step 6, `handle_learn` | `LearnSlot`; its guard `slot \notin learned[replica]` is `if index in log: return` | Faithful |
| Step 7, `process` | `ProcessContiguous` with `ApplyItem` | Faithful. One index per step instead of a loop, and `handle_learn` does not call it atomically |
| Leader change | `Crash` (clears `leader` if the leader crashed), `Elect`, and the `EnableCrashes` disjunct of `Dispatch`'s guard | Differs: the leader changes only when it crashes; the retry by waiting service code is implicit |

## Specification to paper

- **Core protocol:** `leader`, `up`, `dispatchers`, `execResponse`,
  `proposed`, `consensusLog`, `learned`, `processed`, `seen`; `Dispatch`,
  `ExternalRespond`, `ProposeResponse`, `DecideOne`, `LearnSlot`,
  `ProcessContiguous`, `Crash`, `Elect`; and `SubmitVote`, `SelectByQuorum`,
  `votes`, `selected` with `Quorum = 1`.
- **Section 6.1 (caller quorum, force-yield):** `Quorum >= 2`, several
  `Payloads`, `TimeoutSelect`, `selectedByFallback`, `EnableTimeoutFallback`.
- **Section 6.2 (batching):** `EnableBatching`, `DecidePair`. Batches hold at
  most two entries.
- **No counterpart in the paper:** `NoLeaderDispatch`,
  `DirectNoLeaderRespond`, `EnableNoLeaderFallback` (the Go implementation's
  no-known-leader path); `Recover` with full state.
- **Model-checking devices:** `MaxSlots`, `PrioritizeUniqueDecisions`,
  `Symmetry`, `EnableCrashes`; the history variables `observed`, `delivered`,
  `unauthorizedDispatch`, `earlyDelivery`.
- **Mutants:** the five `Mutant*` switches, `ProcessNonContiguous`,
  `DeliverBeforeConsensus`.

## Differences that matter when citing the proofs

In each case: easier or harder means easier or harder to satisfy in the
specification than in the paper's protocol.

1. **A crash is a pause.** The paper's fault model says replicas may crash,
   recover, or be temporarily unavailable, and does not say which state
   survives. In the specification `Crash` and `Recover` change only `up` and
   `leader`: `votes`, `selected`, `dispatchers`, `execResponse`, `learned`,
   `processed`, `seen`, and `delivered` all survive, and `ExternalRespond` has
   no `up` guard, so a call in flight when its caller crashes still returns.
   A replica that led, dispatched, crashed, and is elected again does not
   call again; it proposes the response it kept.
   *Theorem 1:* the same as the paper under crash-stop. A recovery that lost
   `seen` but kept `processed` would break it and is not modelled.
   *Theorem 2:* easier.
2. **Consensus is one fair action.** `DecideOne` and `DecidePair` append only
   proposed entries, so nothing unproposed is ever agreed
   (`ConsensusValidity`). But they have no guard on the leader, on which
   replicas are up, or on a quorum; `proposed` never shrinks, so a crashed
   leader's proposal can still be agreed; the same entry can be agreed
   repeatedly; and consensus, not the leader, forms batches.
   *Theorem 1:* harder, since the specification allows more logs.
   *Theorem 2:* easier. Consensus makes progress with any number of replicas
   down. It is also restricted by `PrioritizeUniqueDecisions` and the
   `MaxSlots` bound, which the paper has no counterpart for.
3. **Leadership.** The paper's leader changes when it becomes unresponsive,
   and each replica asks `is_leader()` locally. The specification has one
   global `leader`, changed only by `Crash` then `Elect`.
   *Theorem 1:* neither. *Theorem 2:* easier: a live leader is never deposed.
4. **Ingress and retries.** The paper has forwarding, and service code
   retrying `handle_request` after a leader change. In the specification
   `votes` and `selected` are global and permanent, so a new leader inherits
   the selection and dispatches without any retry reaching it.
   *Theorem 1:* neither. *Theorem 2:* easier (L1 and L2 are built in).
5. **What liveness says.** `Completion` is about every request id in a
   closed finite set, at every replica. The TLAPS theorem assumes
   `<>[]StableOn(U)`; `Elect` and `Recover` have no fairness, so CG3(1) is a
   hypothesis of the theorem, not something `FairSpec` provides. Fairness is
   per action, which is enough only because the model does finitely much
   work.
6. **Granularity.** The handlers are split into select, dispatch, respond,
   propose and into learn, process.
   *Theorem 1:* harder (more interleavings). *Theorem 2:* neither.
7. **Shared log.** CG1 and CG2 hold for every replica, recovered ones
   included, and Lemma 1 needs no argument.

## Points in the paper source this review ran into

These are observations for the authors, about the 2026-11-10 source.

- **The mechanization subsection describes a different artifact.** It cites
  a 136-line specification, `MC.tla`, `MC_Safe3.cfg`, `MC_Live2.cfg`, mutants
  M1-M3, and 1.19M and 465K states. None of that is in this repository, whose
  specification is about 530 lines without comments, with six mutants and
  the configurations listed in the README. Its third mutant result
  (request-deduplication state that survives a crash violates Theorem 2) does
  not carry over: here that state always survives, and liveness holds
  because the recorded response survives with it. Suggested replacement text
  for this repository's artifact is below.
- **Fault model.** Section 4 allows recovery but never defines "non-faulty",
  and the proofs of Section 5 assume `log`, `processed`, and the delivered
  set are never lost. The mechanization subsection relies on request
  deduplication being in memory, which its own TODO notes is not stated in
  Section 4. `lean/PAPER.md` records a crash-stop scope confirmed on
  2026-09-23; under crash-stop a "recovered leader" cannot occur.
- **Lemma 3.** The proof takes a leader that accepted a request id to go on
  to propose and have the entry agreed. A leader that is deposed without
  crashing and later re-elected keeps its deduplication entry, while CG3(2)
  says nothing about the proposal it made before being deposed.
- **Smaller points.** The pseudocode figure omits the delivered set that
  Section 4's text says each replica keeps. The terminology paragraph says
  delivery is suppressed by "request-id deduplication", which reads as
  `is_request_duplicate` rather than `is_delivery_duplicate`.

## Suggested text for the mechanization subsection

If the paper cites this repository's artifact, the subsection could read as
follows. It uses the paper's own macros. Every number is reproduced by
`make check` and `make check-tlaps`.

```latex
\subsection{Mechanization}
\label{subsec:mechanization}
We also specified \prot{} in TLA\textsuperscript{+}~\cite{lamport2002specifying}
above an abstract consensus service: consensus is a single append-only
\protoagree{agreed} log, so CG1 and CG2 hold by construction, and the
protocol's nondeterminism (crashes, recoveries, and leader changes, a new
leader repeating a nested call, nested calls returning arbitrary responses,
out-of-order \protolearn{learning}, and response batching) is modeled as
explicit actions. The specification is about 530 lines without comments,
including the checked properties.

TLC~\cite{yu1999tlc} exhaustively checks up to twenty invariants, among them
Theorem~1, first-commit-wins, and at-most-once \protodeliver{delivery}, on
six configurations with three replicas (up to 717K distinct states after
symmetry reduction). Two of them have crashes and re-election, and one of
those reaches logs in which successive leaders had different responses
\protoagree{agreed} for the same request id. TLC also checks Theorem~2 under
weak fairness for three replicas and two request ids without crashes (50K
distinct states). To check that the specification is not vacuous, we
confirmed that TLC rejects six mutants, including \protodeliver{delivering}
every \protoagree{agreed} entry rather than the first one for a request id,
\protoprocess{processing} out of log order, and \protodeliver{delivering}
before agreement.

Beyond these bounded checks, we proved both theorems with the
TLA\textsuperscript{+} Proof System~\cite{cousineau2012tlaproofs} for
unbounded parameters. Theorem~1 is proved as an inductive invariant, that
every \protodeliver{delivered} response is the first \protoagree{agreed}
entry for its request id, for any number of replicas, request ids, and
responses, with crashes and batching enabled; the same development proves
each of the twenty invariants that TLC checks. Theorem~2 is proved in
crash-stop form under weak fairness of the actions that L1, L3, L4, and
CG3(2)--(3) assume to be live: once a leader remains in place and a set of
replicas remains up, each replica in that set eventually
\protodeliver{delivers} a response for every request id, while leaders may
change finitely often beforehand and the other replicas may fail forever.
The liveness proof is for the model's bounded log, in which consensus gives
every not-yet-\protoagree{agreed} request a slot before any retry, and for a
fixed finite set of request ids; a crashed replica that returns keeps its
state. The proofs comprise 4{,}242 obligations in thirteen modules, all
discharged by the system's back-end provers. The specification, model
configurations, and proofs are part of our artifact.
```

It needs one new reference, to be checked against the publisher's page:
Cousineau, Doligez, Lamport, Merz, Ricketts, and Vanzetto, "TLA+ Proofs",
FM 2012, LNCS 7436, pages 147-154.

Status of the plan in the comment block at the top of the paper's
correctness section, for this repository: (1)-(4) and (6) are done; the
TLAPS item is done for Theorem 1 and, in crash-stop form, for Theorem 2;
(5), the authors' review of the specification against Section 4, is what
this document is a first pass at.

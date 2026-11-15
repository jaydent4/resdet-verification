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

**`ResdetPaper.tla` was written in response to this review.** It is a second
specification, of the core protocol only, in which the differences below
that made the theorems easier are removed: replicas have their own logs
(difference 7), the log is unbounded and consensus has no scheduling
restriction (2), the leader can be replaced without crashing and a replaced
leader's proposal can be lost (3), requests are submitted over time and are
accepted again by each new leader (4), liveness is stated per request id and
per non-faulty replica (5), and failures are crash-stop (1). The paper's
Lemmas 1-5 and Theorems 1 and 2 are proved about it; Lemma 3 and Theorem 2
need CG3(1) to give a leader that stays, which the paper does not say (see
below and [TLAPS.md](TLAPS.md)). The review below is of `Resdet.tla`.

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
- **Lemma 3, request deduplication.** The proof takes a leader that
  accepted a request id to go on to propose and have the entry agreed. A
  leader that is deposed without crashing and later re-elected keeps its
  deduplication entry, while CG3(2) says nothing about the proposal it made
  before being deposed. `paper-mc/witness/PaperPersistentDedup.cfg` is this
  counterexample; the repair is to scope that state to a leadership term.
- **Lemma 3 and Theorem 2, CG3(1).** "Consensus eventually elects a
  non-faulty leader" is not enough. In
  `paper-mc/witness/PaperLeaderFlapping.cfg` nobody crashes and there is
  always a leader, but two replicas alternate as leader forever; each
  finishes its nested call after it has been replaced, so it proposes as a
  non-leader, CG3(2) does not apply, and the request is never agreed. The
  source shows "that remains leader" was removed from CG3(1) because it is
  not guaranteed. Some such assumption is needed all the same: either that
  wording, or a protocol change so that a replaced leader's response still
  reaches consensus through the new leader.
- **Smaller points.** The pseudocode figure omits the delivered set that
  Section 4's text says each replica keeps. The terminology paragraph says
  delivery is suppressed by "request-id deduplication", which reads as
  `is_request_duplicate` rather than `is_delivery_duplicate`.

## Suggested text for the mechanization subsection

If the paper cites this repository's artifact, the subsection could read as
follows. It uses the paper's own macros. Every number is reproduced by `make check`
and `make check-tlaps`. The second paragraph depends on two changes to the
paper that the proofs call for: CG3(1) has to say the leader remains
leader, and Section 4 has to say request deduplication is cleared when a
replica becomes leader.

```latex
\subsection{Mechanization}
\label{subsec:mechanization}
We also mechanized this section in TLA\textsuperscript{+}~\cite{lamport2002specifying}. A first specification (about 190 lines without comments) models \prot{} at the level of Figure~\ref{fig:eo-pseudocode}: each replica has its own log, the \protoagree{agreed} log is unbounded, request ids are submitted over time, the leader can be replaced at any time, and replicas fail by crashing. Consensus is a box that appends proposed entries to one \protoagree{agreed} log and hands them to replicas, so CG1 and CG2 hold by construction. With the TLA\textsuperscript{+} Proof System~\cite{cousineau2012tlaproofs} we proved Lemmas~1--5 and Theorems~1 and~2 about this specification for any number of replicas, request ids, and responses, taking L1--L4 and CG3(2)--(3) as weak fairness of the corresponding actions.

The proofs made two assumptions explicit, and for each TLC~\cite{yu1999tlc} finds a counterexample to Theorem~2 when it is dropped. First, the leader that CG3(1) provides must remain leader: if two replicas alternate as leader forever, each can complete its nested call only after it has been replaced, so nothing is ever \protoagree{agreed}. Second, request-deduplication state must not outlive a term as leader: a replica that accepts a request, is replaced before proposing, and is elected again would otherwise never propose it.

A second specification (about 530 lines) adds the extensions of Section~\ref{sec:cyclades} (caller quorum, force-yield, and batching) and deliberate mutants, over a bounded log. TLC exhaustively checks up to twenty invariants on six configurations of it with three replicas (up to 717K distinct states after symmetry reduction), including one that reaches logs in which successive leaders had different responses \protoagree{agreed} for the same request id, and rejects six mutants. For this specification too we proved Theorem~1 and each of the twenty invariants for unbounded parameters. In total the proofs comprise 6{,}424 obligations in nineteen modules, all discharged by the proof system's back-end provers. The specifications, model configurations, and proofs are part of our artifact.
```

It needs one new reference, to be checked against the publisher's page:
Cousineau, Doligez, Lamport, Merz, Ricketts, and Vanzetto, "TLA+ Proofs",
FM 2012, LNCS 7436, pages 147-154.

Status of the plan in the comment block at the top of the paper's
correctness section, for this repository: (1)-(4) and (6) are done; the
TLAPS item is done for Lemmas 1-5 and Theorems 1 and 2 on the paper-level
specification; (5), the authors' review of the specifications against
Section 4, is what this document is a first pass at.

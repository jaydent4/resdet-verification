# TLAPS proofs of the paper's lemmas and theorems

The TLC configurations check the specifications exhaustively, but only for
the finite constants in each `.cfg`. The modules described here prove the
paper's results with the TLA+ Proof System (TLAPS), for unbounded
parameters. There are two specifications, and the proofs say different
things about each.

**`ResdetPaper.tla`, the paper-level specification.** The core protocol at
the level of the paper's pseudocode: per-replica logs, an unbounded agreed
log, request ids submitted over time from an arbitrary set, leaders
replaced at any time, crash-stop failures. About it TLAPS proves **every
lemma and theorem of the paper's correctness section**: Lemmas 1-5,
Theorem 1, and Theorem 2. Lemmas 1, 2, 4, 5 and Theorem 1 are proved as the
paper states them. Lemma 3 and Theorem 2 are proved with one assumption
stronger than the paper writes it: the leader that CG3(1) provides has to
stay. With CG3(1) as written they are false, and TLC has the
counterexample. See
[The paper-level specification](#the-paper-level-specification).

**`Resdet.tla`, the model the TLC configurations were built around.** It
adds the Cyclades extensions (caller quorum, timeout fallback, batching)
and the mutants, and has a bounded log shared by all replicas. About it
TLAPS proves:

- **Theorem 1 (safety)** and its companion safety properties, for **any**
  replica set, request, payload and response sets, quorum, and `MaxSlots`.
- **Every invariant the passing TLC configurations check**, in one theorem
  (`EveryCheckedInvariant`), under the same generality.
- **Theorem 2 (liveness)** in crash-stop form for that bounded model: once a
  leader is stable and a set of replicas stays up, each of them eventually
  delivers a response for every request id. Read
  [Liveness](#theorem-2-liveness) before citing it.
- **Deterministic continuation and batch regrouping** (Sections 3.3, 6.2,
  6.3 of the paper).

```sh
make fetch-tlaps    # one-time project-local TLAPS installation
make check-tlaps    # re-prove everything from scratch, plus an audit
```

`make check-tlaps` is local. It does not launch, stop, or modify a TLC run.
[PAPER.md](PAPER.md) relates the specification itself to the paper.

## The paper-level specification

`ResdetPaper.tla` exists so the paper's statements can be proved in the
paper's terms. `Resdet.tla` could not serve: it shares one log between
replicas, bounds the log, closes the request set, and changes leader only
on a crash.

| Paper | TLAPS theorem | Statement, for `ResdetPaper.tla` |
| --- | --- | --- |
| Lemma 1 | `Lemma1` in `ResdetPaperSafety.tla` | `Spec => []SameProcessedEntry`: two replicas that have both processed index `i` hold the same entry there |
| Lemma 2 | `Lemma2` | `Spec => []NoHoleProcessing /\ [][ProcessInOrder]_vars`: a replica that has processed index `i` has processed every index through `i`, and `processed` only advances by one |
| Theorem 1 | `Theorem1` | `Spec => []Agreement` |
| Lemma 3 | `Lemma3` in `ResdetPaperLemma3.tla` | `LiveSpec /\ StableLeader(l) => (x \in submitted ~> Agreed(x))` |
| Lemma 4 | `Lemma4` in `ResdetPaperLemma45.tla` | `LiveSpec /\ NonFaulty(r) => (i \in 1..Len(agreed) ~> LearnedThrough(r, i))` |
| Lemma 5 | `Lemma5` | `LiveSpec /\ NonFaulty(r) => ((LearnedThrough(r, i) /\ AgreedAt(x, i)) ~> Delivers(r, x))` |
| Theorem 2 | `Theorem2`, `Theorem2Paper` in `ResdetPaperTheorems.tla` | `LiveSpec /\ StableLeader(l) /\ NonFaulty(r) => (x \in submitted ~> Delivers(r, x))` |

Here `x` is any request id, `r` and `l` any replicas, `i` any index, and
`~>` is leads-to: whenever the left side holds, the right side holds then or
later. The request set, the response set and the replica set are arbitrary
and may be infinite, and the log has no bound. (For the liveness theorems
to say anything the replica set must be countable: a behavior has countably
many steps, so fairness of `Learn` for uncountably many replicas cannot
hold.)

"Processed" in Lemmas 1 and 2 is the history variable `done`, the set of
indexes each replica has processed, so Lemma 2 is a statement that could
fail, proved by the invariant `done[r] = 1..processed[r]`. Lemma 1 holds
because `Learn` copies the agreed entry, which is CG1 as the paper assumes
it.

### How the paper's assumptions appear

| Paper | In `ResdetPaper.tla` |
| --- | --- |
| CG1, CG2 | Properties of the consensus box: one agreed log, and `Learn` copies the agreed entry into the replica's own log. `LearnedIsAgreed` is the resulting invariant |
| CG3(1) | The premise `StableLeader(l)`: `l` is eventually the leader for good. See below |
| CG3(2) | Weak fairness of `Agree(p)` for every proposal `p`; a proposal can be lost (`Drop`) only once its proposer is no longer the leader |
| CG3(3), L4 | Weak fairness of `Learn(r, k)` for every replica and index, and of `Process(r)` |
| L1, L2, L4 | Weak fairness of `Accept(x)` for every request id: a submitted request reaches the current leader's handler. Forwarding has no separate message |
| L3 | Weak fairness of the nested call returning, per replica and request id |
| Non-faulty replica | `NonFaulty(r)`: `r` never crashes. Failures are crash-stop |
| Request deduplication | `accepted`, cleared when a replica becomes leader |

Three points where the formal statement had to choose a reading.

- **CG3(1) has to mean a leader that stays, which is more than the paper
  writes.** The paper's CG3(1) is "consensus eventually elects a non-faulty
  leader"; its source shows "that remains leader" was removed on purpose.
  That weaker assumption does not give Lemma 3 or Theorem 2. In
  `paper-mc/witness/PaperLeaderFlapping.cfg` no replica ever crashes and
  there is always a leader, yet two replicas alternate as leader forever,
  each finishing its nested call only after it has been replaced, so its
  proposal is discarded and the request is never agreed. TLC finds that
  behavior, and every fairness condition holds on it. So the theorems
  assume `StableLeader(l)`, which is `<>[](leader = l)`, and the paper's
  CG3(1) needs the same strengthening (or the protocol needs a replaced
  leader's response to reach the new leader). A second control,
  `PaperNoStableLeader.cfg`, is the simpler case where the leader crashes
  and nobody is elected.
- **Request deduplication has to be scoped to a leadership term.** With
  that state kept across terms, a replica that accepts a request, is
  replaced before proposing, and becomes leader again never proposes it.
  `paper-mc/witness/PaperPersistentDedup.cfg` is that counterexample. This is
  the repair to the proof of Lemma 3 recorded in [PAPER.md](PAPER.md).
- **Fairness is stated under a box.** `LiveSpec` is `Spec /\ []Fairness`.
  `[]Fairness` says the same as `Fairness`, because each conjunct is weak
  fairness quantified over a constant set, but TLAPS cannot move `[]` across
  those quantifiers, so the theorems use the form their proofs need. TLC
  accepts only the unboxed form and checks `FairSpec`. That equivalence is a
  standard fact of TLA and is not machine-checked here.
- **A replaced leader's proposal is discarded.** `Propose` by a replica
  that is no longer the leader has no effect. The paper does not say what
  happens in that case; this is the conservative reading, and it is what
  makes the flapping counterexample possible.

### How the liveness proofs work

Unlike the proof for `Resdet.tla`, nothing here rests on the model doing
finitely much work. Each lemma is a chain of weak-fairness steps, as in the
paper:

- **Lemma 3.** The request reaches the leader's handler and is accepted, or
  it is a duplicate; then by the invariant `AcceptedProgress` it was accepted
  earlier in the same term and is in flight, answered, proposed, or agreed.
  The nested call returns, the handler proposes, and the proposal of a
  leader that stays cannot be lost, so it is agreed.
- **Lemma 4.** Induction on the index: each agreed index is eventually
  learned and stays learned.
- **Lemma 5.** Induction on the processed index: with every index through
  `i` learned, `processed` reaches `i`; then the entry at `i` was delivered,
  or its request id was already in the delivery-deduplication state, in
  which case a response for it was delivered earlier.
- **Theorem 2.** Lemma 3, then Lemmas 4 and 5 at whatever index the entry
  was agreed at. That index is chosen by the behavior; the proof picks it at
  the point where the entry is agreed.

| Module | Content |
| --- | --- |
| `ResdetPaper.tla` | The specification |
| `ResdetPaperSafety.tla` | `PaperInv`; Lemma 1, Lemma 2, Theorem 1 |
| `ResdetPaperLive.tla` | `AcceptedProgress`; fairness instances; enabledness of each fair action |
| `ResdetPaperLemma3.tla` | Lemma 3 |
| `ResdetPaperLemma45.tla` | Lemmas 4 and 5 |
| `ResdetPaperTheorems.tla` | Theorem 2 |
| `paper-mc/` | A finite instance for TLC, with two negative controls |

### What the paper-level specification still abstracts

- **Consensus is a box.** There is no Raft: agreement is the `Agree`
  action, and its fairness is CG3(2) taken as given, whatever the number of
  replicas that are up.
- **No messages.** Forwarding and delivery of invocations are one fair
  action; L2 has no separate counterpart.
- **Crash-stop.** A crashed replica does not return, so nothing is said
  about recovery or lost state.
- **One leader at a time.** The specification has a single `leader`
  variable; a replica that wrongly believes it is the leader is modelled
  only as a proposer whose proposal is discarded.
- **Core protocol only.** No caller quorum, timeout fallback, or batching;
  those are in `Resdet.tla`.

## `Resdet.tla` — Theorem 1 (safety): what is proved

For `Spec` of `Resdet.tla`, assuming `StrictDelivery`. `Theorem1`,
`DeliveredAppendOnly`, and the delivery and replay invariants use nothing
else about the constants. The validity conjuncts of `Safety` also use the
specification's own `ConstantAssumptions` (`NoValue` is not a payload or a
response).

| Paper claim | TLAPS theorem | Statement |
| --- | --- | --- |
| Theorem 1 (Safety) | `Theorem1` in `ResdetTheorems.tla` | `Spec => []Agreement`: if replicas `r` and `t` deliver `y_r` and `y_t` for the same request id, then `y_r = y_t` |
| Theorem 1, TLC form | `Safety`, conjunct `ResponseAgreement` | The invariant every passing `.cfg` checks |
| Sections 4.2-4.3: first committed response wins | `Safety`, conjunct `DeliveredFirstCommit` | Every delivered response is the first agreed entry for its request id |
| Sections 4.2-4.3: deliver only once | `Safety`, conjuncts `AtMostOnceDelivery`, `SeenMatchesDelivered` | No replica delivers a request id twice |
| Theorem 1 across time | `DeliveredAppendOnly` in `ResdetTheorems.tla` | `Spec => [][DeliveredGrows]_vars`: a step never removes or rewrites a delivered response |
| Lemmas 1 and 2: same processed prefix, same entries | `ReplayInvariant` in `ResdetPrefix.tla` | A replica's delivery state is the replay of the agreed log up to its processed index |
| Lemma 2: no-hole processing | `Safety`, conjuncts `ProcessedPrefixLearned`, `LearnedOnlyDecided`, `ProcessedWithinLog` | An index is processed only after it and every earlier index is learned |
| Section 3.3: common winner of a response race | `Safety`, conjuncts `PrefixAgreement`, `RaceWinnerAgreement` | Delivery histories are prefix-comparable, so their first entries agree |
| Section 4.2: responses do not bypass commitment | `Safety`, conjuncts `ResponseValidity`, `ConsensusValidity`, `ProposalValidity`, `ObservedHasPhysicalExecution`, `NoDispatchBeforeSelection` | Delivered responses were returned to a replica that dispatched a selected request, then proposed, then agreed |

`Agreement` quantifies over all replicas and over whole delivery histories.
Because histories only grow (`DeliveredAppendOnly`), it covers deliveries
made at different times, and with `r = t` it covers two deliveries by the
same replica. It also covers replicas that are down, but see the crash
model below: that adds less than it sounds.

## Theorem 1: assumptions

- **`StrictDelivery`** (`ResdetFold.tla`): `MutantNoDedup`,
  `MutantNonContiguous`, `MutantEarlyDelivery`, and `EnableNoLeaderFallback`
  are `FALSE`. Each one is a deliberate mutant or the no-known-leader escape
  hatch, outside the paper's protocol, and each is needed: with any one of
  them dropped from `StrictDelivery` the proof of `DeliveryStep` fails, and
  the mutant configurations give TLC counterexamples.
  `EnableCrashes`, `EnableBatching`, `EnableTimeoutFallback`,
  `PrioritizeUniqueDecisions`, `MutantAllDispatch`, `MutantNoQuorum`,
  `Quorum`, and `MaxSlots` are unconstrained.
- **Consensus is a black box, and CG1/CG2 hold by construction.** `Spec`
  has one append-only `consensusLog`. Replicas keep no log of their own:
  `LearnSlot` records only which indexes a replica has learned, and
  `ProcessContiguous` reads the entry from the shared log. So two replicas
  cannot learn different entries at one index, and the paper's Lemma 1 needs
  no argument here. The paper assumes CG1 as a property of per-replica
  learned entries; this model assumes it structurally.
- **Crashes are pauses.** `Crash` and `Recover` leave `learned`,
  `processed`, `seen`, and `delivered` untouched, so a replica that comes
  back has lost nothing. A replica that loses its deduplication state but
  keeps its position is not modelled, and the theorems say nothing about it.
  (The paper's confirmed scope is crash-stop, where this does not arise.)
- **The model's granularity.** `ProcessContiguous` handles one log index,
  that is one whole batch of at most two entries, atomically.

## `Resdet.tla` — Theorem 2 (liveness)

```
THEOREM CrashStopLiveness ==
    ASSUME LivenessAssumptions, NEW U \in SUBSET Replicas, VotersSuffice(U)
    PROVE  FairSpec => (<>[]StableOn(U) => <>DoneOn(U))
```

in `ResdetLiveness.tla`, where

- `StableOn(U) == leader # NoNode /\ U \subseteq up`: there is a leader and
  every replica in `U` is up. `<>[]StableOn(U)` says a leader eventually
  stays for good and the replicas in `U` eventually stay up. `U` is any set
  of replicas; taking it to be the replicas that stay up gives the paper's
  "every non-faulty replica". The leader need not be in `U`.
- `DoneOn(U)`: every replica in `U` has every request id in its
  deduplication state. `CrashStopDelivery` states the same conclusion as
  delivery: every replica in `U` has a delivered response for every request
  id.
- `FairSpec` is `Spec` with weak fairness on the eight protocol actions.

Replicas outside `U` may crash and recover forever, and any number of
leaders may come and go before the last one. A new leader dispatches
requests its predecessors already dispatched, and proposes its own response;
that path (the core of the paper's Lemma 3) is covered. Three caveats on
reading this as the paper's theorem:

- **The premise is stronger than CG3(1).** The paper assumes a non-faulty
  leader is eventually elected; `<>[]StableOn(U)` asks for a leader that
  then stays. In this model the leader changes only by crashing, so that
  means one final leader after finitely many changes.
- **Consensus liveness is unconditional.** Agreement is the single `Decide`
  action, which is fair and has no guard on which replicas are up. So
  CG3(2) and CG3(3) are assumed however many replicas are down, and the
  theorem holds even for `U` a single replica with every other replica down
  forever. The paper assumes CG3 under the usual fault bound.
- **A crash is a pause.** A recovered replica keeps its state, including
  what it dispatched and the responses it received. A replica that led
  before, dispatched a request, crashed, and is elected again does not
  dispatch that request again. Under pure crash-stop, where a failed
  replica never returns, this does not arise.

Corollaries, also in `ResdetLiveness.tla`:

| Theorem | Statement |
| --- | --- |
| `CrashStopDelivery` | As above, concluding `<>DeliveredOn(U)` |
| `EventualAgreement` (Lemma 3) | With `U # {}`: `<>[]StableOn(U) => <>(LogRids = RequestIds)`, every request id is eventually agreed. It is derived from the main theorem, so it carries `VotersSuffice(U)`, which the paper's Lemma 3 does not need |
| `Quiescence` | With `U # {}`: `<>[]StableOn(U) => <>[](~CanStep(U))`, eventually none of the eight enabling conditions ever holds again |
| `EventualLearning` (Lemma 4) | With `U # {}`: eventually, for good, every replica in `U` has learned every agreed index |
| `EventualProcessing` (Lemma 5) | With `U # {}`: eventually, for good, every replica in `U` has processed every agreed index |
| `StableLeaderLiveness` | `FairSpec => (<>[](leader # NoNode /\ up = Replicas) => Completion)`, with crashes enabled or not |
| `Theorem2` | With `~EnableCrashes`: `FairSpec => Completion`, the property `ResdetLiveness.cfg` checks, for unbounded finite parameters |

### Assumptions

| Assumption | Role | Paper counterpart |
| --- | --- | --- |
| `StrictDelivery`, `~MutantAllDispatch`, `~MutantNoQuorum` | The protocol, with no TLC mutant switched on | The protocol of Section 4 |
| `<>[]StableOn(U)` (premise of the theorem) | Eventually a leader exists for good and the replicas in `U` stay up | CG3(1) and "non-faulty replica" |
| `VotersSuffice(U)` | The submissions of `U` alone get a request selected: `Quorum = 1`, or the timeout fallback is on, or a single payload and `Cardinality(U) >= Quorum` | One invocation suffices (Section 4); with a caller quorum, `U` must contain a quorum, as with `n = 2f+1` and at most `f` faults |
| `PrioritizeUniqueDecisions`, `MaxSlots >= Cardinality(RequestIds)` | The log is bounded by `MaxSlots`; consensus gives each not-yet-agreed request a slot before any retry, and there is a slot for every request | **None.** It plays the role of CG3(2), but it restricts which entries consensus may agree, not only that it eventually agrees |
| `IsFiniteSet(Replicas)`, `IsFiniteSet(RequestIds)` | Needed to count outstanding work | **None for requests**: the paper's request stream is open, and its claim is per submitted request |

`EnableCrashes`, `EnableBatching`, `EnableTimeoutFallback`, and `Quorum` are
otherwise unconstrained. The assumptions are sufficient, not necessary. TLC
gives counterexamples to `Completion` without `PrioritizeUniqueDecisions`,
without the `MaxSlots` bound, with a split vote that no selection rule can
resolve, and with `MutantNonContiguous`.

Weak fairness in `FairSpec` stands for L1 (submission), L3 (downstream
service), L4 (local execution), CG3(2) and CG3(3). The model has no
messages, so L2 has no separate counterpart. The fairness is on each whole
action, for example "some replica learns some index", not on each instance,
which is weaker than the paper's per-request assumptions. It is enough here
because every instance can happen at most once and there are finitely many;
with an open request stream one request could starve. `FairSpec` has no
fairness on `Elect` or `Recover`: that a leader is eventually elected and
the replicas of `U` eventually stay up is the premise `<>[]StableOn(U)`, not
a consequence of fairness.

### How the proof works

1. **Termination** (`ResdetLiveTermination.tla`, no fairness): the protocol's
   work eventually stops, `Spec => <>[][FALSE]_WorkVars`, where `WorkVars`
   is every variable except `leader` and `up`. Each protocol step casts a
   vote, selects, dispatches, records a response, proposes, agrees a slot,
   learns an index, or processes an index; none is undone, and their number
   is bounded by the constants. Crashes, recoveries and elections may go on
   forever, but they change only `leader` and `up`.
2. **Progress** (`ResdetLiveProgress.tla`): a reachable state with
   `StableOn(U)` but not `DoneOn(U)` satisfies one of eight enabling
   conditions. This is the paper's Lemmas 3-5 read backwards: if nothing can
   step, then every request was submitted by `U`, selected, dispatched by
   the current leader, answered, proposed and agreed, and every replica in
   `U` learned and processed the whole log. The conditions mention only the
   leader and the replicas in `U`.
3. **Enabledness** (`ResdetLiveEnabled.tla`): in such a state each enabling
   condition implies the corresponding fair action is enabled.
4. **Assembly** (`ResdetLiveness.tla`): take a fair behavior with
   `<>[]StableOn(U)` that never reaches `DoneOn(U)`. Eventually the work has
   stopped and `StableOn(U)` holds forever, so the leader no longer changes.
   The enabling conditions read only the leader and `WorkVars`, so whichever
   one holds then holds forever; its action is enabled forever, weak
   fairness makes it step, and a step of a protocol action changes a work
   variable.

| Module | Content |
| --- | --- |
| `ResdetLiveInv.tla` | `LivenessAssumptions`, `StableOn`, `DoneOn`, the invariant `LiveState`, the enabling conditions; `LiveStateInvariant` |
| `ResdetLiveProgress.tla` | `Progress` |
| `ResdetLiveEnabled.tla` | `EnabledVote` ... `EnabledProcess` |
| `ResdetLiveTermination.tla` | `Termination` |
| `ResdetLiveness.tla` | `CrashStopLiveness` and the corollaries above |

### What remains narrower than the paper's Theorem 2

- **Bounded log.** The model's log has `MaxSlots` slots, and liveness needs
  the `PrioritizeUniqueDecisions` scheduling restriction on consensus. The
  proof's termination argument depends on the bound. Nothing here covers an
  unbounded log with unboundedly many retries.
- **Closed request set.** `RequestIds` is finite and every request is
  submitted by the replicas in `U`; the paper's claim is per submitted
  request over an open stream.
- **Crashes are pauses.** A replica that recovers has kept its state, and a
  replica in `U` may have crashed and recovered before it became stable.
  The paper's confirmed scope is crash-stop, which this includes, but
  loss of state on recovery is not modelled.
- **Lemmas 3-5 are stated about the final stretch, not as leads-to
  chains.** `EventualAgreement`, `EventualLearning` and `EventualProcessing`
  say what holds once the behavior has quiesced, which implies the paper's
  per-index and per-request statements in this bounded model but is derived
  differently.

## Every TLC invariant

```
THEOREM EveryCheckedInvariant == ASSUME CoreProtocol PROVE Spec => [](...)
```

in `ResdetComplete.tla`. The conjuncts are exactly the twenty `INVARIANTS`
of `ResdetCore.cfg`; the other passing configurations check subsets of
them. `CoreProtocol` is `StrictDelivery /\ ~MutantAllDispatch /\
~MutantNoQuorum`: the five mutants and the no-known-leader escape hatch are
off, and nothing else is assumed. Two invariants are conditional by design
and appear with their condition: `StrictQuorumOnly` when the timeout
fallback is off, and `AtMostOnePhysicalDispatch` when crashes are off.

| Module | Content |
| --- | --- |
| `ResdetRequests.tla` | `TypeOK`, `SelectionJustified`, `StrictQuorumOnly`, `OnlyAuthorizedDispatch`, `AtMostOnePhysicalDispatch`, `NoEarlyDelivery` |
| `ResdetApplied.tla` | `AppliedPrefixCorrect` in its literal form: the delivery history is the deduplicated flattening of the processed log prefix |
| `ResdetComplete.tla` | `EveryCheckedInvariant` |

## Further claims of the paper, for `Resdet.tla`

| Paper claim | TLAPS theorem in `ResdetContinuation.tla` |
| --- | --- |
| Sections 3.3, 6.3: deterministic continuations agree after shared inputs | `DeterministicContinuation`: for any transition function `Step` and start state, two replicas that have consumed the same number of delivered responses are in the same application state |
| Section 6.2: batching preserves results | `RebatchingPreservesDelivery`: two logs with the same entries in the same order, however grouped into batches, replay to the same deliveries |

Both are narrower than the paper's prose. `DeterministicContinuation`
models service code as a sequential function of the delivered responses
alone: no top-level requests, no threads, no request ids that depend on
state. `RebatchingPreservesDelivery` is a fact about replaying two whole
logs, not about behaviors of `Spec`; that batching preserves Theorem 1 is
the Theorem 1 proof itself, which has batching in it.

## What is not proved with TLAPS

- **That either specification matches the Go implementation or Raft.**
- **The mutant configurations.** They are expected to fail, and TLC's
  counterexamples are the evidence.
- **The Go implementation and Raft**, as for every other check in this
  repository.

## Theorem 1: proof structure

| Module | Content |
| --- | --- |
| `ResdetFold.tla` | `ApplyItemsCorrect`: what processing one agreed batch does to a replica's deduplication state and delivery history (induction over the batch) |
| `ResdetDelivery.tla` | `DeliveryInv`, the inductive invariant behind Theorem 1: every delivered response sits at the first agreed position of its request id |
| `ResdetPrefix.tla` | `ReplayInv`: delivery state is a function of the log and the processed index; prefix and race-winner agreement |
| `ResdetValidity.tla` | `ValidityInv`: the chain from physical execution through proposal and agreement to delivery, and processing order |
| `ResdetTheorems.tla` | `Theorem1` and the combined `Safety` theorem |

The argument is the paper's. A replica delivers a response for request id
`x` only when processing an entry whose id is not yet in its deduplication
state. That state is exactly the set of ids in the indexes already processed
(`SeenIsProcessed`), and indexes are processed in order with no holes, so the
entry is the first agreed entry for `x` (`DeliveredFirstCommit`). The log is
shared and append-only, so the first agreed entry for `x` is the same for
every replica (`FirstCommitUnique`), which gives `Agreement`.

## Change to `Resdet.tla`

TLAPS rejects any module that declares a `RECURSIVE` operator. The three
folds `FlattenBatches`, `ApplyItems`, and `DedupFrom` are therefore written
as recursive functions over a prefix length. They scan left to right exactly
as the previous `Head`/`Tail` recursion did, and the full TLC suite
(`make check`: six passing configurations, six mutants) reports identical
generated and distinct state counts before and after the change. The
constants `ASSUME` also gained the name `ConstantAssumptions` so proofs can
cite it.

`DoubleBatches` was a set constructor with two bound variables,
`{<<first, second>> : first \in ResponseItems, second \in ResponseItems}`,
which no TLAPS backend supports. It is now the same set written over a
product, `{<<pair[1], pair[2]>> : pair \in ResponseItems \X ResponseItems}`;
the full TLC suite again reports identical output. No action, invariant, or
existing configuration changed.

`NoConflictingResponses` was added for the witness configuration
`witness/RetryConflict.cfg`. It is not an invariant and no proof mentions it.

## Trust base

- `tlapm` build `ff40755` (rolling `1.6.0-pre` release; `scripts/fetch-tlaps.sh`
  pins the archive checksum) with Zenon 0.8.4, Z3 4.8.9, Isabelle2025, and LS4.
- Obligations are discharged by those backends. SMT and LS4 results are
  trusted as reported. Re-certification in Isabelle (`tlapm -C`) is not part
  of the check: it only re-checks the obligations Zenon proved, which are a
  handful per module, and in this TLAPS build it is unreliable. Tried on
  `ResdetFold.tla`, it re-checked two of the three Zenon obligations and
  stopped on the third with an Isabelle syntax error in the generated proof
  script (the printing of `count - 1`), not with a logical rejection.
- The proofs cite theorems of the TLAPS library (`NaturalsInduction`,
  `FiniteSetTheorems`). Their proofs ship with TLAPS and are not re-checked
  here.
- The liveness proofs additionally rely on three TLAPS features:
  `ExpandENABLED` (TLAPS's expansion of `ENABLED` into a quantifier over
  next-state values), the PTL backend for the temporal steps, and
  `NatInduction` with a temporal formula as the induction predicate, used
  three times (`HaltsBelow(n)` in `ResdetLiveTermination.tla`;
  `LearnsThrough` and `ProcessesTo` in `ResdetPaperLemma45.tla`). Each is
  induction over a constant `n` that the formula only compares against, and
  each is then used at a constant. `NatInduction` is stated for a
  constant-level predicate, so this use is outside what TLA+ level checking
  covers; it is sound because `n` is rigid, and TLAPS refuses the unsound
  variant that instantiates `n` with a state-dependent term.
- The enabledness lemmas give Isabelle an explicit tactic script instead of
  relying on proof search. The scripts only apply introduction and
  elimination rules; Isabelle checks the result.
- The paper-level liveness proofs choose a witness from a later state of
  the behavior (the index an entry was agreed at, the response a call
  returned) by proving a lemma for a constant witness, then picking the
  witness at that state and letting PTL box the result. TLAPS refuses to
  box a fact proved after such a state-level choice, which is what keeps
  this sound.
- `scripts/check-tlaps.sh` re-proves every module from an empty cache with
  `tlapm --strict`. Before that, an audit rejects axioms, omitted proofs,
  module-level assumptions in the proof modules, theorems stated in either
  specification, local modules that are not on the checked list, local
  files that shadow a library module, and a theorem name used twice. It
  checks that each specification has exactly one named assumption about
  its constants, not what that assumption says; `ConstantAssumptions` and
  `PaperAssumptions` are a few lines each and should be read. The audit is
  textual and conservative, not a proof that no other loophole exists.
- The proofs are about `Resdet.tla` and `ResdetPaper.tla`. Whether either
  specification matches the paper's pseudocode action by action is a review
  question, not something TLAPS checks. [PAPER.md](PAPER.md) records a first such review, and lists
  where the specification makes each theorem easier or harder than the
  paper's protocol.

# TLAPS proofs of Theorem 1 (safety) and Theorem 2 (liveness)

The TLC configurations check `spec/Resdet.tla` exhaustively, but only for the
finite constants in each `.cfg`. The modules described here prove, for the
same specification with the TLA+ Proof System (TLAPS):

- **Theorem 1 (safety)** and its companion safety properties, for **any**
  replica set, request, payload and response sets, quorum, and `MaxSlots`.
- **Every invariant the passing TLC configurations check**, in one theorem
  (`EveryCheckedInvariant`), under the same generality.
- **Theorem 2 (liveness)** in crash-stop form: once a leader is stable and a
  set of replicas stays up, each of them eventually delivers a response for
  every request id, whatever the other replicas do. This is for any finite
  replica and request sets, with crashes, recoveries and leader changes
  allowed. It keeps the model's bounded log. Read
  [Liveness](#theorem-2-liveness) before citing it.

```sh
make fetch-tlaps    # one-time project-local TLAPS installation
make check-tlaps    # re-prove everything from scratch, plus an audit
```

`make check-tlaps` is local. It does not launch, stop, or modify a TLC run.

## Theorem 1 (safety): what is proved

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

## Theorem 2 (liveness)

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

## What is not proved with TLAPS

- **Liveness for an unbounded log or an open request stream.** See above.
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
configuration changed.

## Trust base

- `tlapm` build `ff40755` (rolling `1.6.0-pre` release; `scripts/fetch-tlaps.sh`
  pins the archive checksum) with Zenon 0.8.4, Z3 4.8.9, Isabelle2025, and LS4.
- Obligations are discharged by those backends. SMT and LS4 results are
  trusted as reported; they are not re-certified in Isabelle (`tlapm -C`).
- The proofs cite theorems of the TLAPS library (`NaturalsInduction`,
  `FiniteSetTheorems`). Their proofs ship with TLAPS and are not re-checked
  here.
- The liveness proof additionally relies on three TLAPS features:
  `ExpandENABLED` (TLAPS's expansion of `ENABLED` into a quantifier over
  next-state values), the PTL backend for the temporal steps, and one use of
  `NatInduction` with a temporal formula as the induction predicate
  (`HaltsBelow(n)` in `ResdetLiveTermination.tla`). The last is induction
  over a constant `n` that the formula only compares against, and the final
  instance is the constant `WorkBound + 1`. `NatInduction` is stated for a
  constant-level predicate, so this use is outside what TLA+ level checking
  covers; it is sound because `n` is rigid, and TLAPS refuses the unsound
  variant that instantiates `n` with a state-dependent term.
- The enabledness lemmas give Isabelle an explicit tactic script instead of
  relying on proof search. The scripts only apply introduction and
  elimination rules; Isabelle checks the result.
- `scripts/check-tlaps.sh` re-proves every module from an empty cache with
  `tlapm --strict`. Before that, an audit rejects axioms, omitted proofs,
  module-level assumptions in the proof modules, theorems stated in
  `Resdet.tla`, local modules that are not on the checked list, and local
  files that shadow a library module. The audit is textual and conservative,
  not a proof that no other loophole exists.
- The proofs are about `Resdet.tla`. Whether that specification matches the
  paper's pseudocode action by action is a review question, not something
  TLAPS checks.

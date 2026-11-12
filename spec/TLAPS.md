# TLAPS proofs of Theorem 1 (safety) and Theorem 2 (liveness)

The TLC configurations check `spec/Resdet.tla` exhaustively, but only for the
finite constants in each `.cfg`. The modules described here prove the paper's
two theorems for the same specification with the TLA+ Proof System (TLAPS):

- **Theorem 1 (safety)** and its companion safety properties, for **any**
  replica set, request, payload and response sets, quorum, and `MaxSlots`.
- **Theorem 2 (liveness)**, for any finite replica and request sets and any
  payload and response sets, under the conditions in
  [Liveness](#theorem-2-liveness) below. Read that section before citing it:
  it is liveness of this bounded-log model with a leader that is stable from
  the start, not of the protocol under leader changes.

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
THEOREM Theorem2 == ASSUME LivenessAssumptions PROVE FairSpec => Completion
```

in `ResdetLiveness.tla`. `Completion` is the property the TLC liveness
configuration checks: eventually every replica's deduplication state holds
every request id. `Theorem2Delivered` states the same result as delivery:
`FairSpec => <>AllDelivered`, eventually every replica has a delivered
response for every request id. `FairSpec` is `Spec` with weak fairness on
the eight protocol actions.

This is narrower than the paper's Theorem 2 in three ways, detailed below:
no replica ever crashes, the log is bounded with a scheduling restriction on
consensus, and the request set is closed with every request submitted.

### What `LivenessAssumptions` says

`Completion` is not a theorem of `FairSpec` for arbitrary constants, so the
theorem carries conditions under which it holds (`ResdetLiveInv.tla`). They
are sufficient, not necessary. TLC gives counterexamples to `Completion`
without `~EnableCrashes`, without `PrioritizeUniqueDecisions`, without the
`MaxSlots` bound, without the selection condition (two payloads, quorum two,
split vote), and with `MutantNonContiguous`. The other mutant switches and
the exact form of the selection condition are needed by the proof, not by
the property.

| Conjunct | Role | Paper counterpart |
| --- | --- | --- |
| `StrictDelivery`, `~MutantAllDispatch`, `~MutantNoQuorum` | The protocol, with no TLC mutant switched on | The protocol of Section 4 |
| `~EnableCrashes` | No replica ever crashes; the initial leader stays leader | CG3(1), but **stronger**: the paper only needs a non-faulty leader eventually. `FairSpec` has no fairness on `Elect` or `Recover`, so nothing in it stands for CG3(1) |
| `PrioritizeUniqueDecisions`, `MaxSlots >= Cardinality(RequestIds)` | The log is bounded by `MaxSlots`; consensus gives each not-yet-agreed request a slot before any retry, and there is a slot for every request | **None.** It plays the role of CG3(2), but it restricts which entries consensus may agree, not only that it eventually agrees |
| `IsFiniteSet(Replicas)`, `IsFiniteSet(RequestIds)` | Needed to count outstanding work | **None for requests**: the paper's request stream is open, and its claim is per submitted request |
| `Quorum = 1`, or `EnableTimeoutFallback`, or a single payload | A request can be selected once every replica has submitted it | One invocation suffices (Section 4), or the same request body per id (Section 3) |

Weak fairness in `FairSpec` stands for L1 (submission), L3 (downstream
service), L4 (local execution), CG3(2) and CG3(3). The model has no
messages, so L2 has no separate counterpart. The fairness is on each whole
action, for example "some replica learns some index", not on each instance,
which is weaker than the paper's per-request assumptions. It is enough here
only because every instance can happen at most once and there are finitely
many; with an open request stream one request could starve.

### What kind of result this is

Under `LivenessAssumptions` the model does a bounded amount of work: every
step casts a vote, selects, dispatches, records a response, proposes, agrees
a slot, learns an index, or processes an index, and none of these is ever
undone or repeated. The proof uses exactly that:

1. **Termination** (`ResdetLiveTermination.tla`, no fairness): every behavior
   of `Spec` eventually stops changing, because a natural-number measure of
   outstanding work strictly decreases on every step that changes the state.
2. **Progress** (`ResdetLiveProgress.tla`): a reachable state in which not
   every replica has delivered everything satisfies one of eight enabling
   conditions. This is the paper's Lemmas 3-5 read backwards: if nothing can
   step, then every request was submitted, selected, dispatched, answered,
   proposed and agreed, and every replica learned and processed the whole
   log.
3. **Enabledness** (`ResdetLiveEnabled.tla`): each enabling condition implies
   the corresponding fair action is enabled and changes the state.
4. **Assembly** (`ResdetLiveness.tla`): a fair behavior that never completes
   would stop changing with one fair action enabled forever, which weak
   fairness forbids.

So this is "the model does finitely much work and cannot stop early". It
is not a leads-to proof that mirrors Lemmas 3-5 step by step, and it does
not address leader changes, crashed replicas, retries after a failure, or
an unbounded log; re-dispatch by a new leader, the core of Lemma 3, is never
exercised. For liveness under crash-stop failover and retries, see the
conditional Lean proofs (`lean/PAPER.md`), which assume their progress
contracts rather than deriving them from fairness.

A stronger statement is true of the model and is not proved here. With
crashes enabled, TLC confirms on a two-replica, two-request configuration
that `<>[](leader # NoNode /\ up = Replicas) => Completion` holds under
`FairSpec`. The termination argument cannot reach it, because crash and
recovery cycles never terminate.

| Module | Content |
| --- | --- |
| `ResdetLiveInv.tla` | `LivenessAssumptions`, the invariant `LiveState`, the enabling conditions; `LiveStateInvariant` |
| `ResdetLiveProgress.tla` | `Progress`: `LiveState /\ ~Done => CanStep` |
| `ResdetLiveEnabled.tla` | `EnabledVote` ... `EnabledProcess`: each condition implies `ENABLED <<A>>_vars` |
| `ResdetLiveTermination.tla` | `Termination`: `Spec => <>[][FALSE]_vars` |
| `ResdetLiveness.tla` | `Theorem2`, `Theorem2Delivered` |

## What is not proved with TLAPS

- **Liveness under leader changes, crashes, or an unbounded log.** See above.
- **Request-side invariants** `SelectionJustified`, `StrictQuorumOnly`,
  `OnlyAuthorizedDispatch`, `AtMostOnePhysicalDispatch`, `NoEarlyDelivery`,
  and the full `TypeOK`. TLC checks them; they are not part of Theorem 1.
- **`AppliedPrefixCorrect` in its literal form.** `ReplayInvariant` states the
  same fact (delivery state equals the deduplicated replay of the processed
  prefix) with `ApplyItems` instead of `DedupFrom`/`FlattenBatches`.
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
cite it. No action, invariant, or configuration changed.

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

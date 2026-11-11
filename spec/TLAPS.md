# TLAPS proof of Theorem 1 (safety)

The TLC configurations check `spec/Resdet.tla` exhaustively, but only for the
finite constants in each `.cfg`. The modules described here prove the paper's
Theorem 1 and its companion safety properties for the same specification with
the TLA+ Proof System (TLAPS), for **any** replica set, request, payload and
response sets, quorum, and `MaxSlots`.

```sh
make fetch-tlaps    # one-time project-local TLAPS installation
make check-tlaps    # re-prove everything from scratch, plus an audit
```

`make check-tlaps` is local. It does not launch, stop, or modify a TLC run.

## What is proved

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

## Assumptions

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

## What is not proved with TLAPS

- **Theorem 2 (liveness).** It stays with the bounded TLC check of
  `Completion` under `FairSpec` and with the conditional Lean proofs.
  `Completion` as written depends on the finite `MaxSlots` and on
  `PrioritizeUniqueDecisions`, so it is not a general theorem of `FairSpec`.
- **Request-side invariants** `SelectionJustified`, `StrictQuorumOnly`,
  `OnlyAuthorizedDispatch`, `AtMostOnePhysicalDispatch`, `NoEarlyDelivery`,
  and the full `TypeOK`. TLC checks them; they are not part of Theorem 1.
- **`AppliedPrefixCorrect` in its literal form.** `ReplayInvariant` states the
  same fact (delivery state equals the deduplicated replay of the processed
  prefix) with `ApplyItems` instead of `DedupFrom`/`FlattenBatches`.
- **The Go implementation and Raft**, as for every other check in this
  repository.

## Proof structure

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
- `scripts/check-tlaps.sh` re-proves every module from an empty cache with
  `tlapm --strict`. Before that, an audit rejects axioms, omitted proofs,
  module-level assumptions in the proof modules, theorems stated in
  `Resdet.tla`, local modules that are not on the checked list, and local
  files that shadow a library module. The audit is textual and conservative,
  not a proof that no other loophole exists.
- The proofs are about `Resdet.tla`. Whether that specification matches the
  paper's pseudocode action by action is a review question, not something
  TLAPS checks.

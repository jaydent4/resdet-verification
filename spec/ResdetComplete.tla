--------------------------- MODULE ResdetComplete ---------------------------
(***************************************************************************
Every invariant that the passing TLC configurations check, proved with
TLAPS for unbounded parameters, in one statement.

The twenty conjuncts are exactly the INVARIANTS of ResdetCore.cfg (the
other passing configurations check subsets of them). TLC establishes them
for the finite constants of each configuration; this theorem establishes
them for every replica set, request, payload and response sets, quorum,
and MaxSlots, with batching, crashes and the timeout fallback on or off.

CoreProtocol switches off the five TLC mutants and the no-known-leader
escape hatch, nothing else. Two invariants are by design conditional on a
further switch and appear here with that condition: StrictQuorumOnly holds
when the timeout fallback is off, and AtMostOnePhysicalDispatch when
crashes are off (a new leader may dispatch again; see README, "Exact-once
boundary").
***************************************************************************)
EXTENDS ResdetRequests, ResdetApplied

CoreProtocol ==
    /\ StrictDelivery
    /\ ~MutantAllDispatch
    /\ ~MutantNoQuorum

THEOREM EveryCheckedInvariant ==
    ASSUME CoreProtocol
    PROVE  Spec => [](/\ TypeOK
                      /\ SelectionJustified
                      /\ ~EnableTimeoutFallback => StrictQuorumOnly
                      /\ NoDispatchBeforeSelection
                      /\ OnlyAuthorizedDispatch
                      /\ ObservedHasPhysicalExecution
                      /\ ProposalValidity
                      /\ ConsensusValidity
                      /\ ~EnableCrashes => AtMostOnePhysicalDispatch
                      /\ AtMostOnceDelivery
                      /\ ResponseAgreement
                      /\ PrefixAgreement
                      /\ ProcessedPrefixLearned
                      /\ LearnedOnlyDecided
                      /\ ProcessedWithinLog
                      /\ AppliedPrefixCorrect
                      /\ ResponseValidity
                      /\ SeenMatchesDelivered
                      /\ RaceWinnerAgreement
                      /\ NoEarlyDelivery)
<1> USE DEF CoreProtocol
<1>1. Spec => [](/\ ResponseAgreement
                 /\ AtMostOnceDelivery
                 /\ SeenMatchesDelivered
                 /\ PrefixAgreement
                 /\ RaceWinnerAgreement
                 /\ ResponseValidity
                 /\ ConsensusValidity
                 /\ ProposalValidity
                 /\ ObservedHasPhysicalExecution
                 /\ NoDispatchBeforeSelection
                 /\ ProcessedPrefixLearned
                 /\ LearnedOnlyDecided
                 /\ ProcessedWithinLog)
  BY Safety, PTL
<1>2. Spec => [](/\ TypeOK
                 /\ SelectionJustified
                 /\ OnlyAuthorizedDispatch
                 /\ NoEarlyDelivery
                 /\ AppliedPrefixCorrect)
  BY TypeOKInvariant, SelectionJustifiedInvariant,
     OnlyAuthorizedDispatchInvariant, NoEarlyDeliveryInvariant,
     AppliedPrefixCorrectInvariant, PTL
<1>3. Spec => [](~EnableTimeoutFallback => StrictQuorumOnly)
  <2>1. CASE ~EnableTimeoutFallback
    BY <2>1, StrictQuorumOnlyInvariant, PTL
  <2>2. CASE EnableTimeoutFallback
    <3>1. ~EnableTimeoutFallback => StrictQuorumOnly
      BY <2>2
    <3> QED
      BY <3>1, PTL
  <2> QED
    BY <2>1, <2>2
<1>4. Spec => [](~EnableCrashes => AtMostOnePhysicalDispatch)
  <2>1. CASE ~EnableCrashes
    BY <2>1, AtMostOnePhysicalDispatchInvariant, PTL
  <2>2. CASE EnableCrashes
    <3>1. ~EnableCrashes => AtMostOnePhysicalDispatch
      BY <2>2
    <3> QED
      BY <3>1, PTL
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, PTL
=============================================================================

--------------------------- MODULE ResdetLiveness ---------------------------
(***************************************************************************
TLAPS liveness proof, part 5 of 5: the paper's Theorem 2.

  CrashStopLiveness ==
      LivenessAssumptions, U \subseteq Replicas, VotersSuffice(U)  =>
          FairSpec => (<>[]StableOn(U) => <>DoneOn(U))

If from some point on there is a leader and every replica in U stays up,
then every replica in U eventually delivers a response for every request
id. U is any set of replicas; taking it to be the replicas that stay up
gives the paper's "every non-faulty replica". The other replicas may
crash and recover forever, and any number of leaders may come before the
last one.

Three things to keep in mind when reading this as the paper's Theorem 2.
The premise <>[]StableOn(U) asks for a leader that stays for good, which
is stronger than CG3(1) as the paper states it (a non-faulty leader is
eventually elected). Consensus in this model is the single Decide action,
which is fair and has no guard on which replicas are up, so CG3(2) and
CG3(3) are assumed however many replicas are down; the paper assumes
them under the usual fault bound. And a crash is a pause: a replica that
recovers keeps its state, so a replica that led before, dispatched a
request, crashed and is elected again does not dispatch it again.

FairSpec's weak fairness on the eight protocol actions stands for the
paper's liveness assumptions: request submission (L1), the downstream
service (L3), local execution (L4), and consensus agreeing and delivering
entries (CG3(2), CG3(3)). The model has no messages, so L2 has no
separate counterpart. Fairness is on each whole action, not on each
instance; that suffices because every instance happens at most once.

The argument has three parts, proved in the three modules extended here.

  Termination   The protocol's work eventually stops: from some point on
                only leader and up change (no fairness needed).
  Progress      A reachable state with StableOn(U) but not DoneOn(U)
                satisfies one of eight enabling conditions.
  Enabled*      In such a state each enabling condition implies that its
                fair action is enabled.

Suppose a fair behavior has <>[]StableOn(U) and never reaches DoneOn(U).
Eventually the work has stopped and StableOn(U) holds forever. The leader
no longer changes, and the enabling conditions read only the leader and
the work variables, so whichever condition holds then holds forever. Its
action is enabled forever, so weak fairness makes it step, and a step of
a protocol action changes a work variable: a contradiction.

What remains narrower than the paper: the log is bounded with the
PrioritizeUniqueDecisions scheduling restriction, the request set is
closed and finite with every request submitted by the replicas in U, and
a crashed replica keeps its state (crashes are pauses).
***************************************************************************)
EXTENDS ResdetLiveProgress, ResdetLiveEnabled, ResdetLiveTermination

(* The enabling conditions read only the work variables and the leader. *)
LEMMA CanStable ==
    ASSUME NEW U
    PROVE  UNCHANGED WorkVars /\ leader' = leader =>
               /\ CanVote(U)' <=> CanVote(U)
               /\ CanSelect(U)' <=> CanSelect(U)
               /\ CanDispatch' <=> CanDispatch
               /\ CanRespond' <=> CanRespond
               /\ CanPropose' <=> CanPropose
               /\ CanDecide' <=> CanDecide
               /\ CanLearn(U)' <=> CanLearn(U)
               /\ CanProcess(U)' <=> CanProcess(U)
<1> SUFFICES ASSUME UNCHANGED WorkVars, leader' = leader
             PROVE  /\ CanVote(U)' <=> CanVote(U)
                    /\ CanSelect(U)' <=> CanSelect(U)
                    /\ CanDispatch' <=> CanDispatch
                    /\ CanRespond' <=> CanRespond
                    /\ CanPropose' <=> CanPropose
                    /\ CanDecide' <=> CanDecide
                    /\ CanLearn(U)' <=> CanLearn(U)
                    /\ CanProcess(U)' <=> CanProcess(U)
  OBVIOUS
<1>0. /\ leader' = leader /\ votes' = votes /\ selected' = selected
      /\ dispatchers' = dispatchers /\ execResponse' = execResponse
      /\ proposed' = proposed /\ consensusLog' = consensusLog
      /\ learned' = learned /\ processed' = processed
  BY DEF WorkVars
<1>1. CanVote(U)' <=> CanVote(U)
  BY <1>0 DEF CanVote, HasVoted
<1>2. CanSelect(U)' <=> CanSelect(U)
  BY <1>0 DEF CanSelect, HasVoted
<1>3. CanDispatch' <=> CanDispatch
  BY <1>0 DEF CanDispatch
<1>4. CanRespond' <=> CanRespond
  BY <1>0 DEF CanRespond
<1>5. CanPropose' <=> CanPropose
  BY <1>0 DEF CanPropose, ObservedItem
<1>6. CanDecide' <=> CanDecide
  BY <1>0 DEF CanDecide, LogRids
<1>7. CanLearn(U)' <=> CanLearn(U)
  BY <1>0 DEF CanLearn
<1>8. CanProcess(U)' <=> CanProcess(U)
  BY <1>0 DEF CanProcess
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8

(* A leader that is still the leader after a step is the same leader:
   the only ways to change it go through "no leader". *)
LEMMA LeaderStays ==
    leader # NoNode /\ leader' # NoNode /\ [Next]_vars => leader' = leader
<1> SUFFICES ASSUME leader # NoNode, leader' # NoNode, [Next]_vars
             PROVE  leader' = leader
  OBVIOUS
<1>1. CASE SubmitVoteAction
  BY <1>1 DEF SubmitVoteAction, SubmitVote
<1>2. CASE SelectAction
  BY <1>2 DEF SelectAction, SelectByQuorum, TimeoutSelect
<1>3. CASE DispatchAction
  BY <1>3 DEF DispatchAction, Dispatch
<1>4. CASE ExternalRespondAction
  BY <1>4 DEF ExternalRespondAction, ExternalRespond
<1>5. CASE ProposeResponseAction
  BY <1>5 DEF ProposeResponseAction, ProposeResponse
<1>6. CASE DecideAction
  BY <1>6 DEF DecideAction, DecideOne, DecidePair
<1>7. CASE LearnAction
  BY <1>7 DEF LearnAction, LearnSlot
<1>8. CASE ProcessAction
  BY <1>8 DEF ProcessAction, ProcessContiguous
<1>9. CASE \E replica \in Replicas, slot \in 1..MaxSlots :
              ProcessNonContiguous(replica, slot)
  BY <1>9 DEF ProcessNonContiguous
<1>10. CASE \E replica \in Replicas, item \in ResponseItems :
               DeliverBeforeConsensus(replica, item)
  BY <1>10 DEF DeliverBeforeConsensus
<1>11. CASE \E replica \in Replicas : Crash(replica)
  BY <1>11 DEF Crash
<1>12. CASE \E replica \in Replicas : Recover(replica)
  BY <1>12 DEF Recover
<1>13. CASE \E replica \in Replicas : Elect(replica)
  BY <1>13 DEF Elect
<1>14. CASE \E replica \in Replicas,
               request \in RequestIds,
               payload \in Payloads :
               NoLeaderDispatch(replica, request, payload)
  BY <1>14 DEF NoLeaderDispatch
<1>15. CASE \E replica \in Replicas,
               request \in RequestIds,
               responseValue \in Responses :
               DirectNoLeaderRespond(replica, request, responseValue)
  BY <1>15 DEF DirectNoLeaderRespond
<1>16. CASE UNCHANGED vars
  BY <1>16 DEF vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
     <1>11, <1>12, <1>13, <1>14, <1>15, <1>16 DEF Next

(* The fair actions leave leader and up alone, so a step of one that
   changes the state changes a work variable. *)
LEMMA FairStepsWork ==
    /\ <<SubmitVoteAction>>_vars => ~UNCHANGED WorkVars
    /\ <<SelectAction>>_vars => ~UNCHANGED WorkVars
    /\ <<DispatchAction>>_vars => ~UNCHANGED WorkVars
    /\ <<ExternalRespondAction>>_vars => ~UNCHANGED WorkVars
    /\ <<ProposeResponseAction>>_vars => ~UNCHANGED WorkVars
    /\ <<DecideAction>>_vars => ~UNCHANGED WorkVars
    /\ <<LearnAction>>_vars => ~UNCHANGED WorkVars
    /\ <<ProcessAction>>_vars => ~UNCHANGED WorkVars
<1>1. <<SubmitVoteAction>>_vars => ~UNCHANGED WorkVars
  BY DEF SubmitVoteAction, SubmitVote, vars, WorkVars
<1>2. <<SelectAction>>_vars => ~UNCHANGED WorkVars
  BY DEF SelectAction, SelectByQuorum, TimeoutSelect, vars, WorkVars
<1>3. <<DispatchAction>>_vars => ~UNCHANGED WorkVars
  BY DEF DispatchAction, Dispatch, vars, WorkVars
<1>4. <<ExternalRespondAction>>_vars => ~UNCHANGED WorkVars
  BY DEF ExternalRespondAction, ExternalRespond, vars, WorkVars
<1>5. <<ProposeResponseAction>>_vars => ~UNCHANGED WorkVars
  BY DEF ProposeResponseAction, ProposeResponse, vars, WorkVars
<1>6. <<DecideAction>>_vars => ~UNCHANGED WorkVars
  BY DEF DecideAction, DecideOne, DecidePair, vars, WorkVars
<1>7. <<LearnAction>>_vars => ~UNCHANGED WorkVars
  BY DEF LearnAction, LearnSlot, vars, WorkVars
<1>8. <<ProcessAction>>_vars => ~UNCHANGED WorkVars
  BY DEF ProcessAction, ProcessContiguous, vars, WorkVars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8

(***************************************************************************
Theorem 2 (Liveness), paper Section 5, in crash-stop form.
***************************************************************************)
THEOREM CrashStopLiveness ==
    ASSUME LivenessAssumptions,
           NEW U \in SUBSET Replicas,
           VotersSuffice(U)
    PROVE  FairSpec => (<>[]StableOn(U) => <>DoneOn(U))
<1>1. CASE U = {}
  <2>1. DoneOn(U)
    BY <1>1 DEF DoneOn
  <2> QED
    BY <2>1, PTL
<1>2. CASE U # {}
  <2>1. LiveState /\ StableOn(U) /\ ~DoneOn(U) => CanStep(U)
    BY Progress
  <2>2. /\ LiveState /\ StableOn(U) /\ CanVote(U)
              => ENABLED <<SubmitVoteAction>>_vars
        /\ LiveState /\ StableOn(U) /\ CanSelect(U)
              => ENABLED <<SelectAction>>_vars
        /\ LiveState /\ StableOn(U) /\ CanDispatch
              => ENABLED <<DispatchAction>>_vars
        /\ LiveState /\ StableOn(U) /\ CanRespond
              => ENABLED <<ExternalRespondAction>>_vars
        /\ LiveState /\ StableOn(U) /\ CanPropose
              => ENABLED <<ProposeResponseAction>>_vars
        /\ LiveState /\ StableOn(U) /\ CanDecide
              => ENABLED <<DecideAction>>_vars
        /\ LiveState /\ StableOn(U) /\ CanLearn(U)
              => ENABLED <<LearnAction>>_vars
        /\ LiveState /\ StableOn(U) /\ CanProcess(U)
              => ENABLED <<ProcessAction>>_vars
    BY <1>2, EnabledVote, EnabledSelect, EnabledDispatch, EnabledRespond,
       EnabledPropose, EnabledDecide, EnabledLearn, EnabledProcess
  <2>3. Spec => []LiveState
    BY LiveStateInvariant
  <2>4. Spec => <>[][FALSE]_WorkVars
    BY Termination
  <2>5. StableOn(U) /\ StableOn(U)' /\ [Next]_vars => leader' = leader
    BY LeaderStays DEF StableOn
  <2>6. UNCHANGED WorkVars /\ leader' = leader =>
            /\ CanVote(U)' <=> CanVote(U)
            /\ CanSelect(U)' <=> CanSelect(U)
            /\ CanDispatch' <=> CanDispatch
            /\ CanRespond' <=> CanRespond
            /\ CanPropose' <=> CanPropose
            /\ CanDecide' <=> CanDecide
            /\ CanLearn(U)' <=> CanLearn(U)
            /\ CanProcess(U)' <=> CanProcess(U)
    BY CanStable
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, FairStepsWork, PTL
       DEF FairSpec, Spec, CanStep
<1> QED
  BY <1>1, <1>2

(***************************************************************************
Corollaries.
***************************************************************************)

(* A request can be selected once every replica has submitted it. *)
SelectionPossible ==
    \/ Quorum = 1
    \/ EnableTimeoutFallback
    \/ \E payload \in Payloads : Payloads = {payload}

LEMMA AllReplicasSuffice ==
    ASSUME LivenessAssumptions, SelectionPossible
    PROVE  VotersSuffice(Replicas)
<1>1. Cardinality(Replicas) >= Quorum
  BY ConstantAssumptions, FS_CardinalityType DEF LivenessAssumptions
<1> QED
  BY <1>1 DEF VotersSuffice, SelectionPossible

(* The same result as delivery, in the paper's words. *)
DeliveredOn(U) ==
    \A replica \in U :
        \A request \in RequestIds :
            \E i \in 1..Len(delivered[replica]) :
                delivered[replica][i].rid = request

THEOREM CrashStopDelivery ==
    ASSUME LivenessAssumptions,
           NEW U \in SUBSET Replicas,
           VotersSuffice(U)
    PROVE  FairSpec => (<>[]StableOn(U) => <>DeliveredOn(U))
<1>1. LiveState /\ DoneOn(U) => DeliveredOn(U)
  BY DEF LiveState, DeliveryInv, SeenDelivered, DoneOn, DeliveredOn
<1>2. Spec => []LiveState
  BY LiveStateInvariant
<1> QED
  BY <1>1, <1>2, CrashStopLiveness, PTL DEF FairSpec

(* Lemma 3 (eventual agreement): with a stable leader and at least one
   replica that stays up, every request id is eventually agreed. *)
THEOREM EventualAgreement ==
    ASSUME LivenessAssumptions,
           NEW U \in SUBSET Replicas, U # {},
           VotersSuffice(U)
    PROVE  FairSpec => (<>[]StableOn(U) => <>(LogRids = RequestIds))
<1>1. LiveState /\ DoneOn(U) => LogRids = RequestIds
  <2> SUFFICES ASSUME LiveState, DoneOn(U)
               PROVE  LogRids = RequestIds
    OBVIOUS
  <2>1. PICK r \in U : seen[r] = RequestIds
    BY DEF DoneOn
  <2>2. /\ r \in Replicas
        /\ processed[r] \in Nat
        /\ Len(consensusLog) \in Nat
        /\ processed[r] <= Len(consensusLog)
    BY DEF LiveState, DeliveryInv, DeliveryTypeOK
  <2>3. \A x \in RequestIds :
            \E s \in 1..processed[r] :
                \E k \in 1..Len(consensusLog[s]) :
                    consensusLog[s][k].rid = x
    BY <2>1, <2>2 DEF LiveState, DeliveryInv, SeenIsProcessed
  <2>4. \A x \in RequestIds : x \in LogRids
    <3> TAKE x \in RequestIds
    <3>1. PICK s \in 1..processed[r] :
              \E k \in 1..Len(consensusLog[s]) :
                  consensusLog[s][k].rid = x
      BY <2>3
    <3>2. s \in 1..Len(consensusLog)
      BY <2>2
    <3> QED
      BY <3>1, <3>2 DEF LogRids
  <2> QED
    BY <2>4 DEF LogRids
<1>2. Spec => []LiveState
  BY LiveStateInvariant
<1> QED
  BY <1>1, <1>2, CrashStopLiveness, PTL DEF FairSpec

(* With every replica eventually up for good and a leader in place, the
   property of the TLC liveness configuration holds, crashes or not. *)
THEOREM StableLeaderLiveness ==
    ASSUME LivenessAssumptions, SelectionPossible
    PROVE  FairSpec =>
               (<>[](leader # NoNode /\ up = Replicas) => Completion)
<1>1. PICK U \in SUBSET Replicas : U = Replicas
  OBVIOUS
<1>2. VotersSuffice(U)
  BY <1>1, AllReplicasSuffice
<1>3. FairSpec => (<>[]StableOn(U) => <>DoneOn(U))
  BY <1>2, CrashStopLiveness
<1>4. (leader # NoNode /\ up = Replicas) => StableOn(U)
  BY <1>1 DEF StableOn
<1>5. DoneOn(U) => Done
  BY <1>1 DEF Done
<1>6. FairSpec => (<>[](leader # NoNode /\ up = Replicas) => <>Done)
  BY <1>3, <1>4, <1>5, PTL
<1> QED
  BY <1>6 DEF Completion, Done, DoneOn

(* Without crashes the leader is stable from the start, and FairSpec
   implies Completion outright: the TLC liveness check, unbounded. *)
THEOREM Theorem2 ==
    ASSUME LivenessAssumptions, SelectionPossible, ~EnableCrashes
    PROVE  FairSpec => Completion
<1>1. LiveState => (leader # NoNode /\ up = Replicas)
  BY DEF LiveState, LiveInv, NoCrashStable
<1>2. Spec => []LiveState
  BY LiveStateInvariant
<1>3. FairSpec => (<>[](leader # NoNode /\ up = Replicas) => Completion)
  BY StableLeaderLiveness
<1> QED
  BY <1>1, <1>2, <1>3, PTL DEF FairSpec
(***************************************************************************
Quiescence, and the paper's Lemmas 4 and 5.

With a stable leader and a non-empty set U of replicas that stay up, the
behavior reaches a point after which none of the eight enabling conditions
ever holds again. Read off the conditions one by one, that final stretch
is the conclusion of each step of the paper's liveness proof: every
replica in U has submitted every request, every request is selected,
dispatched by the leader, answered, proposed and agreed (Lemma 3), and
every replica in U has learned every agreed index (Lemma 4) and processed
it (Lemma 5).
***************************************************************************)
THEOREM Quiescence ==
    ASSUME LivenessAssumptions,
           NEW U \in SUBSET Replicas, U # {},
           VotersSuffice(U)
    PROVE  FairSpec => (<>[]StableOn(U) => <>[](~CanStep(U)))
<1>1. /\ LiveState /\ StableOn(U) /\ CanVote(U)
            => ENABLED <<SubmitVoteAction>>_vars
      /\ LiveState /\ StableOn(U) /\ CanSelect(U)
            => ENABLED <<SelectAction>>_vars
      /\ LiveState /\ StableOn(U) /\ CanDispatch
            => ENABLED <<DispatchAction>>_vars
      /\ LiveState /\ StableOn(U) /\ CanRespond
            => ENABLED <<ExternalRespondAction>>_vars
      /\ LiveState /\ StableOn(U) /\ CanPropose
            => ENABLED <<ProposeResponseAction>>_vars
      /\ LiveState /\ StableOn(U) /\ CanDecide
            => ENABLED <<DecideAction>>_vars
      /\ LiveState /\ StableOn(U) /\ CanLearn(U)
            => ENABLED <<LearnAction>>_vars
      /\ LiveState /\ StableOn(U) /\ CanProcess(U)
            => ENABLED <<ProcessAction>>_vars
  BY EnabledVote, EnabledSelect, EnabledDispatch, EnabledRespond,
     EnabledPropose, EnabledDecide, EnabledLearn, EnabledProcess
<1>2. Spec => []LiveState
  BY LiveStateInvariant
<1>3. Spec => <>[][FALSE]_WorkVars
  BY Termination
<1>4. StableOn(U) /\ StableOn(U)' /\ [Next]_vars => leader' = leader
  BY LeaderStays DEF StableOn
<1>5. UNCHANGED WorkVars /\ leader' = leader =>
          /\ CanVote(U)' <=> CanVote(U)
          /\ CanSelect(U)' <=> CanSelect(U)
          /\ CanDispatch' <=> CanDispatch
          /\ CanRespond' <=> CanRespond
          /\ CanPropose' <=> CanPropose
          /\ CanDecide' <=> CanDecide
          /\ CanLearn(U)' <=> CanLearn(U)
          /\ CanProcess(U)' <=> CanProcess(U)
  BY CanStable
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, FairStepsWork, PTL
     DEF FairSpec, Spec, CanStep

(* Lemma 4 (eventual prefix learning): every replica that stays up
   eventually has learned every agreed index, for good. *)
LearnedAll(U) ==
    \A replica \in U :
        \A slot \in 1..Len(consensusLog) : slot \in learned[replica]

THEOREM EventualLearning ==
    ASSUME LivenessAssumptions,
           NEW U \in SUBSET Replicas, U # {},
           VotersSuffice(U)
    PROVE  FairSpec => (<>[]StableOn(U) => <>[]LearnedAll(U))
<1>1. ~CanStep(U) => LearnedAll(U)
  BY DEF CanStep, CanLearn, LearnedAll
<1> QED
  BY <1>1, Quiescence, PTL

(* Lemma 5 (eventual delivery), in the form "processes the whole agreed
   log": every replica that stays up eventually has processed every agreed
   index, for good. CrashStopDelivery gives the delivered responses. *)
ProcessedAll(U) ==
    \A replica \in U : processed[replica] = Len(consensusLog)

THEOREM EventualProcessing ==
    ASSUME LivenessAssumptions,
           NEW U \in SUBSET Replicas, U # {},
           VotersSuffice(U)
    PROVE  FairSpec => (<>[]StableOn(U) => <>[]ProcessedAll(U))
<1>1. LiveState /\ ~CanStep(U) => ProcessedAll(U)
  <2> SUFFICES ASSUME LiveState, ~CanStep(U), NEW r \in U
               PROVE  processed[r] = Len(consensusLog)
    BY DEF ProcessedAll
  <2>1. /\ r \in Replicas
        /\ processed[r] \in Nat
        /\ Len(consensusLog) \in Nat
        /\ processed[r] <= Len(consensusLog)
    BY DEF LiveState, DeliveryInv, DeliveryTypeOK
  <2>2. \A slot \in 1..Len(consensusLog) : slot \in learned[r]
    BY DEF CanStep, CanLearn
  <2>3. ~(/\ processed[r] < Len(consensusLog)
          /\ processed[r] + 1 \in learned[r])
    BY DEF CanStep, CanProcess
  <2> QED
    BY <2>1, <2>2, <2>3
<1>2. Spec => []LiveState
  BY LiveStateInvariant
<1> QED
  BY <1>1, <1>2, Quiescence, PTL DEF FairSpec
=============================================================================

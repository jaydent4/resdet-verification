--------------------------- MODULE ResdetLiveness ---------------------------
(***************************************************************************
TLAPS liveness proof, part 5 of 5: the paper's Theorem 2 for this model
with a leader that is stable from the start.

  Theorem2 ==  LivenessAssumptions  =>  (FairSpec => Completion)

Every replica eventually delivers a response for every request id, for
any finite replica and request sets, any payload and response sets, and
any MaxSlots with room for every request. FairSpec's weak fairness on
the eight protocol actions stands for the paper's liveness assumptions:
request submission (L1), the downstream service (L3), local execution
(L4), and consensus agreeing and delivering entries (CG3(2), CG3(3)).
The model has no messages, so L2 has no separate counterpart.

This is narrower than the paper's Theorem 2. LivenessAssumptions rules
out every crash, where the paper needs only an eventually stable
non-faulty leader (CG3(1)); the request set is closed and every request
is submitted, where the paper's claim is per submitted request; and the
argument is that the model does a bounded amount of work and cannot stop
before it is done, which does not extend to leader changes, retries, or
an unbounded log. Fairness is on each whole action, not on each
instance, and suffices only because every instance happens at most once.

The argument has three parts, proved in the three modules extended here.

  Progress      A reachable state that is not Done satisfies one of the
                eight enabling conditions Can*.
  Enabled*      Each enabling condition implies its fair action is
                enabled.
  Termination   Every behavior eventually stops changing.

Suppose a fair behavior never reaches Done. It eventually stops changing,
and from then on one particular enabling condition holds forever, because
the conditions are state predicates and the state no longer changes. The
corresponding action is then enabled forever, so weak fairness makes it
step, and a step of <<A>>_vars changes the state: a contradiction.
***************************************************************************)
EXTENDS ResdetLiveProgress, ResdetLiveEnabled, ResdetLiveTermination

(* The enabling conditions read only the state, so a stuttering step
   leaves each of them as it was. *)
LEMMA CanStable ==
    UNCHANGED vars =>
        /\ CanVote' <=> CanVote
        /\ CanSelect' <=> CanSelect
        /\ CanDispatch' <=> CanDispatch
        /\ CanRespond' <=> CanRespond
        /\ CanPropose' <=> CanPropose
        /\ CanDecide' <=> CanDecide
        /\ CanLearn' <=> CanLearn
        /\ CanProcess' <=> CanProcess
<1> SUFFICES ASSUME UNCHANGED vars
             PROVE  /\ CanVote' <=> CanVote
                    /\ CanSelect' <=> CanSelect
                    /\ CanDispatch' <=> CanDispatch
                    /\ CanRespond' <=> CanRespond
                    /\ CanPropose' <=> CanPropose
                    /\ CanDecide' <=> CanDecide
                    /\ CanLearn' <=> CanLearn
                    /\ CanProcess' <=> CanProcess
  OBVIOUS
<1>0. /\ leader' = leader /\ votes' = votes /\ selected' = selected
      /\ dispatchers' = dispatchers /\ execResponse' = execResponse
      /\ proposed' = proposed /\ consensusLog' = consensusLog
      /\ learned' = learned /\ processed' = processed
  BY DEF vars
<1>1. CanVote' <=> CanVote
  BY <1>0 DEF CanVote, HasVoted
<1>2. CanSelect' <=> CanSelect
  BY <1>0 DEF CanSelect, AllVoted, HasVoted
<1>3. CanDispatch' <=> CanDispatch
  BY <1>0 DEF CanDispatch
<1>4. CanRespond' <=> CanRespond
  BY <1>0 DEF CanRespond
<1>5. CanPropose' <=> CanPropose
  BY <1>0 DEF CanPropose, ObservedItem
<1>6. CanDecide' <=> CanDecide
  BY <1>0 DEF CanDecide, LogRids
<1>7. CanLearn' <=> CanLearn
  BY <1>0 DEF CanLearn
<1>8. CanProcess' <=> CanProcess
  BY <1>0 DEF CanProcess
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8

LEMMA EventuallyDone ==
    ASSUME LivenessAssumptions
    PROVE  FairSpec => <>Done
<1>1. LiveState /\ ~Done => CanStep
  BY Progress
<1>2. /\ LiveState /\ CanVote => ENABLED <<SubmitVoteAction>>_vars
      /\ LiveState /\ CanSelect => ENABLED <<SelectAction>>_vars
      /\ LiveState /\ CanDispatch => ENABLED <<DispatchAction>>_vars
      /\ LiveState /\ CanRespond => ENABLED <<ExternalRespondAction>>_vars
      /\ LiveState /\ CanPropose => ENABLED <<ProposeResponseAction>>_vars
      /\ LiveState /\ CanDecide => ENABLED <<DecideAction>>_vars
      /\ LiveState /\ CanLearn => ENABLED <<LearnAction>>_vars
      /\ LiveState /\ CanProcess => ENABLED <<ProcessAction>>_vars
  BY EnabledVote, EnabledSelect, EnabledDispatch, EnabledRespond,
     EnabledPropose, EnabledDecide, EnabledLearn, EnabledProcess
<1>3. Spec => []LiveState
  BY LiveStateInvariant
<1>4. Spec => <>[][FALSE]_vars
  BY Termination
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, CanStable, PTL DEF FairSpec, CanStep

(***************************************************************************
Theorem 2 (Liveness), paper Section 5, in the form the TLC liveness
configuration checks.
***************************************************************************)
THEOREM Theorem2 ==
    ASSUME LivenessAssumptions
    PROVE  FairSpec => Completion
BY EventuallyDone DEF Completion, Done

(***************************************************************************
The same result in the paper's words: every replica eventually has a
delivered response for every request id. Completion speaks of the
deduplication state; SeenDelivered (ResdetDelivery.tla) says every
recorded request id has a delivered response.
***************************************************************************)
AllDelivered ==
    \A replica \in Replicas :
        \A request \in RequestIds :
            \E i \in 1..Len(delivered[replica]) :
                delivered[replica][i].rid = request

THEOREM Theorem2Delivered ==
    ASSUME LivenessAssumptions
    PROVE  FairSpec => <>AllDelivered
<1>1. LiveState /\ Done => AllDelivered
  BY DEF LiveState, DeliveryInv, SeenDelivered, Done, AllDelivered
<1>2. Spec => []LiveState
  BY LiveStateInvariant
<1> QED
  BY <1>1, <1>2, EventuallyDone, PTL DEF FairSpec
=============================================================================

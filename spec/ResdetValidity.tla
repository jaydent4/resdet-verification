--------------------------- MODULE ResdetValidity ---------------------------
(***************************************************************************
TLAPS proofs, part 4 of 5: validity and processing order.

Every delivered response was physically returned by the downstream service
to a replica that dispatched a selected request, then proposed, then
agreed (paper Section 4.2: responses do not bypass commitment). A replica
processes an index only after learning it and every index before it
(Lemma 2), and learns only agreed indexes.
***************************************************************************)
EXTENDS ResdetFold

(* Every agreed entry was proposed. This is ConsensusValidity without the
   FlattenBatches fold. *)
LogProposed ==
    \A s \in 1..Len(consensusLog) :
        \A k \in 1..Len(consensusLog[s]) :
            consensusLog[s][k] \in proposed

ValidityTypeOK ==
    /\ selected \in [RequestIds -> Payloads \union {NoValue}]
    /\ dispatchers \in [RequestIds -> SUBSET Replicas]
    /\ execResponse \in
        [RequestIds -> [Replicas -> Responses \union {NoValue}]]
    /\ observed \subseteq ResponseItems
    /\ proposed \subseteq ResponseItems
    /\ consensusLog \in Seq(Seq(ResponseItems))
    /\ learned \in [Replicas -> SUBSET Nat]
    /\ processed \in [Replicas -> Nat]
    /\ delivered \in [Replicas -> Seq(ResponseItems)]

(* A response recorded for a dispatching replica has been observed. *)
ExecObserved ==
    \A request \in RequestIds, replica \in Replicas :
        execResponse[request][replica] # NoValue =>
            ObservedItem(request, execResponse[request][replica])
                \in observed

(* Every delivered entry is an agreed entry at a processed position. *)
DeliveredFromLog ==
    \A r \in Replicas :
        \A i \in 1..Len(delivered[r]) :
            \E s \in 1..processed[r] :
                \E k \in 1..Len(consensusLog[s]) :
                    delivered[r][i] = consensusLog[s][k]

ValidityInv ==
    /\ ValidityTypeOK
    /\ LogProposed
    /\ ProposalValidity
    /\ ExecObserved
    /\ ObservedHasPhysicalExecution
    /\ NoDispatchBeforeSelection
    /\ DeliveredFromLog
    /\ ProcessedPrefixLearned
    /\ LearnedOnlyDecided
    /\ ProcessedWithinLog

(* The variables ValidityInv reads. *)
ValidityVars ==
    <<selected, dispatchers, execResponse, observed, proposed,
      consensusLog, learned, processed, delivered>>

THEOREM ValidityInit == Init => ValidityInv
<1> SUFFICES ASSUME Init PROVE ValidityInv
  OBVIOUS
<1>1. ValidityTypeOK
  BY DEF Init, ValidityTypeOK
<1>2. LogProposed
  BY DEF Init, LogProposed
<1>3. ProposalValidity /\ ObservedHasPhysicalExecution
  BY DEF Init, ProposalValidity, ObservedHasPhysicalExecution
<1>4. ExecObserved
  BY DEF Init, ExecObserved
<1>5. NoDispatchBeforeSelection
  BY DEF Init, NoDispatchBeforeSelection
<1>6. DeliveredFromLog
  BY DEF Init, DeliveredFromLog
<1>7. ProcessedPrefixLearned /\ LearnedOnlyDecided /\ ProcessedWithinLog
  BY DEF Init, ProcessedPrefixLearned, LearnedOnlyDecided,
         ProcessedWithinLog
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF ValidityInv

LEMMA ValidityUnchanged ==
    ASSUME ValidityInv, UNCHANGED ValidityVars
    PROVE  ValidityInv'
BY DEF ValidityVars, ValidityInv, ValidityTypeOK, LogProposed,
       ProposalValidity, ExecObserved, ObservedHasPhysicalExecution,
       NoDispatchBeforeSelection, DeliveredFromLog,
       ProcessedPrefixLearned, LearnedOnlyDecided, ProcessedWithinLog,
       ObservedItem

LEMMA EligibleProposed == EligibleProposalItems \subseteq proposed
BY DEF EligibleProposalItems, UndecidedProposals

THEOREM ValidityStep ==
    ASSUME StrictDelivery
    PROVE  ValidityInv /\ [Next]_vars => ValidityInv'
<1> SUFFICES ASSUME ValidityInv, [Next]_vars PROVE ValidityInv'
  OBVIOUS
<1>inv. /\ ValidityTypeOK
        /\ LogProposed
        /\ ProposalValidity
        /\ ExecObserved
        /\ ObservedHasPhysicalExecution
        /\ NoDispatchBeforeSelection
        /\ DeliveredFromLog
        /\ ProcessedPrefixLearned
        /\ LearnedOnlyDecided
        /\ ProcessedWithinLog
  BY DEF ValidityInv
<1>1. CASE SubmitVoteAction
  BY <1>1, ValidityUnchanged DEF SubmitVoteAction, SubmitVote, ValidityVars
<1>2. CASE SelectAction
  <2>1. PICK request \in RequestIds, payload \in Payloads :
            /\ selected' = [selected EXCEPT ![request] = payload]
            /\ UNCHANGED <<dispatchers, execResponse, observed, proposed,
                           consensusLog, learned, processed, delivered>>
    BY <1>2 DEF SelectAction, SelectByQuorum, TimeoutSelect
  <2>2. ValidityTypeOK'
    BY <2>1, <1>inv DEF ValidityTypeOK
  <2>3. NoDispatchBeforeSelection'
    BY <2>1, <1>inv, ConstantAssumptions
       DEF NoDispatchBeforeSelection, ValidityTypeOK
  <2>4. /\ LogProposed'
        /\ ProposalValidity'
        /\ ExecObserved'
        /\ ObservedHasPhysicalExecution'
        /\ DeliveredFromLog'
    BY <2>1, <1>inv DEF LogProposed, ProposalValidity, ExecObserved,
                        ObservedHasPhysicalExecution, DeliveredFromLog,
                        ObservedItem
  <2>5. /\ ProcessedPrefixLearned'
        /\ LearnedOnlyDecided'
        /\ ProcessedWithinLog'
    BY <2>1, <1>inv DEF ProcessedPrefixLearned, LearnedOnlyDecided,
                        ProcessedWithinLog
  <2> QED
    BY <2>2, <2>3, <2>4, <2>5 DEF ValidityInv
<1>3. CASE DispatchAction
  <2>1. PICK replica \in Replicas, request \in RequestIds :
            /\ selected[request] # NoValue
            /\ dispatchers' = [dispatchers EXCEPT
                                 ![request] = @ \union {replica}]
            /\ UNCHANGED <<selected, execResponse, observed, proposed,
                           consensusLog, learned, processed, delivered>>
    BY <1>3 DEF DispatchAction, Dispatch
  <2>2. ValidityTypeOK'
    BY <2>1, <1>inv DEF ValidityTypeOK
  <2>3. NoDispatchBeforeSelection'
    BY <2>1, <1>inv DEF NoDispatchBeforeSelection, ValidityTypeOK
  <2>4. ObservedHasPhysicalExecution'
    <3> SUFFICES ASSUME NEW item \in observed'
                 PROVE  \E replica2 \in dispatchers'[item.rid] :
                            execResponse'[item.rid][replica2] = item.value
      BY DEF ObservedHasPhysicalExecution
    <3>1. item \in observed /\ item.rid \in RequestIds
      BY <2>1, <1>inv DEF ValidityTypeOK, ResponseItems
    <3>2. PICK replica2 \in dispatchers[item.rid] :
              execResponse[item.rid][replica2] = item.value
      BY <3>1, <1>inv DEF ObservedHasPhysicalExecution
    <3>3. replica2 \in dispatchers'[item.rid]
      BY <2>1, <3>1, <3>2, <1>inv DEF ValidityTypeOK
    <3> QED
      BY <2>1, <3>2, <3>3
  <2>5. /\ LogProposed'
        /\ ProposalValidity'
        /\ ExecObserved'
        /\ DeliveredFromLog'
    BY <2>1, <1>inv DEF LogProposed, ProposalValidity, ExecObserved,
                        DeliveredFromLog, ObservedItem
  <2>6. /\ ProcessedPrefixLearned'
        /\ LearnedOnlyDecided'
        /\ ProcessedWithinLog'
    BY <2>1, <1>inv DEF ProcessedPrefixLearned, LearnedOnlyDecided,
                        ProcessedWithinLog
  <2> QED
    BY <2>2, <2>3, <2>4, <2>5, <2>6 DEF ValidityInv
<1>4. CASE ExternalRespondAction
  <2>1. PICK replica \in Replicas,
             request \in RequestIds,
             responseValue \in Responses :
            /\ replica \in dispatchers[request]
            /\ execResponse[request][replica] = NoValue
            /\ execResponse' = [execResponse EXCEPT
                                  ![request][replica] = responseValue]
            /\ observed' =
                observed \union {ObservedItem(request, responseValue)}
            /\ UNCHANGED <<selected, dispatchers, proposed, consensusLog,
                           learned, processed, delivered>>
    BY <1>4 DEF ExternalRespondAction, ExternalRespond
  <2>2. ValidityTypeOK'
    BY <2>1, <1>inv DEF ValidityTypeOK, ObservedItem, ResponseItems
  <2>3. ProposalValidity'
    BY <2>1, <1>inv DEF ProposalValidity
  <2>4. ExecObserved'
    <3> SUFFICES ASSUME NEW request2 \in RequestIds,
                        NEW replica2 \in Replicas,
                        execResponse'[request2][replica2] # NoValue
                 PROVE  ObservedItem(
                            request2, execResponse'[request2][replica2])
                            \in observed'
      BY DEF ExecObserved
    <3>1. CASE request2 = request /\ replica2 = replica
      <4>1. execResponse'[request2][replica2] = responseValue
        BY <2>1, <3>1, <1>inv DEF ValidityTypeOK
      <4> QED
        BY <2>1, <3>1, <4>1
    <3>2. CASE ~(request2 = request /\ replica2 = replica)
      <4>1. execResponse'[request2][replica2] =
                execResponse[request2][replica2]
        BY <2>1, <3>2, <1>inv DEF ValidityTypeOK
      <4> QED
        BY <2>1, <4>1, <1>inv DEF ExecObserved
    <3> QED
      BY <3>1, <3>2
  <2>5. ObservedHasPhysicalExecution'
    <3> SUFFICES ASSUME NEW item \in observed'
                 PROVE  \E replica2 \in dispatchers'[item.rid] :
                            execResponse'[item.rid][replica2] = item.value
      BY DEF ObservedHasPhysicalExecution
    <3>1. CASE item = ObservedItem(request, responseValue)
      <4>1. item.rid = request /\ item.value = responseValue
        BY <3>1 DEF ObservedItem
      <4>2. execResponse'[request][replica] = responseValue
        BY <2>1, <1>inv DEF ValidityTypeOK
      <4> QED
        BY <2>1, <4>1, <4>2
    <3>2. CASE item \in observed
      <4>1. item.rid \in RequestIds /\ item.value \in Responses
        BY <3>2, <1>inv DEF ValidityTypeOK, ResponseItems
      <4>2. PICK replica2 \in dispatchers[item.rid] :
                execResponse[item.rid][replica2] = item.value
        BY <3>2, <1>inv DEF ObservedHasPhysicalExecution
      <4>3. replica2 \in Replicas
        BY <4>1, <4>2, <1>inv DEF ValidityTypeOK
      <4>4. ~(item.rid = request /\ replica2 = replica)
        BY <2>1, <4>1, <4>2, ConstantAssumptions
      <4>5. execResponse'[item.rid][replica2] =
                execResponse[item.rid][replica2]
        BY <2>1, <4>1, <4>3, <4>4, <1>inv DEF ValidityTypeOK
      <4> QED
        BY <2>1, <4>2, <4>5
    <3> QED
      BY <2>1, <3>1, <3>2
  <2>6. /\ LogProposed'
        /\ NoDispatchBeforeSelection'
        /\ DeliveredFromLog'
    BY <2>1, <1>inv DEF LogProposed, NoDispatchBeforeSelection,
                        DeliveredFromLog
  <2>7. /\ ProcessedPrefixLearned'
        /\ LearnedOnlyDecided'
        /\ ProcessedWithinLog'
    BY <2>1, <1>inv DEF ProcessedPrefixLearned, LearnedOnlyDecided,
                        ProcessedWithinLog
  <2> QED
    BY <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF ValidityInv
<1>5. CASE ProposeResponseAction
  <2>1. PICK replica \in Replicas,
             request \in RequestIds,
             responseValue \in Responses :
            /\ execResponse[request][replica] = responseValue
            /\ proposed' =
                proposed \union {ObservedItem(request, responseValue)}
            /\ UNCHANGED <<selected, dispatchers, execResponse, observed,
                           consensusLog, learned, processed, delivered>>
    BY <1>5 DEF ProposeResponseAction, ProposeResponse
  <2>2. ObservedItem(request, responseValue) \in observed
    BY <2>1, <1>inv, ConstantAssumptions DEF ExecObserved
  <2>3. ValidityTypeOK'
    BY <2>1, <1>inv DEF ValidityTypeOK, ObservedItem, ResponseItems
  <2>4. ProposalValidity'
    BY <2>1, <2>2, <1>inv DEF ProposalValidity
  <2>5. LogProposed'
    BY <2>1, <1>inv DEF LogProposed
  <2>6. /\ ExecObserved'
        /\ ObservedHasPhysicalExecution'
        /\ NoDispatchBeforeSelection'
        /\ DeliveredFromLog'
    BY <2>1, <1>inv DEF ExecObserved, ObservedHasPhysicalExecution,
                        NoDispatchBeforeSelection, DeliveredFromLog,
                        ObservedItem
  <2>7. /\ ProcessedPrefixLearned'
        /\ LearnedOnlyDecided'
        /\ ProcessedWithinLog'
    BY <2>1, <1>inv DEF ProcessedPrefixLearned, LearnedOnlyDecided,
                        ProcessedWithinLog
  <2> QED
    BY <2>3, <2>4, <2>5, <2>6, <2>7 DEF ValidityInv
<1>6. CASE DecideAction
  <2>1. PICK batch \in Seq(ResponseItems) :
            /\ \A k \in 1..Len(batch) : batch[k] \in proposed
            /\ consensusLog' = Append(consensusLog, batch)
            /\ UNCHANGED <<selected, dispatchers, execResponse, observed,
                           proposed, learned, processed, delivered>>
    <3>1. CASE \E item \in ResponseItems : DecideOne(item)
      <4>1. PICK item \in ResponseItems : DecideOne(item)
        BY <3>1
      <4>2. <<item>> \in Seq(ResponseItems)
        OBVIOUS
      <4>3. \A k \in 1..Len(<<item>>) : <<item>>[k] \in proposed
        BY <4>1, EligibleProposed DEF DecideOne
      <4> QED
        BY <4>1, <4>2, <4>3 DEF DecideOne
    <3>2. CASE \E first \in ResponseItems, second \in ResponseItems :
                  DecidePair(first, second)
      <4>1. PICK first \in ResponseItems, second \in ResponseItems :
                DecidePair(first, second)
        BY <3>2
      <4>2. <<first, second>> \in Seq(ResponseItems)
        OBVIOUS
      <4>3. \A k \in 1..Len(<<first, second>>) :
                <<first, second>>[k] \in proposed
        BY <4>1, EligibleProposed DEF DecidePair
      <4> QED
        BY <4>1, <4>2, <4>3 DEF DecidePair
    <3> QED
      BY <1>6, <3>1, <3>2 DEF DecideAction
  <2>2. /\ Len(consensusLog') = Len(consensusLog) + 1
        /\ \A s \in 1..Len(consensusLog) : consensusLog'[s] = consensusLog[s]
        /\ consensusLog'[Len(consensusLog) + 1] = batch
        /\ Len(consensusLog) \in Nat
    BY <2>1, <1>inv DEF ValidityTypeOK
  <2>3. ValidityTypeOK'
    BY <2>1, <1>inv DEF ValidityTypeOK
  <2>4. LogProposed'
    <3> SUFFICES ASSUME NEW s \in 1..Len(consensusLog'),
                        NEW k \in 1..Len(consensusLog'[s])
                 PROVE  consensusLog'[s][k] \in proposed'
      BY DEF LogProposed
    <3>1. CASE s \in 1..Len(consensusLog)
      BY <3>1, <2>1, <2>2, <1>inv DEF LogProposed
    <3>2. CASE s = Len(consensusLog) + 1
      BY <3>2, <2>1, <2>2
    <3> QED
      BY <3>1, <3>2, <2>2
  <2>5. DeliveredFromLog'
    <3> SUFFICES ASSUME NEW r \in Replicas,
                        NEW i \in 1..Len(delivered'[r])
                 PROVE  \E s \in 1..processed'[r] :
                            \E k \in 1..Len(consensusLog'[s]) :
                                delivered'[r][i] = consensusLog'[s][k]
      BY DEF DeliveredFromLog
    <3>1. PICK s \in 1..processed[r] :
              \E k \in 1..Len(consensusLog[s]) :
                  delivered[r][i] = consensusLog[s][k]
      BY <2>1, <1>inv DEF DeliveredFromLog
    <3>2. s \in 1..Len(consensusLog)
      BY <3>1, <2>2, <1>inv DEF ProcessedWithinLog, ValidityTypeOK
    <3> QED
      BY <2>1, <2>2, <3>1, <3>2
  <2>6. /\ ProposalValidity'
        /\ ExecObserved'
        /\ ObservedHasPhysicalExecution'
        /\ NoDispatchBeforeSelection'
    BY <2>1, <1>inv DEF ProposalValidity, ExecObserved,
                        ObservedHasPhysicalExecution,
                        NoDispatchBeforeSelection, ObservedItem
  <2>7. /\ ProcessedPrefixLearned'
        /\ LearnedOnlyDecided'
        /\ ProcessedWithinLog'
    BY <2>1, <2>2, <1>inv DEF ProcessedPrefixLearned, LearnedOnlyDecided,
                               ProcessedWithinLog, ValidityTypeOK
  <2> QED
    BY <2>3, <2>4, <2>5, <2>6, <2>7 DEF ValidityInv
<1>7. CASE LearnAction
  <2>1. PICK replica \in Replicas, slot \in 1..Len(consensusLog) :
            /\ learned' = [learned EXCEPT ![replica] = @ \union {slot}]
            /\ UNCHANGED <<selected, dispatchers, execResponse, observed,
                           proposed, consensusLog, processed, delivered>>
    BY <1>7 DEF LearnAction, LearnSlot
  <2>2. Len(consensusLog) \in Nat
    BY <1>inv DEF ValidityTypeOK
  <2>3. ValidityTypeOK'
    BY <2>1, <2>2, <1>inv DEF ValidityTypeOK
  <2>4. /\ ProcessedPrefixLearned'
        /\ LearnedOnlyDecided'
        /\ ProcessedWithinLog'
    BY <2>1, <2>2, <1>inv DEF ProcessedPrefixLearned, LearnedOnlyDecided,
                               ProcessedWithinLog, ValidityTypeOK
  <2>5. /\ LogProposed'
        /\ ProposalValidity'
        /\ ExecObserved'
        /\ ObservedHasPhysicalExecution'
        /\ NoDispatchBeforeSelection'
        /\ DeliveredFromLog'
    BY <2>1, <1>inv DEF LogProposed, ProposalValidity, ExecObserved,
                        ObservedHasPhysicalExecution,
                        NoDispatchBeforeSelection, DeliveredFromLog,
                        ObservedItem
  <2> QED
    BY <2>3, <2>4, <2>5 DEF ValidityInv
<1>8. CASE ProcessAction
  <2>1. PICK replica \in Replicas : ProcessContiguous(replica)
    BY <1>8 DEF ProcessAction
  <2> DEFINE slot == processed[replica] + 1
             items == consensusLog[slot]
             out == delivered[replica]
             result == ApplyItems(items, seen[replica], out)
  <2>2. /\ slot \in 1..Len(consensusLog)
        /\ slot \in learned[replica]
        /\ processed' = [processed EXCEPT ![replica] = slot]
        /\ delivered' = [delivered EXCEPT ![replica] = result.output]
        /\ UNCHANGED <<selected, dispatchers, execResponse, observed,
                       proposed, consensusLog, learned>>
    BY <2>1 DEF ProcessContiguous
  <2>3. /\ items \in Seq(ResponseItems)
        /\ out \in Seq(ResponseItems)
        /\ processed[replica] \in Nat
        /\ slot \in Nat
        /\ Len(consensusLog) \in Nat
    BY <2>2, <1>inv DEF ValidityTypeOK
  <2>4. AppliedCorrectly(ResponseItems, items, seen[replica], out, result)
    BY <2>3, ApplyItemsCorrect DEF StrictDelivery
  <2> HIDE DEF result
  <2>5. /\ result.output \in Seq(ResponseItems)
        /\ Len(out) <= Len(result.output)
        /\ \A i \in 1..Len(out) : result.output[i] = out[i]
        /\ \A i \in (Len(out) + 1)..Len(result.output) :
             \E k \in 1..Len(items) : result.output[i] = items[k]
    BY <2>4 DEF AppliedCorrectly
  <2>6. ValidityTypeOK'
    BY <2>2, <2>3, <2>5, <1>inv DEF ValidityTypeOK
  <2>7. DeliveredFromLog'
    <3> SUFFICES ASSUME NEW r \in Replicas,
                        NEW i \in 1..Len(delivered'[r])
                 PROVE  \E s \in 1..processed'[r] :
                            \E k \in 1..Len(consensusLog'[s]) :
                                delivered'[r][i] = consensusLog'[s][k]
      BY DEF DeliveredFromLog
    <3>1. CASE r # replica
      <4>1. delivered'[r] = delivered[r] /\ processed'[r] = processed[r]
        BY <3>1, <2>2, <1>inv DEF ValidityTypeOK
      <4> QED
        BY <4>1, <2>2, <1>inv DEF DeliveredFromLog
    <3>2. CASE r = replica
      <4>1. delivered'[r] = result.output /\ processed'[r] = slot
        BY <3>2, <2>2, <1>inv DEF ValidityTypeOK
      <4>2. Len(out) \in Nat /\ Len(result.output) \in Nat
        BY <2>3, <2>5
      <4>3. CASE i \in 1..Len(out)
        <5>1. delivered'[r][i] = out[i]
          BY <4>1, <4>3, <2>5
        <5>2. PICK s \in 1..processed[replica] :
                  \E k \in 1..Len(consensusLog[s]) :
                      out[i] = consensusLog[s][k]
          BY <4>3, <1>inv DEF DeliveredFromLog
        <5>3. s \in 1..slot
          BY <5>2, <2>3
        <5> QED
          BY <5>1, <5>2, <5>3, <4>1, <2>2
      <4>4. CASE i \in (Len(out) + 1)..Len(result.output)
        <5>1. PICK k \in 1..Len(items) : result.output[i] = items[k]
          BY <4>4, <2>5
        <5>2. slot \in 1..slot
          BY <2>3, <2>2
        <5> QED
          BY <5>1, <5>2, <4>1, <2>2
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4
    <3> QED
      BY <3>1, <3>2
  <2>8. ProcessedPrefixLearned'
    <3> SUFFICES ASSUME NEW r \in Replicas
                 PROVE  (1..processed'[r]) \subseteq learned'[r]
      BY DEF ProcessedPrefixLearned
    <3>1. CASE r # replica
      BY <3>1, <2>2, <1>inv DEF ProcessedPrefixLearned, ValidityTypeOK
    <3>2. CASE r = replica
      <4>1. processed'[r] = slot /\ learned'[r] = learned[replica]
        BY <3>2, <2>2, <1>inv DEF ValidityTypeOK
      <4>2. (1..processed[replica]) \subseteq learned[replica]
        BY <1>inv DEF ProcessedPrefixLearned
      <4> QED
        BY <4>1, <4>2, <2>2, <2>3
    <3> QED
      BY <3>1, <3>2
  <2>9. LearnedOnlyDecided' /\ ProcessedWithinLog'
    BY <2>2, <2>3, <1>inv DEF LearnedOnlyDecided, ProcessedWithinLog,
                               ValidityTypeOK
  <2>10. /\ LogProposed'
         /\ ProposalValidity'
         /\ ExecObserved'
         /\ ObservedHasPhysicalExecution'
         /\ NoDispatchBeforeSelection'
    BY <2>2, <1>inv DEF LogProposed, ProposalValidity, ExecObserved,
                        ObservedHasPhysicalExecution,
                        NoDispatchBeforeSelection, ObservedItem
  <2> QED
    BY <2>6, <2>7, <2>8, <2>9, <2>10 DEF ValidityInv
<1>9. CASE \E replica \in Replicas, slot \in 1..MaxSlots :
              ProcessNonContiguous(replica, slot)
  BY <1>9 DEF ProcessNonContiguous, StrictDelivery
<1>10. CASE \E replica \in Replicas, item \in ResponseItems :
               DeliverBeforeConsensus(replica, item)
  BY <1>10 DEF DeliverBeforeConsensus, StrictDelivery
<1>11. CASE \E replica \in Replicas : Crash(replica)
  BY <1>11, ValidityUnchanged DEF Crash, ValidityVars
<1>12. CASE \E replica \in Replicas : Recover(replica)
  BY <1>12, ValidityUnchanged DEF Recover, ValidityVars
<1>13. CASE \E replica \in Replicas : Elect(replica)
  BY <1>13, ValidityUnchanged DEF Elect, ValidityVars
<1>14. CASE \E replica \in Replicas,
               request \in RequestIds,
               payload \in Payloads :
               NoLeaderDispatch(replica, request, payload)
  BY <1>14 DEF NoLeaderDispatch, StrictDelivery
<1>15. CASE \E replica \in Replicas,
               request \in RequestIds,
               responseValue \in Responses :
               DirectNoLeaderRespond(replica, request, responseValue)
  BY <1>15 DEF DirectNoLeaderRespond, StrictDelivery
<1>16. CASE UNCHANGED vars
  BY <1>16, ValidityUnchanged DEF vars, ValidityVars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11,
     <1>12, <1>13, <1>14, <1>15, <1>16 DEF Next

THEOREM ValidityInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []ValidityInv
<1>1. Init => ValidityInv
  BY ValidityInit
<1>2. ValidityInv /\ [Next]_vars => ValidityInv'
  BY ValidityStep
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM ProposalChainInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => [](/\ LogProposed
                      /\ ProposalValidity
                      /\ ObservedHasPhysicalExecution
                      /\ NoDispatchBeforeSelection)
<1>1. ValidityInv => /\ LogProposed
                     /\ ProposalValidity
                     /\ ObservedHasPhysicalExecution
                     /\ NoDispatchBeforeSelection
  BY DEF ValidityInv
<1> QED
  BY <1>1, ValidityInvariant, PTL

LEMMA ValidityImpliesResponseValidity == ValidityInv => ResponseValidity
<1> SUFFICES ASSUME ValidityInv,
                    NEW replica \in Replicas,
                    NEW index \in 1..Len(delivered[replica])
             PROVE  /\ delivered[replica][index] \in observed
                    /\ selected[delivered[replica][index].rid] # NoValue
  BY DEF ResponseValidity
<1> DEFINE item == delivered[replica][index]
<1>1. PICK s \in 1..processed[replica] :
          \E k \in 1..Len(consensusLog[s]) : item = consensusLog[s][k]
  BY DEF ValidityInv, DeliveredFromLog
<1>2. s \in 1..Len(consensusLog)
  BY <1>1 DEF ValidityInv, ProcessedWithinLog, ValidityTypeOK
<1>3. item \in proposed
  BY <1>1, <1>2 DEF ValidityInv, LogProposed
<1>4. item \in observed
  BY <1>3 DEF ValidityInv, ProposalValidity
<1>5. item.rid \in RequestIds
  BY <1>4 DEF ValidityInv, ValidityTypeOK, ResponseItems
<1>6. dispatchers[item.rid] # {}
  BY <1>4 DEF ValidityInv, ObservedHasPhysicalExecution
<1>7. selected[item.rid] # NoValue
  BY <1>5, <1>6 DEF ValidityInv, NoDispatchBeforeSelection
<1> QED
  BY <1>4, <1>7

THEOREM ResponseValidityInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []ResponseValidity
BY ValidityImpliesResponseValidity, ValidityInvariant, PTL

THEOREM ProcessingOrderInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => [](/\ ProcessedPrefixLearned
                      /\ LearnedOnlyDecided
                      /\ ProcessedWithinLog)
<1>1. ValidityInv => /\ ProcessedPrefixLearned
                     /\ LearnedOnlyDecided
                     /\ ProcessedWithinLog
  BY DEF ValidityInv
<1> QED
  BY <1>1, ValidityInvariant, PTL

(***************************************************************************
The TLC invariant ConsensusValidity reads the log through the
FlattenBatches fold. FlattenBatchesItems unfolds that fold: every entry of
the flattened log is an entry of some agreed batch. ConsensusValidity then
follows from LogProposed.
***************************************************************************)
LEMMA FlattenBatchesItems ==
    ASSUME NEW S, NEW log \in Seq(Seq(S))
    PROVE  LET items == FlattenBatches(log)
           IN  /\ items \in Seq(S)
               /\ \A index \in 1..Len(items) :
                    \E s \in 1..Len(log) :
                        \E k \in 1..Len(log[s]) :
                            items[index] = log[s][k]
<1> DEFINE f == CHOOSE g : g = [i \in 0..Len(log) |->
                                    IF i = 0
                                    THEN <<>>
                                    ELSE g[i - 1] \o log[i]]
<1>1. Len(log) \in Nat
  OBVIOUS
<1>2. FiniteNatInductiveDefHypothesis(
          f, <<>>, LAMBDA v, i : v \o log[i], 0, Len(log))
  BY DEF FiniteNatInductiveDefHypothesis
<1>3. FiniteNatInductiveDefConclusion(
          f, <<>>, LAMBDA v, i : v \o log[i], 0, Len(log))
  <2> HIDE DEF f
  <2> QED
    BY <1>1, <1>2, FiniteNatInductiveDef
<1>4. f = [i \in 0..Len(log) |->
              IF i = 0 THEN <<>> ELSE f[i - 1] \o log[i]]
  BY <1>3 DEF FiniteNatInductiveDefConclusion
<1>5. FlattenBatches(log) = f[Len(log)]
  BY DEF FlattenBatches
<1> HIDE DEF f
<1> DEFINE P(n) ==
        n \in 0..Len(log) =>
            /\ f[n] \in Seq(S)
            /\ \A index \in 1..Len(f[n]) :
                 \E s \in 1..n :
                    \E k \in 1..Len(log[s]) : f[n][index] = log[s][k]
<1>6. P(0)
  BY <1>1, <1>4
<1>7. \A n \in Nat : P(n) => P(n + 1)
  <2> SUFFICES ASSUME NEW n \in Nat, P(n), n + 1 \in 0..Len(log)
               PROVE  /\ f[n + 1] \in Seq(S)
                      /\ \A index \in 1..Len(f[n + 1]) :
                           \E s \in 1..(n + 1) :
                              \E k \in 1..Len(log[s]) :
                                  f[n + 1][index] = log[s][k]
    OBVIOUS
  <2>1. n \in 0..Len(log)
    BY <1>1
  <2>2. f[n + 1] = f[n] \o log[n + 1]
    BY <1>1, <1>4
  <2>3. log[n + 1] \in Seq(S)
    BY <1>1
  <2>4. /\ f[n] \in Seq(S)
        /\ \A index \in 1..Len(f[n]) :
             \E s \in 1..n :
                \E k \in 1..Len(log[s]) : f[n][index] = log[s][k]
    BY <2>1
  <2>5. f[n + 1] \in Seq(S)
    BY <2>2, <2>3, <2>4
  <2>6. ASSUME NEW index \in 1..Len(f[n + 1])
        PROVE  \E s \in 1..(n + 1) :
                  \E k \in 1..Len(log[s]) : f[n + 1][index] = log[s][k]
    <3>1. Len(f[n + 1]) = Len(f[n]) + Len(log[n + 1])
      BY <2>2, <2>3, <2>4
    <3>2. CASE index <= Len(f[n])
      <4>1. f[n + 1][index] = f[n][index]
        BY <3>2, <2>2, <2>3, <2>4
      <4>2. PICK s \in 1..n :
                \E k \in 1..Len(log[s]) : f[n][index] = log[s][k]
        BY <3>2, <2>4
      <4>3. s \in 1..(n + 1)
        OBVIOUS
      <4> QED
        BY <4>1, <4>2, <4>3
    <3>3. CASE index > Len(f[n])
      <4>1. /\ index - Len(f[n]) \in 1..Len(log[n + 1])
            /\ f[n + 1][index] = log[n + 1][index - Len(f[n])]
        BY <3>3, <3>1, <2>2, <2>3, <2>4
      <4>2. n + 1 \in 1..(n + 1)
        OBVIOUS
      <4> QED
        BY <4>1, <4>2
    <3> QED
      BY <3>2, <3>3, <2>4
  <2> QED
    BY <2>5, <2>6
<1>8. \A n \in Nat : P(n)
  <2> HIDE DEF P
  <2> QED
    BY <1>6, <1>7, NatInduction
<1>9. P(Len(log))
  BY <1>1, <1>8
<1> QED
  BY <1>1, <1>5, <1>9

LEMMA ValidityImpliesConsensusValidity == ValidityInv => ConsensusValidity
<1> SUFFICES ASSUME ValidityInv PROVE ConsensusItems \subseteq proposed
  BY DEF ConsensusValidity
<1> DEFINE items == FlattenBatches(consensusLog)
<1>1. consensusLog \in Seq(Seq(ResponseItems))
  BY DEF ValidityInv, ValidityTypeOK
<1>2. \A index \in 1..Len(items) :
          \E s \in 1..Len(consensusLog) :
              \E k \in 1..Len(consensusLog[s]) :
                  items[index] = consensusLog[s][k]
  BY <1>1, FlattenBatchesItems
<1>3. \A index \in 1..Len(items) : items[index] \in proposed
  BY <1>2 DEF ValidityInv, LogProposed
<1> QED
  BY <1>3 DEF ConsensusItems

THEOREM ConsensusValidityInvariant ==
    ASSUME StrictDelivery
    PROVE  Spec => []ConsensusValidity
BY ValidityImpliesConsensusValidity, ValidityInvariant, PTL
=============================================================================

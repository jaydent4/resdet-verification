---------------------------- MODULE ResdetLiveInv ----------------------------
(***************************************************************************
TLAPS liveness proof, part 1 of 5: assumptions, the invariant, and the
enabling conditions that the rest of the proof of Theorem 2 is stated in.

Theorem 2 of the paper says every submitted request is eventually
delivered at every non-faulty replica. The statement proved here is its
crash-stop form for this model: once a leader is stable and the replicas
in a set U stay up, every replica in U eventually delivers a response for
every request id. Replicas outside U may crash, recover, and crash again
forever, and leaders may change any number of times before the stable one.

  CrashStopLiveness ==
      FairSpec => (<>[]StableOn(U) => <>DoneOn(U))      (ResdetLiveness.tla)

Completion under FairSpec, the property the TLC liveness configuration
checks, is the special case with no crashes and U = Replicas.
***************************************************************************)
EXTENDS ResdetTheorems

(***************************************************************************
Conditions on the constants. They are sufficient, not necessary.

  StrictDelivery              The strict protocol (see ResdetFold.tla).
  ~MutantAllDispatch,
  ~MutantNoQuorum             The remaining TLC mutants are off.
  PrioritizeUniqueDecisions,
  MaxSlots >= |RequestIds|    The log is bounded by MaxSlots. Consensus
                              gives each not-yet-agreed request a slot
                              before any retry, and there are enough slots
                              for every request. This plays the role of
                              CG3(2) but has no counterpart in the paper:
                              it restricts which entries consensus may
                              agree, not only that it eventually agrees.
  finite Replicas, RequestIds Needed to count outstanding work.

EnableCrashes is not constrained: crashes, recoveries and elections may
or may not be enabled.
***************************************************************************)
LivenessAssumptions ==
    /\ StrictDelivery
    /\ ~MutantAllDispatch
    /\ ~MutantNoQuorum
    /\ PrioritizeUniqueDecisions
    /\ IsFiniteSet(Replicas)
    /\ IsFiniteSet(RequestIds)
    /\ MaxSlots >= Cardinality(RequestIds)

(***************************************************************************
The submissions of the replicas in U are enough to select a request: one
invocation suffices (the paper's protocol), or the timeout fallback is on,
or all invocations carry the same payload (the paper's system model) and
U has a quorum.
***************************************************************************)
VotersSuffice(U) ==
    \/ Quorum = 1
    \/ EnableTimeoutFallback
    \/ /\ \E payload \in Payloads : Payloads = {payload}
       /\ Cardinality(U) >= Quorum

(* CG3(1) and non-faultiness, as a state predicate that the theorem
   assumes holds from some point on: there is a leader, and every replica
   in U is up. *)
StableOn(U) == leader # NoNode /\ U \subseteq up

(* Every replica in U has delivered a response for every request id. *)
DoneOn(U) == \A replica \in U : seen[replica] = RequestIds

(* Completion (Resdet.tla) is <>Done. *)
Done == DoneOn(Replicas)

(* Every variable except leader and up. Crash, Recover and Elect leave
   these unchanged; every other action changes at least one of them. *)
WorkVars ==
    <<votes, selected, selectedByFallback, dispatchers, execResponse,
      observed, proposed, consensusLog, learned, processed, delivered,
      seen, unauthorizedDispatch, earlyDelivery>>

(* The request ids that occur in the agreed log, by position. *)
LogRids ==
    {request \in RequestIds :
        \E s \in 1..Len(consensusLog) :
            \E k \in 1..Len(consensusLog[s]) :
                consensusLog[s][k].rid = request}

(* A known leader is up. *)
LeaderUp == leader # NoNode => leader \in up

(* Without crashes the initial leader stays and every replica stays up. *)
NoCrashStable == ~EnableCrashes => (leader # NoNode /\ up = Replicas)

(* Without crashes only the one leader ever dispatches. *)
SingleDispatcher ==
    ~EnableCrashes =>
        \A request \in RequestIds : dispatchers[request] \subseteq {leader}

(* Until every request is agreed, no slot has been spent on a retry. *)
SlotsCount ==
    \/ LogRids = RequestIds
    \/ Len(consensusLog) <= Cardinality(LogRids)

LiveInv ==
    /\ leader \in Replicas \union {NoNode}
    /\ up \subseteq Replicas
    /\ LeaderUp
    /\ NoCrashStable
    /\ SingleDispatcher
    /\ votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
    /\ seen \in [Replicas -> SUBSET RequestIds]
    /\ Len(consensusLog) <= MaxSlots
    /\ learned \in [Replicas -> SUBSET (1..MaxSlots)]
    /\ SlotsCount

(* Everything the liveness proof knows about a reachable state. *)
LiveState == LiveInv /\ ValidityInv /\ DeliveryInv

(***************************************************************************
Enabling conditions, one per fair action of FairSpec. Each is a state
predicate that reads only WorkVars and leader. In a reachable state where
StableOn(U) holds, each implies its action is enabled
(ResdetLiveEnabled.tla), and if DoneOn(U) does not hold then at least one
of them does (ResdetLiveProgress.tla). They mention only the leader and
the replicas in U, so what the other replicas do cannot disable them.
***************************************************************************)
CanVote(U) ==
    \E replica \in U, request \in RequestIds :
        ~HasVoted(replica, request)

CanSelect(U) ==
    \E request \in RequestIds :
        /\ selected[request] = NoValue
        /\ \A replica \in U : HasVoted(replica, request)

CanDispatch ==
    \E request \in RequestIds :
        selected[request] # NoValue /\ leader \notin dispatchers[request]

CanRespond ==
    \E request \in RequestIds :
        /\ leader \in dispatchers[request]
        /\ execResponse[request][leader] = NoValue

CanPropose ==
    \E request \in RequestIds :
        /\ leader \in dispatchers[request]
        /\ execResponse[request][leader] # NoValue
        /\ ObservedItem(request, execResponse[request][leader])
              \notin proposed

CanDecide ==
    /\ Len(consensusLog) < MaxSlots
    /\ \E item \in proposed : item.rid \notin LogRids

CanLearn(U) ==
    \E replica \in U :
        \E slot \in 1..Len(consensusLog) : slot \notin learned[replica]

CanProcess(U) ==
    \E replica \in U :
        /\ processed[replica] < Len(consensusLog)
        /\ processed[replica] + 1 \in learned[replica]

CanStep(U) ==
    \/ CanVote(U)
    \/ CanSelect(U)
    \/ CanDispatch
    \/ CanRespond
    \/ CanPropose
    \/ CanDecide
    \/ CanLearn(U)
    \/ CanProcess(U)

(***************************************************************************
Converse of FlattenBatchesItems (ResdetValidity.tla): every entry of every
batch occurs in the flattened log.
***************************************************************************)
LEMMA FlattenBatchesCovers ==
    ASSUME NEW S, NEW log \in Seq(Seq(S))
    PROVE  LET items == FlattenBatches(log)
           IN  \A s \in 1..Len(log) :
                  \A k \in 1..Len(log[s]) :
                      \E index \in 1..Len(items) : items[index] = log[s][k]
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
            /\ \A s \in 1..n :
                 \A k \in 1..Len(log[s]) :
                    \E index \in 1..Len(f[n]) : f[n][index] = log[s][k]
<1>6. P(0)
  BY <1>1, <1>4
<1>7. \A n \in Nat : P(n) => P(n + 1)
  <2> SUFFICES ASSUME NEW n \in Nat, P(n), n + 1 \in 0..Len(log)
               PROVE  /\ f[n + 1] \in Seq(S)
                      /\ \A s \in 1..(n + 1) :
                           \A k \in 1..Len(log[s]) :
                              \E index \in 1..Len(f[n + 1]) :
                                  f[n + 1][index] = log[s][k]
    OBVIOUS
  <2>1. n \in 0..Len(log)
    BY <1>1
  <2>2. f[n + 1] = f[n] \o log[n + 1]
    BY <1>1, <1>4
  <2>3. log[n + 1] \in Seq(S)
    BY <1>1
  <2>4. /\ f[n] \in Seq(S)
        /\ \A s \in 1..n :
             \A k \in 1..Len(log[s]) :
                \E index \in 1..Len(f[n]) : f[n][index] = log[s][k]
    BY <2>1
  <2>5. f[n + 1] \in Seq(S)
    BY <2>2, <2>3, <2>4
  <2>6. Len(f[n + 1]) = Len(f[n]) + Len(log[n + 1])
    BY <2>2, <2>3, <2>4
  <2>7. /\ Len(f[n]) \in Nat
        /\ Len(log[n + 1]) \in Nat
    BY <2>3, <2>4
  <2>8. ASSUME NEW s \in 1..(n + 1), NEW k \in 1..Len(log[s])
        PROVE  \E index \in 1..Len(f[n + 1]) : f[n + 1][index] = log[s][k]
    <3>1. CASE s <= n
      <4>1. s \in 1..n
        BY <3>1
      <4>2. PICK index \in 1..Len(f[n]) : f[n][index] = log[s][k]
        BY <4>1, <2>4
      <4>3. /\ index \in 1..Len(f[n + 1])
            /\ f[n + 1][index] = f[n][index]
        BY <2>2, <2>3, <2>4, <2>6, <2>7
      <4> QED
        BY <4>2, <4>3
    <3>2. CASE s = n + 1
      <4>1. k \in 1..Len(log[n + 1])
        BY <3>2
      <4>2. /\ Len(f[n]) + k \in 1..Len(f[n + 1])
            /\ f[n + 1][Len(f[n]) + k] = log[n + 1][k]
        BY <4>1, <2>2, <2>3, <2>4, <2>6, <2>7
      <4> QED
        BY <4>2, <3>2
    <3> QED
      BY <3>1, <3>2
  <2> QED
    BY <2>5, <2>8
<1>8. \A n \in Nat : P(n)
  <2> HIDE DEF P
  <2> QED
    BY <1>6, <1>7, NatInduction
<1>9. P(Len(log))
  BY <1>1, <1>8
<1> QED
  BY <1>1, <1>5, <1>9

(***************************************************************************
The action guards read the agreed request ids through the FlattenBatches
fold; LogRids names the same set by position.
***************************************************************************)
LEMMA DecidedIsLogRids ==
    ASSUME consensusLog \in Seq(Seq(ResponseItems))
    PROVE  DecidedRequestIds = LogRids
<1> DEFINE items == FlattenBatches(consensusLog)
<1>1. /\ items \in Seq(ResponseItems)
      /\ \A index \in 1..Len(items) :
           \E s \in 1..Len(consensusLog) :
              \E k \in 1..Len(consensusLog[s]) :
                  items[index] = consensusLog[s][k]
  BY FlattenBatchesItems
<1>2. \A s \in 1..Len(consensusLog) :
         \A k \in 1..Len(consensusLog[s]) :
            \E index \in 1..Len(items) : items[index] = consensusLog[s][k]
  BY FlattenBatchesCovers
<1>3. DecidedRequestIds = {items[index].rid : index \in 1..Len(items)}
  BY DEF DecidedRequestIds
<1>4. \A index \in 1..Len(items) : items[index].rid \in RequestIds
  BY <1>1 DEF ResponseItems
<1> HIDE DEF items
<1>5. ASSUME NEW x \in DecidedRequestIds
      PROVE  x \in LogRids
  <2>1. PICK index \in 1..Len(items) : x = items[index].rid
    BY <1>3
  <2>2. x \in RequestIds
    BY <2>1, <1>4
  <2>3. PICK s \in 1..Len(consensusLog) :
            \E k \in 1..Len(consensusLog[s]) :
                items[index] = consensusLog[s][k]
    BY <1>1
  <2> QED
    BY <2>1, <2>2, <2>3 DEF LogRids
<1>6. ASSUME NEW x \in LogRids
      PROVE  x \in DecidedRequestIds
  <2>1. PICK s \in 1..Len(consensusLog) :
            \E k \in 1..Len(consensusLog[s]) : consensusLog[s][k].rid = x
    BY DEF LogRids
  <2>2. PICK k \in 1..Len(consensusLog[s]) : consensusLog[s][k].rid = x
    BY <2>1
  <2>3. PICK index \in 1..Len(items) : items[index] = consensusLog[s][k]
    BY <1>2
  <2> QED
    BY <2>2, <2>3, <1>3
<1> QED
  BY <1>5, <1>6

(***************************************************************************
LiveInv is inductive relative to the safety invariants.
***************************************************************************)
THEOREM LiveInit == Init => LiveInv
<1> SUFFICES ASSUME Init PROVE LiveInv
  OBVIOUS
<1>1. /\ leader \in Replicas
      /\ up = Replicas
      /\ votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
      /\ seen \in [Replicas -> SUBSET RequestIds]
      /\ learned \in [Replicas -> SUBSET (1..MaxSlots)]
  BY DEF Init
<1>2. Len(consensusLog) = 0 /\ MaxSlots \in Nat
  BY ConstantAssumptions DEF Init
<1>3. leader # NoNode
  BY <1>1, ConstantAssumptions
<1>4. LeaderUp /\ NoCrashStable
  BY <1>1, <1>3 DEF LeaderUp, NoCrashStable
<1>5. SingleDispatcher
  BY DEF Init, SingleDispatcher
<1>6. LogRids = {}
  BY <1>2 DEF LogRids
<1>7. SlotsCount
  BY <1>2, <1>6, FS_EmptySet DEF SlotsCount
<1> QED
  BY <1>1, <1>2, <1>4, <1>5, <1>7 DEF LiveInv

(* Steps that touch none of the variables LiveInv constrains, other than
   votes and seen, whose types are supplied separately. *)
LEMMA LiveFrame ==
    ASSUME LiveInv,
           UNCHANGED <<leader, up, consensusLog, learned, dispatchers>>,
           votes' \in [RequestIds -> [Payloads -> SUBSET Replicas]],
           seen' \in [Replicas -> SUBSET RequestIds]
    PROVE  LiveInv'
BY DEF LiveInv, LeaderUp, NoCrashStable, SingleDispatcher, SlotsCount,
       LogRids

(* Crash, Recover and Elect: only leader and up change, and they stay
   well-formed. These steps happen only when crashes are enabled, which
   makes the two no-crash conjuncts hold trivially. *)
LEMMA LiveMembership ==
    ASSUME LiveInv,
           EnableCrashes,
           leader' \in Replicas \union {NoNode},
           up' \subseteq Replicas,
           leader' # NoNode => leader' \in up',
           UNCHANGED <<votes, seen, consensusLog, learned, dispatchers>>
    PROVE  LiveInv'
BY DEF LiveInv, LeaderUp, NoCrashStable, SingleDispatcher, SlotsCount,
       LogRids

(* Consensus agrees on one more batch whose first entry was eligible. *)
LEMMA LiveDecideSlots ==
    ASSUME PrioritizeUniqueDecisions,
           IsFiniteSet(RequestIds),
           consensusLog \in Seq(Seq(ResponseItems)),
           SlotsCount,
           NEW batch \in Seq(ResponseItems),
           Len(batch) >= 1,
           batch[1] \in EligibleProposalItems,
           consensusLog' = Append(consensusLog, batch)
    PROVE  SlotsCount'
<1> DEFINE n == Len(consensusLog)
<1>1. /\ n \in Nat
      /\ Len(consensusLog') = n + 1
      /\ consensusLog'[n + 1] = batch
      /\ \A s \in 1..n : consensusLog'[s] = consensusLog[s]
  OBVIOUS
<1>2. LogRids' =
        {request \in RequestIds :
            \E s \in 1..Len(consensusLog') :
                \E k \in 1..Len(consensusLog'[s]) :
                    consensusLog'[s][k].rid = request}
  BY DEF LogRids
<1>3. LogRids \subseteq LogRids'
  <2> SUFFICES ASSUME NEW x \in LogRids PROVE x \in LogRids'
    OBVIOUS
  <2>1. x \in RequestIds
    BY DEF LogRids
  <2>2. PICK s \in 1..n :
            \E k \in 1..Len(consensusLog[s]) : consensusLog[s][k].rid = x
    BY DEF LogRids
  <2>3. PICK k \in 1..Len(consensusLog[s]) : consensusLog[s][k].rid = x
    BY <2>2
  <2>4. /\ s \in 1..Len(consensusLog')
        /\ consensusLog'[s] = consensusLog[s]
    BY <1>1
  <2>5. /\ k \in 1..Len(consensusLog'[s])
        /\ consensusLog'[s][k].rid = x
    BY <2>3, <2>4
  <2> QED
    BY <1>2, <2>1, <2>4, <2>5
<1>4. LogRids' \subseteq RequestIds
  BY <1>2
<1>5. CASE LogRids = RequestIds
  BY <1>3, <1>4, <1>5 DEF SlotsCount
<1>6. CASE LogRids # RequestIds
  <2>1. n <= Cardinality(LogRids)
    BY <1>6 DEF SlotsCount
  <2>2. DecidedRequestIds = LogRids
    BY DecidedIsLogRids
  <2>3. batch[1] \in UndecidedProposals
    BY <1>6, <2>2 DEF EligibleProposalItems
  <2> DEFINE x == batch[1].rid
  <2>4. x \notin LogRids
    BY <2>2, <2>3 DEF UndecidedProposals
  <2>5. batch[1] \in ResponseItems /\ 1 \in 1..Len(batch)
    OBVIOUS
  <2>6. x \in RequestIds
    BY <2>5 DEF ResponseItems
  <2>7. x \in LogRids'
    <3>1. /\ n + 1 \in 1..Len(consensusLog')
          /\ 1 \in 1..Len(consensusLog'[n + 1])
          /\ consensusLog'[n + 1][1].rid = x
      BY <1>1, <2>5
    <3> QED
      BY <1>2, <2>6, <3>1
  <2> HIDE DEF x
  <2>8. IsFiniteSet(LogRids') /\ IsFiniteSet(LogRids)
    <3>1. LogRids \subseteq RequestIds
      BY DEF LogRids
    <3> QED
      BY <1>4, <3>1, FS_Subset
  <2>9. /\ IsFiniteSet(LogRids \cup {x})
        /\ Cardinality(LogRids \cup {x}) = Cardinality(LogRids) + 1
    BY <2>4, <2>8, FS_AddElement
  <2>10. (LogRids \cup {x}) \in SUBSET LogRids'
    BY <1>3, <2>7
  <2>11. Cardinality(LogRids \cup {x}) <= Cardinality(LogRids')
    BY <2>8, <2>10, FS_Subset
  <2>12. /\ Cardinality(LogRids) \in Nat
         /\ Cardinality(LogRids') \in Nat
    BY <2>8, FS_CardinalityType
  <2>13. Len(consensusLog') <= Cardinality(LogRids')
    BY <1>1, <2>1, <2>9, <2>11, <2>12
  <2> QED
    BY <2>13 DEF SlotsCount
<1> QED
  BY <1>5, <1>6

LEMMA LiveDecide ==
    ASSUME LivenessAssumptions,
           LiveInv, ValidityInv,
           NEW batch \in Seq(ResponseItems),
           Len(batch) >= 1,
           batch[1] \in EligibleProposalItems,
           Len(consensusLog) < MaxSlots,
           consensusLog' = Append(consensusLog, batch),
           UNCHANGED <<leader, up, votes, seen, learned, dispatchers>>
    PROVE  LiveInv'
<1>1. consensusLog \in Seq(Seq(ResponseItems))
  BY DEF ValidityInv, ValidityTypeOK
<1>2. SlotsCount'
  BY <1>1, LiveDecideSlots DEF LivenessAssumptions, LiveInv
<1>3. Len(consensusLog') <= MaxSlots
  <2>1. MaxSlots \in Nat /\ Len(consensusLog) \in Nat
    BY <1>1, ConstantAssumptions
  <2>2. Len(consensusLog') = Len(consensusLog) + 1
    BY <1>1
  <2> QED
    BY <2>1, <2>2
<1>4. /\ leader' \in Replicas \union {NoNode}
      /\ up' \subseteq Replicas
      /\ votes' \in [RequestIds -> [Payloads -> SUBSET Replicas]]
      /\ seen' \in [Replicas -> SUBSET RequestIds]
      /\ learned' \in [Replicas -> SUBSET (1..MaxSlots)]
  BY DEF LiveInv
<1>5. LeaderUp' /\ NoCrashStable' /\ SingleDispatcher'
  BY DEF LiveInv, LeaderUp, NoCrashStable, SingleDispatcher
<1> QED
  BY <1>2, <1>3, <1>4, <1>5 DEF LiveInv

THEOREM LiveStep ==
    ASSUME LivenessAssumptions
    PROVE  LiveInv /\ ValidityInv /\ DeliveryInv /\ [Next]_vars => LiveInv'
<1> SUFFICES ASSUME LiveInv, ValidityInv, DeliveryInv, [Next]_vars
             PROVE  LiveInv'
  OBVIOUS
<1> USE DEF LivenessAssumptions, StrictDelivery
<1>d. DeliveryInv'
  BY DeliveryStep
<1>s. seen' \in [Replicas -> SUBSET RequestIds]
  BY <1>d DEF DeliveryInv, DeliveryTypeOK
<1>t. /\ leader \in Replicas \union {NoNode}
      /\ up \subseteq Replicas
      /\ LeaderUp
      /\ votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
      /\ learned \in [Replicas -> SUBSET (1..MaxSlots)]
      /\ dispatchers \in [RequestIds -> SUBSET Replicas]
  BY DEF LiveInv, ValidityInv, ValidityTypeOK
<1>1. CASE SubmitVoteAction
  <2>1. PICK replica \in Replicas, request \in RequestIds,
             payload \in Payloads : SubmitVote(replica, request, payload)
    BY <1>1 DEF SubmitVoteAction
  <2>2. votes' \in [RequestIds -> [Payloads -> SUBSET Replicas]]
    BY <2>1, <1>t DEF SubmitVote
  <2> QED
    BY <2>1, <2>2, <1>s, LiveFrame DEF SubmitVote
<1>2. CASE SelectAction
  BY <1>2, <1>s, <1>t, LiveFrame
     DEF SelectAction, SelectByQuorum, TimeoutSelect
<1>3. CASE DispatchAction
  <2>1. PICK replica \in Replicas, request \in RequestIds :
             Dispatch(replica, request)
    BY <1>3 DEF DispatchAction
  <2>2. /\ replica = leader
        /\ dispatchers' = [dispatchers EXCEPT
                              ![request] = @ \union {replica}]
        /\ UNCHANGED <<leader, up, votes, consensusLog, learned>>
    BY <2>1 DEF Dispatch
  <2>3. SingleDispatcher'
    <3>1. \A q \in RequestIds :
             dispatchers'[q] \subseteq dispatchers[q] \union {leader}
      BY <2>2, <1>t
    <3> QED
      BY <3>1, <2>2 DEF LiveInv, SingleDispatcher
  <2>4. LeaderUp' /\ NoCrashStable'
    BY <2>2 DEF LiveInv, LeaderUp, NoCrashStable
  <2>5. SlotsCount' /\ Len(consensusLog') <= MaxSlots
    BY <2>2 DEF LiveInv, SlotsCount, LogRids
  <2> QED
    BY <2>2, <2>3, <2>4, <2>5, <1>s, <1>t DEF LiveInv
<1>4. CASE ExternalRespondAction
  BY <1>4, <1>s, <1>t, LiveFrame
     DEF ExternalRespondAction, ExternalRespond
<1>5. CASE ProposeResponseAction
  BY <1>5, <1>s, <1>t, LiveFrame
     DEF ProposeResponseAction, ProposeResponse
<1>6. CASE DecideAction
  <2>1. ASSUME NEW item \in ResponseItems, DecideOne(item)
        PROVE  LiveInv'
    <3>1. /\ <<item>> \in Seq(ResponseItems)
          /\ Len(<<item>>) >= 1
          /\ <<item>>[1] = item
      OBVIOUS
    <3>2. /\ Len(consensusLog) < MaxSlots
          /\ item \in EligibleProposalItems
          /\ consensusLog' = Append(consensusLog, <<item>>)
          /\ UNCHANGED <<leader, up, votes, seen, learned, dispatchers>>
      BY <2>1 DEF DecideOne
    <3> QED
      BY <3>1, <3>2, LiveDecide
  <2>2. ASSUME NEW first \in ResponseItems,
               NEW second \in ResponseItems,
               DecidePair(first, second)
        PROVE  LiveInv'
    <3>1. /\ <<first, second>> \in Seq(ResponseItems)
          /\ Len(<<first, second>>) >= 1
          /\ <<first, second>>[1] = first
      OBVIOUS
    <3>2. /\ Len(consensusLog) < MaxSlots
          /\ first \in EligibleProposalItems
          /\ consensusLog' = Append(consensusLog, <<first, second>>)
          /\ UNCHANGED <<leader, up, votes, seen, learned, dispatchers>>
      BY <2>2 DEF DecidePair
    <3> QED
      BY <3>1, <3>2, LiveDecide
  <2> QED
    BY <1>6, <2>1, <2>2 DEF DecideAction
<1>7. CASE LearnAction
  <2>1. PICK replica \in Replicas, slot \in 1..MaxSlots :
             LearnSlot(replica, slot)
    BY <1>7 DEF LearnAction
  <2>2. /\ learned' = [learned EXCEPT ![replica] = @ \union {slot}]
        /\ UNCHANGED <<leader, up, votes, dispatchers, consensusLog>>
    BY <2>1 DEF LearnSlot
  <2>3. learned' \in [Replicas -> SUBSET (1..MaxSlots)]
    BY <2>2, <1>t
  <2>4. LeaderUp' /\ NoCrashStable' /\ SingleDispatcher'
    BY <2>2 DEF LiveInv, LeaderUp, NoCrashStable, SingleDispatcher
  <2>5. SlotsCount' /\ Len(consensusLog') <= MaxSlots
    BY <2>2 DEF LiveInv, SlotsCount, LogRids
  <2> QED
    BY <2>2, <2>3, <2>4, <2>5, <1>s, <1>t DEF LiveInv
<1>8. CASE ProcessAction
  BY <1>8, <1>s, <1>t, LiveFrame DEF ProcessAction, ProcessContiguous
<1>9. CASE \E replica \in Replicas, slot \in 1..MaxSlots :
              ProcessNonContiguous(replica, slot)
  BY <1>9 DEF ProcessNonContiguous
<1>10. CASE \E replica \in Replicas, item \in ResponseItems :
               DeliverBeforeConsensus(replica, item)
  BY <1>10 DEF DeliverBeforeConsensus
<1>11. CASE \E replica \in Replicas : Crash(replica)
  <2>1. PICK replica \in Replicas : Crash(replica)
    BY <1>11
  <2>2. /\ EnableCrashes
        /\ up' = up \ {replica}
        /\ leader' = IF leader = replica THEN NoNode ELSE leader
        /\ UNCHANGED <<votes, seen, consensusLog, learned, dispatchers>>
    BY <2>1 DEF Crash
  <2>3. /\ leader' \in Replicas \union {NoNode}
        /\ up' \subseteq Replicas
    BY <2>2, <1>t
  <2>4. leader' # NoNode => leader' \in up'
    BY <2>2, <1>t DEF LeaderUp
  <2> QED
    BY <2>2, <2>3, <2>4, LiveMembership
<1>12. CASE \E replica \in Replicas : Recover(replica)
  <2>1. PICK replica \in Replicas : Recover(replica)
    BY <1>12
  <2>2. /\ EnableCrashes
        /\ up' = up \union {replica}
        /\ UNCHANGED <<leader, votes, seen, consensusLog, learned,
                       dispatchers>>
    BY <2>1 DEF Recover
  <2>3. /\ leader' \in Replicas \union {NoNode}
        /\ up' \subseteq Replicas
    BY <2>2, <1>t
  <2>4. leader' # NoNode => leader' \in up'
    BY <2>2, <1>t DEF LeaderUp
  <2> QED
    BY <2>2, <2>3, <2>4, LiveMembership
<1>13. CASE \E replica \in Replicas : Elect(replica)
  <2>1. PICK replica \in Replicas : Elect(replica)
    BY <1>13
  <2>2. /\ EnableCrashes
        /\ replica \in up
        /\ leader' = replica
        /\ UNCHANGED <<up, votes, seen, consensusLog, learned,
                       dispatchers>>
    BY <2>1 DEF Elect
  <2>3. /\ leader' \in Replicas \union {NoNode}
        /\ up' \subseteq Replicas
    BY <2>2, <1>t
  <2>4. leader' # NoNode => leader' \in up'
    BY <2>2
  <2> QED
    BY <2>2, <2>3, <2>4, LiveMembership
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
  BY <1>16, <1>s, <1>t, LiveFrame DEF vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
     <1>11, <1>12, <1>13, <1>14, <1>15, <1>16 DEF Next

THEOREM LiveStateInvariant ==
    ASSUME LivenessAssumptions
    PROVE  Spec => []LiveState
<1>1. StrictDelivery
  BY DEF LivenessAssumptions
<1>2. Init => LiveState
  BY LiveInit, ValidityInit, DeliveryInit DEF LiveState
<1>3. LiveState /\ [Next]_vars => LiveState'
  BY <1>1, LiveStep, ValidityStep, DeliveryStep DEF LiveState
<1> QED
  BY <1>2, <1>3, PTL DEF Spec
=============================================================================

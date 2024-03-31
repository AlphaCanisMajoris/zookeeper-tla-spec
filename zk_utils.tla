----------------------------- MODULE zk_utils -----------------------------
(* 
    Common componenets of specifications for ZooKeeper and Zab, including
        - CONSTANTS
        - VARIABLES
        - TypeOK
        - INIT
        - utils
        - recorder functions
        - INVARIANTS
        - NETWORK
*)

EXTENDS Integers, FiniteSets, Sequences, Naturals, TLC

-----------------------------------------------------------------------------
(***** CONSTANTS *****)

\* The set of server identifiers
CONSTANT Server
\* Server states
CONSTANTS LOOKING, FOLLOWING, LEADING
\* Zab states of server
CONSTANTS ELECTION, DISCOVERY, SYNCHRONIZATION, BROADCAST
\* Serving states of server
CONSTANTS INITIAL, RUNNING, SHUTDOWN
\* Message types
CONSTANTS FOLLOWERINFO, LEADERINFO, ACKEPOCH, NEWLEADER, ACKLD, UPTODATE, PROPOSAL, ACK, COMMIT
\* Sync modes & message types
CONSTANTS TRUNC, DIFF, SNAP
\* [MaxTimeoutFailures, MaxTransactionNum, MaxEpoch, MaxCrashes, MaxPartitions]
CONSTANT Parameters

\* NullPoint == CHOOSE p: p \notin Server
CONSTANT NullPoint, ONLINE, OFFLINE

CONSTANT NONE


\* The set of requests that can go into history
\* CONSTANT Value \* Replaced by recorder.nClientRequest
Value == Nat

MAXEPOCH == 10

Quorums == {Q \in SUBSET Server: Cardinality(Q)*2 > Cardinality(Server)}

-----------------------------------------------------------------------------
(***** VARIABLES *****)

\* Variables that all servers use.
VARIABLES state,          \* State of server, in {LOOKING, FOLLOWING, LEADING}.
          zabState,       \* Current phase of server, in
                          \* {ELECTION, DISCOVERY, SYNCHRONIZATION, BROADCAST}.
          servingState,   \* Serving state of server, in
                          \* {INITIAL, RUNNING, SHUTDOWN}.
          acceptedEpoch,  \* Epoch of the last LEADERINFO packet accepted,
                          \* namely f.p in paper.
          currentEpoch,   \* Epoch of the last NEWLEADER packet accepted,
                          \* namely f.a in paper.
          history,        \* History of servers: sequence of transactions,
                          \* containing: [zxid, value, ackSid, epoch].
          lastCommitted,  \* Maximum index and zxid "in history" known to be committed,
                          \* namely 'lastCommitted' in Leader (maintained by all servers). 
                          \* Starts from 0, and increases monotonically before restarting.
          lastProcessed,  \* Index and zxid of the last processed txn.                          
          initialHistory, \* history that server initially has before election.
          lastSnapshot,   \* Index and zxid corresponding to latest snapshot
                          \* from data tree.
          hzxid           \* highest zxid kept in Leader's ZooKeeperServer. May not be in history.

\* Variables only used for leader.
VARIABLES learners,       \* Set of servers leader connects, 
                          \* namely 'learners' in Leader.
          connecting,     \* Set of learners leader has received 
                          \* FOLLOWERINFO from, namely  
                          \* 'connectingFollowers' in Leader.
                          \* Set of record [sid, connected].
          electing,       \* Set of learners leader has received
                          \* ACKEPOCH from, namely 'electingFollowers'
                          \* in Leader. Set of record 
                          \* [sid, peerLastZxid, inQuorum].
                          \* And peerLastZxid = <<-1,-1>> means has done
                          \* syncFollower with this sid.
                          \* inQuorum = TRUE means in code it is one
                          \* element in 'electingFollowers'.
          ackldRecv,      \* Set of learners leader has received
                          \* ACK of NEWLEADER from, namely
                          \* 'newLeaderProposal' in Leader.
                          \* Set of record [sid, connected].         
          forwarding,     \* Set of learners that are synced with
                          \* leader, namely 'forwardingFollowers'
                          \* in Leader.
          tempMaxEpoch    \* ({Maximum epoch in FOLLOWEINFO} + 1) that 
                          \* leader has received from learners,
                          \* namely 'epoch' in Leader.

\* Variables only used for follower.
VARIABLES connectInfo, \* Record [sid, syncMode, nlRcv].
                       \* sid: Leader id that follower has connected with.
                       \* syncMode: Sync mode according to reveiced Sync Message.
                       \* nlRcv: If follower has received NEWLEADER.
          packetsSync \* packets of PROPOSAL and COMMIT from leader,
                      \* namely 'packetsNotCommitted' and
                      \* 'packetsCommitted' in SyncWithLeader
                      \* in Learner.

VARIABLE leaderOracle \* Current leader.
                      \* Currently not used for node to search leader.

\* Variables about network channel.
VARIABLE rcvBuffer  \* Simulates network channel.
                    \* rcvBuffer[i][j] means the receive buffer of server j 
                    \* from server i.

\* Variables about status of cluster network and node presence.
VARIABLES status,    \* Whether the server is online or offline.
          partition  \* network partion.

\* Variables only used in verifying properties.
VARIABLES epochLeader,       \* Set of leaders in every epoch.
          proposalMsgsLog,   \* Set of all broadcast messages.
          committedLog       \* txns committed.
          
VARIABLES daInv,             \* Check invariants during action.
          aaInv              \* Check invariants after action.

\* Variable used for recording critical data,
\* to constrain state space or update values.
VARIABLE recorder \* Consists: members of Parameters and pc, values.
                  \* Form is record: 
                  \* [pc, nTransaction, maxEpoch, nTimeout, nClientRequest,
                  \*  nPartition, nCrash]

serverVars   == <<state, zabState, servingState, acceptedEpoch, currentEpoch>>
logVars      == <<history, initialHistory, lastCommitted, lastProcessed, lastSnapshot, hzxid>>
disVars      == <<connecting, tempMaxEpoch>>
noDisVars    == <<learners, electing, ackldRecv, forwarding>>
leaderVars   == <<disVars, noDisVars>>
followerVars == <<connectInfo, packetsSync>>
electionVars == <<leaderOracle>>
netVars      == <<rcvBuffer>>
envVars      == <<status, partition>>
verifyVars   == <<epochLeader, proposalMsgsLog>>
invVars      == <<daInv, aaInv>>
commitVars   == <<committedLog>>

coreVars == <<serverVars, logVars, leaderVars, followerVars, electionVars, 
        netVars, envVars, verifyVars, invVars, commitVars, recorder>>

-----------------------------------------------------------------------------
(***** TypeOK *****)

ServersIncNullPoint == Server \union {NullPoint} 

Zxid ==
    Seq(Nat \union {-1}) 
    
HistoryItem ==
     [ zxid: Zxid,
       value: Value,
       ackSid: SUBSET Server,
       epoch: Nat ]    
    
Proposal ==
    [ source: Server, 
      epoch: Nat,
      zxid: Zxid,
      data: Value ]   

LastItem ==
    [ index: Nat, zxid: Zxid ]

SyncPackets == 
    [ notCommitted: Seq(HistoryItem),
      committed: Seq(Zxid) ]

Message ==
    [ mtype: {FOLLOWERINFO}, mzxid: Zxid ] \union
    [ mtype: {LEADERINFO}, mzxid: Zxid ] \union
    [ mtype: {ACKEPOCH}, mzxid: Zxid, mepoch: Nat \union {-1} ] \union
    [ mtype: {DIFF}, mzxid: Zxid ] \union 
    [ mtype: {TRUNC}, mzxid: Zxid ] \union 
    [ mtype: {SNAP}, mzxid: Zxid, msnapshot: Seq(HistoryItem)] \union
    [ mtype: {PROPOSAL}, mzxid: Zxid, mdata: Value ] \union 
    [ mtype: {COMMIT}, mzxid: Zxid ] \union 
    [ mtype: {NEWLEADER}, mzxid: Zxid ] \union 
    [ mtype: {ACKLD}, mzxid: Zxid ] \union 
    [ mtype: {ACK}, mzxid: Zxid ] \union 
    [ mtype: {UPTODATE}, mzxid: Zxid ]

ElectionState == {LOOKING, FOLLOWING, LEADING}

ZabState == {ELECTION, DISCOVERY, SYNCHRONIZATION, BROADCAST}

ServingState == {INITIAL, RUNNING, SHUTDOWN}

DaInvSet == {"stateConsistent", "proposalConsistent", "commitConsistent", "ackConsistent", "messageLegal" }

AaInvSet == {"leadership", "integrity",      
              "agreement", "totalOrder", "localPrimaryOrder", "globalPrimaryOrder", "primaryIntegrity",
              "commitCompleteness", "commitConsistency", "historyConsistency"
              }

SyncMode == {DIFF, TRUNC, SNAP, NONE}

Connecting == [ sid : Server,
                connected: BOOLEAN ]

AckldRecv  == Connecting

Electing == [ sid: Server,
              peerLastZxid: Zxid,
              inQuorum: BOOLEAN  ]

ConnectInfo == [ sid : ServersIncNullPoint,
                 syncMode: SyncMode,
                 nlRcv: BOOLEAN ]

CoreTypeOK == 
    /\ state \in [Server -> ElectionState]
    /\ zabState \in [Server -> ZabState]
    /\ servingState \in [Server -> ServingState]
    /\ acceptedEpoch \in [Server -> Nat]
    /\ currentEpoch \in [Server -> Nat]
    /\ history \in [Server -> Seq(HistoryItem)]
    /\ initialHistory \in [Server -> Seq(HistoryItem)] 
    /\ lastCommitted \in [Server -> LastItem]
    /\ lastSnapshot \in [Server -> LastItem]
    /\ hzxid \in [Server -> Zxid]
    /\ lastProcessed \in [Server -> LastItem]
    /\ learners \in [Server -> SUBSET Server]
    /\ connecting \in [Server -> SUBSET Connecting]
    /\ electing \in [Server -> SUBSET Electing]
    /\ ackldRecv \in [Server -> SUBSET AckldRecv]
    /\ forwarding \in [Server -> SUBSET Server]
    /\ tempMaxEpoch \in [Server -> Nat]
    /\ connectInfo \in [Server -> ConnectInfo]
    /\ packetsSync \in [Server -> SyncPackets]
    /\ leaderOracle \in ServersIncNullPoint
    /\ rcvBuffer \in [Server -> [Server -> Seq(Message)]]
    /\ status \in [Server -> {ONLINE, OFFLINE}]
    /\ partition \in [Server -> [Server -> BOOLEAN ]]
    /\ proposalMsgsLog \in SUBSET Proposal
    /\ epochLeader \in [1..MAXEPOCH -> SUBSET Server]
    /\ daInv \in [DaInvSet -> BOOLEAN ]
    /\ aaInv \in [AaInvSet -> BOOLEAN ] 
    /\ committedLog \in Seq(HistoryItem)

-----------------------------------------------------------------------------
(***** INIT *****)

InitServerVars == /\ state         = [s \in Server |-> LOOKING]
                  /\ zabState      = [s \in Server |-> ELECTION]
                  /\ servingState  = [s \in Server |-> SHUTDOWN]
                  /\ acceptedEpoch = [s \in Server |-> 0]
                  /\ currentEpoch  = [s \in Server |-> 0]
InitLogVars == /\ history = [s \in Server |-> << >>]
               /\ initialHistory = [s \in Server |-> << >>]
               /\ lastCommitted = [s \in Server |-> [ index |-> 0,
                                                      zxid  |-> <<0, 0>> ] ]
               /\ lastProcessed = [s \in Server |-> [ index |-> 0,
                                                      zxid  |-> <<0, 0>>] ]    
               /\ lastSnapshot  = [s \in Server |-> [ index |-> 0,
                                                      zxid  |-> <<0, 0>> ] ]  
               /\ hzxid  = [s \in Server |-> <<0, 0>> ]     
InitLeaderVars == /\ learners       = [s \in Server |-> {}]
                  /\ connecting     = [s \in Server |-> {}]
                  /\ electing       = [s \in Server |-> {}]
                  /\ ackldRecv      = [s \in Server |-> {}]
                  /\ forwarding     = [s \in Server |-> {}]
                  /\ tempMaxEpoch   = [s \in Server |-> 0 ]
InitFollowerVars == /\ connectInfo = [s \in Server |-> [sid |-> NullPoint,
                                                        syncMode |-> NONE,
                                                        nlRcv |-> FALSE ] ]
                    /\ packetsSync = [s \in Server |->
                                        [ notCommitted |-> << >>,
                                          committed    |-> << >> ] ]
InitElectionVars == leaderOracle = NullPoint
InitMsgVars == /\ rcvBuffer = [s \in Server |-> [v \in Server |-> << >>] ]
InitEnvVars == /\ status    = [s \in Server |-> ONLINE ]
               /\ partition = [s \in Server |-> [v \in Server |-> FALSE] ]
InitVerifyVars == /\ proposalMsgsLog  = {}
                  /\ epochLeader      = [i \in 1..MAXEPOCH |-> {} ]
InitInvVars == /\ daInv  = [stateConsistent    |-> TRUE,
                            proposalConsistent |-> TRUE,
                            commitConsistent   |-> TRUE,
                            ackConsistent      |-> TRUE,
                            messageLegal       |-> TRUE ]
               /\ aaInv  = [ leadership        |-> TRUE,
                             integrity         |-> TRUE,
                             agreement         |-> TRUE,
                             totalOrder        |-> TRUE,
                             localPrimaryOrder |-> TRUE,
                             globalPrimaryOrder|-> TRUE,
                             primaryIntegrity  |-> TRUE,
                             commitCompleteness|-> TRUE,
                             commitConsistency |-> TRUE,
                             historyConsistency|-> TRUE]
InitCommitVars == committedLog = << >>
InitRecorder == recorder = [step           |-> 0,
                            nTimeout       |-> 0,
                            nTransaction   |-> 0,
                            nPartition     |-> 0,
                            maxEpoch       |-> 0,
                            nCrash         |-> 0,
                            pc             |-> <<"Init">>,
                            nClientRequest |-> 0,
                            nConsequentFailure |-> 0,
                            noExecute          |-> {} ]

CoreInit == /\ InitServerVars
            /\ InitLogVars
            /\ InitLeaderVars
            /\ InitFollowerVars
            /\ InitElectionVars
            /\ InitMsgVars
            /\ InitEnvVars
            /\ InitVerifyVars
            /\ InitInvVars
            /\ InitCommitVars
            /\ InitRecorder

-----------------------------------------------------------------------------
(***** UTILS *****)

\* Return the maximum value from the set S
Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n >= m

\* Return the minimum value from the set S
Minimum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n <= m

\* Check server state       
IsON(s)  == status[s] = ONLINE 
IsOFF(s) == status[s] = OFFLINE 

IsLeader(s)   == state[s] = LEADING
IsFollower(s) == state[s] = FOLLOWING
IsLooking(s)  == state[s] = LOOKING

IsMyLearner(i, j) == j \in learners[i]
IsMyLeader(i, j)  == connectInfo[i].sid = j
HasNoLeader(i)    == connectInfo[i].sid = NullPoint
HasLeader(i)      == connectInfo[i].sid /= NullPoint

\* Check if s is a quorum
IsQuorum(s) == s \in Quorums

HasPartitioned(i, j) == /\ partition[i][j] = TRUE 
                        /\ partition[j][i] = TRUE

----
\* FALSE: zxid1 <= zxid2; TRUE: zxid1 > zxid2
ZxidComparePredicate(zxid1, zxid2) == \/ zxid1[1] > zxid2[1]
                                      \/ /\ zxid1[1] = zxid2[1]
                                         /\ zxid1[2] > zxid2[2]

ZxidEqualPredicate(zxid1, zxid2) == /\ zxid1[1] = zxid2[1] 
                                    /\ zxid1[2] = zxid2[2]

TxnZxidEqual(txn, z) == txn.zxid[1] = z[1] /\ txn.zxid[2] = z[2]

TxnEqual(txn1, txn2) == /\ ZxidEqualPredicate(txn1.zxid, txn2.zxid)
                        /\ txn1.value = txn2.value

EpochPrecedeInTxn(txn1, txn2) == txn1.zxid[1] < txn2.zxid[1]

-----------------------------------------------------------------------------
(***** RECORDER FUNCTIONS *****)
GetParameter(p) == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE 0
GetRecorder(p)  == IF p \in DOMAIN recorder   THEN recorder[p]   ELSE 0

RecorderGetHelper(m) == (m :> recorder[m])
RecorderIncHelper(m) == (m :> recorder[m] + 1)

RecorderIncTimeout == RecorderIncHelper("nTimeout")
RecorderGetTimeout == RecorderGetHelper("nTimeout")
RecorderIncCrash   == RecorderIncHelper("nCrash")
RecorderGetCrash   == RecorderGetHelper("nCrash")

UnchangeRecorder   == UNCHANGED recorder

RecorderSetPc(pc)      == ("pc" :> pc)
RecorderSetFailure(pc) == CASE pc[1] = "Timeout"         -> RecorderIncTimeout @@ RecorderGetCrash
                          []   pc[1] = "LeaderTimeout"   -> RecorderIncTimeout @@ RecorderGetCrash 
                          []   pc[1] = "FollowerTimeout" -> RecorderIncTimeout @@ RecorderGetCrash 
                          []   pc[1] = "PartitionStart"  -> IF IsLooking(pc[2]) 
                                                            THEN RecorderGetTimeout @@ RecorderGetCrash
                                                            ELSE RecorderIncTimeout @@ RecorderGetCrash
                          []   pc[1] = "NodeCrash"       -> IF IsLooking(pc[2]) 
                                                            THEN RecorderGetTimeout @@ RecorderIncCrash 
                                                            ELSE RecorderIncTimeout @@ RecorderIncCrash 
                          []   OTHER                     -> RecorderGetTimeout @@ RecorderGetCrash

CheckParameterHelper(n, p, Comp(_,_)) == IF p \in DOMAIN Parameters 
                                         THEN Comp(n, Parameters[p])
                                         ELSE TRUE

CheckParameterLimit(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i < j)

\* For compress state space, we limit that external failure cannot appear too frequently,
\* or continuously.
CheckExternalFailure == /\ recorder.nConsequentFailure + 1 < Cardinality(Server)
                        /\ recorder.nCrash + recorder.nPartition <= (Cardinality(Server) - 1) * (recorder.maxEpoch + 1)
                        
CheckExternalEventExecute(pc) == 
            LET consider == IF pc[1] \in {"NodeCrash", "NodeStart", "PartitionStart", "PartitionRecover"} THEN TRUE ELSE FALSE 
            IN \/ ~consider
               \/ /\ consider 
                  /\ \/ /\ pc[1] \in {"NodeCrash", "NodeStart"}
                        /\ pc \notin recorder.noExecute
                     \/ /\ pc[1] \in {"PartitionStart", "PartitionRecover"}
                        /\ LET exist == \E event \in recorder.noExecute: event[1] = pc[1] 
                           IN \/ ~exist 
                              \/ /\ exist 
                                 /\ LET events == {event \in recorder.noExecute: event[1] = pc[1]} 
                                    IN \A event \in events: \/ pc[2] \notin event[2]
                                                            \/ pc[3] \notin event[2]
                                 
CheckTimeout        == CheckParameterLimit(recorder.nTimeout,     "MaxTimeoutFailures")
CheckTransactionNum == CheckParameterLimit(recorder.nTransaction, "MaxTransactionNum")
CheckEpoch          == CheckParameterLimit(recorder.maxEpoch,     "MaxEpoch")
CheckPartition      == CheckParameterLimit(recorder.nPartition,   "MaxPartitions")
CheckCrash(i)       == CheckParameterLimit(recorder.nCrash,    "MaxCrashes")
\* CheckStateConstraints == CheckTimeout /\ CheckTransactionNum /\ CheckEpoch /\ CheckPartition

\* recorder update
RecorderSetTransactionNum(pc) == ("nTransaction" :> 
                                IF pc[1] \in {"LeaderProcessRequest", "SetInitState"} THEN
                                    LET s == CHOOSE i \in Server: 
                                        \A j \in Server: Len(history'[i]) >= Len(history'[j])                       
                                    IN Len(history'[s])
                                ELSE recorder["nTransaction"])

RecorderSetMaxEpoch(pc)       == ("maxEpoch" :> 
                                IF pc[1] \in {"Election", "LeaderProcessFOLLOWERINFO", "FollowerProcessLEADERINFO", "ElectionAndDiscovery", "SetInitState"} THEN 
                                    LET s == CHOOSE i \in Server:
                                        \A j \in Server: acceptedEpoch'[i] >= acceptedEpoch'[j]
                                    IN acceptedEpoch'[s]
                                ELSE recorder["maxEpoch"])

RecorderSetRequests(pc)       == ("nClientRequest" :>
                                IF pc[1] = "LeaderProcessRequest" THEN
                                    recorder["nClientRequest"] + 1
                                ELSE IF pc[1] = "SetInitState" THEN 2
                                     ELSE recorder["nClientRequest"] )

RecorderSetPartition(pc)      == ("nPartition" :> 
                                IF pc[1] = "PartitionStart" THEN recorder["nPartition"] + 1
                                                            ELSE recorder["nPartition"] ) 

RecorderSetConsequentFailure(pc) == ("nConsequentFailure" :> 
                                IF pc[1] \in {"NodeCrash", "PartitionStart"} THEN
                                    recorder["nConsequentFailure"] + 1
                                ELSE IF pc[1] \in {"ElectionAndDiscovery", "Election"}
                                     THEN 0 ELSE recorder["nConsequentFailure"] )

RECURSIVE ReleaseNoExecute(_,_)
ReleaseNoExecute(remaining, S) == 
                               IF remaining = {} THEN {}
                               ELSE LET event == CHOOSE e \in remaining: TRUE 
                                        re     == remaining \ {event}
                                    IN CASE event[1] = "NodeCrash" ->
                                                IF event[2] \in S THEN ReleaseNoExecute(re, S)
                                                ELSE {event} \union ReleaseNoExecute(re, S)
                                       []   event[1] = "NodeStart" ->
                                                ReleaseNoExecute(re, S)
                                       []   event[1] = "PartitionStart" ->
                                                IF \E s \in event[2]: s \in S THEN ReleaseNoExecute(re, S)
                                                ELSE {event} \union ReleaseNoExecute(re, S)
                                       []   event[1] = "PartitionRecover" ->
                                                ReleaseNoExecute(re, S)

RecorderSetNoExecute(pc) == ("noExecute" :> 
                                IF pc[1] \in {"NodeCrash", "PartitionStart"} THEN 
                                    CASE pc[1] = "NodeCrash" -> 
                                            LET s == pc[2]
                                            IN IF state[s] = LOOKING 
                                               THEN recorder["noExecute"] \union {<<"NodeStart", s>>, <<"NodeCrash", s>>}
                                               ELSE recorder["noExecute"] \union {<<"NodeCrash", s>>}
                                    []   pc[1] = "PartitionStart" ->
                                            LET s == pc[2]
                                                v == pc[3]
                                            IN IF state[s] = LOOKING /\ state[v] = LOOKING
                                               THEN recorder["noExecute"] \union {<<"PartitionRecover", {s, v}>>, <<"PartitionStart", {s, v}>>}
                                               ELSE recorder["noExecute"] \union {<<"PartitionStart", {s, v}>>}
                                ELSE IF pc[1] \in {"ElectionAndDiscovery", "Election"} THEN 
                                        LET l  == pc[2]
                                            fs == pc[3]
                                        IN ReleaseNoExecute(recorder["noExecute"], {l} \union fs)
                                     ELSE recorder["noExecute"] )                        

UpdateRecorder(pc) == recorder' = RecorderIncHelper("step") 
                                  @@ RecorderSetPartition(pc) @@ RecorderSetConsequentFailure(pc)
                                  @@ RecorderSetNoExecute(pc)
                                  @@  RecorderSetFailure(pc)  @@ RecorderSetTransactionNum(pc)
                                  @@ RecorderSetMaxEpoch(pc)  @@ RecorderSetPc(pc) 
                                  @@ RecorderSetRequests(pc)  @@ recorder 

-----------------------------------------------------------------------------
(***** INVARIANTS (Checked after action) *****)

\* There is most one established leader for a certain epoch.
Leadership1 == \A i, j \in Server:
                /\ state'[i] = LEADING /\ zabState'[i] \in {SYNCHRONIZATION, BROADCAST}
                /\ state'[j] = LEADING /\ zabState'[j] \in {SYNCHRONIZATION, BROADCAST}
                /\ currentEpoch'[i] = currentEpoch'[j]
                => i = j

Leadership2 == \A epoch \in 1..MAXEPOCH: Cardinality(epochLeader'[epoch]) <= 1

\* Integrity: If some process delivers one transaction, then some primary has broadcast it.
Integrity == \A i \in Server: lastCommitted'[i].index > 0
                => \A idx \in 1..lastCommitted'[i].index: \E proposal \in proposalMsgsLog':
                    LET txn_proposal == [ zxid  |-> proposal.zxid,
                                          value |-> proposal.data ]
                    IN  TxnEqual(history'[i][idx], txn_proposal)

\* Agreement: If some process f delivers transaction a and some process f' delivers transaction b,
\*            then f' delivers a or f delivers b.
Agreement == \A i, j \in Server: 
                /\ lastCommitted'[i].index > 0
                /\ lastCommitted'[j].index > 0
                =>
                \A idx1 \in 1..lastCommitted'[i].index, idx2 \in 1..lastCommitted'[j].index :
                    \/ \E idx_j \in 1..lastCommitted'[j].index:
                        TxnEqual(history'[j][idx_j], history'[i][idx1])
                    \/ \E idx_i \in 1..lastCommitted'[i].index:
                        TxnEqual(history'[i][idx_i], history'[j][idx2])

\* Total order: If some process delivers a before b, then any process that delivers b
\*              must also deliver a and deliver a before b.
TotalOrder == \A i, j \in Server: 
                LET committed1 == lastCommitted'[i].index 
                    committed2 == lastCommitted'[j].index  
                IN committed1 >= 2 /\ committed2 >= 1
                    => \A idx_i1 \in 1..(committed1 - 1) : \A idx_i2 \in (idx_i1 + 1)..committed1 :
                    LET logOk == \E idx \in 1..committed2 :
                                     TxnEqual(history'[i][idx_i2], history'[j][idx])
                    IN \/ ~logOk 
                       \/ /\ logOk 
                          /\ \E idx_j2 \in 1..committed2 : 
                                /\ TxnEqual(history'[i][idx_i2], history'[j][idx_j2])
                                /\ \E idx_j1 \in 1..(idx_j2 - 1):
                                       TxnEqual(history'[i][idx_i1], history'[j][idx_j1])

\* Local primary order: If a primary broadcasts a before it broadcasts b, then a process that
\*                      delivers b must also deliver a before b.
LocalPrimaryOrder == LET p_set(i, e) == {p \in proposalMsgsLog': /\ p.source = i 
                                                                 /\ p.epoch  = e }
                         txn_set(i, e) == { [ zxid  |-> p.zxid, 
                                              value |-> p.data ] : p \in p_set(i, e) }
                     IN \A i \in Server: \A e \in 1..currentEpoch'[i]:
                         \/ Cardinality(txn_set(i, e)) < 2
                         \/ /\ Cardinality(txn_set(i, e)) >= 2
                            /\ \E txn1, txn2 \in txn_set(i, e):
                             \/ TxnEqual(txn1, txn2)
                             \/ /\ ~TxnEqual(txn1, txn2)
                                /\ LET TxnPre  == IF ZxidComparePredicate(txn1.zxid, txn2.zxid) THEN txn2 ELSE txn1
                                       TxnNext == IF ZxidComparePredicate(txn1.zxid, txn2.zxid) THEN txn1 ELSE txn2
                                   IN \A j \in Server: /\ lastCommitted'[j].index >= 2
                                                       /\ \E idx \in 1..lastCommitted'[j].index: 
                                                            TxnEqual(history'[j][idx], TxnNext)
                                        => \E idx2 \in 1..lastCommitted'[j].index: 
                                            /\ TxnEqual(history'[j][idx2], TxnNext)
                                            /\ idx2 > 1
                                            /\ \E idx1 \in 1..(idx2 - 1): 
                                                TxnEqual(history'[j][idx1], TxnPre)

\* Global primary order: A process f delivers both a with epoch e and b with epoch e', and e < e',
\*                       then f must deliver a before b.
GlobalPrimaryOrder == \A i \in Server: lastCommitted'[i].index >= 2
                         => \A idx1, idx2 \in 1..lastCommitted'[i].index:
                                \/ ~EpochPrecedeInTxn(history'[i][idx1], history'[i][idx2])
                                \/ /\ EpochPrecedeInTxn(history'[i][idx1], history'[i][idx2])
                                   /\ idx1 < idx2

\* Primary integrity: If some primary p broadcasts a and some process f delivers b such that b has epoch
\*                    smaller than epoch of p, then p must deliver b before it broadcasts a.
PrimaryIntegrity == \A i, j \in Server: /\ state'[i] = LEADING /\ zabState'[i] = BROADCAST  
                                        /\ state'[j] = FOLLOWING /\ zabState'[j] = BROADCAST
                                        /\ currentEpoch'[i] = acceptedEpoch'[i]
                                        /\ currentEpoch'[i] = currentEpoch'[j]
                                        /\ lastCommitted'[j].index >= 1
                        => \A idx_j \in 1..lastCommitted'[j].index:
                                \/ history'[j][idx_j].zxid[1] >= currentEpoch'[i]
                                \/ /\ history'[j][idx_j].zxid[1] < currentEpoch'[i]
                                   /\ \E idx_i \in 1..lastCommitted'[i].index: 
                                        TxnEqual(history'[i][idx_i], history'[j][idx_j])

\* Leader's committed log will always become longer and each txn committed is always the same.
RECURSIVE TxnEqualHelper(_,_,_,_)
TxnEqualHelper(leaderLog, standardLog, cur, end) ==
        IF cur > end THEN TRUE
        ELSE IF ~TxnEqual(leaderLog[cur], standardLog[cur]) THEN FALSE 
             ELSE TxnEqualHelper(leaderLog, standardLog, cur+1, end)

RECURSIVE TxnNotEqualHelper(_,_,_,_)
TxnNotEqualHelper(followerLog, standardLog, cur, end) ==
        IF cur > end THEN TRUE
        ELSE IF TxnEqual(followerLog[cur], standardLog[cur]) THEN FALSE
             ELSE TxnNotEqualHelper(followerLog, standardLog, cur+1, end)

\* Commit completeness: Leader's committed log will contain previous committed log.
CommitCompleteness ==
        \/ leaderOracle' \notin Server
        \/ /\ leaderOracle' \in Server
           /\ LET leader == leaderOracle'
                  index  == lastCommitted'[leader].index
                  on   == status'[leader] = ONLINE
                  lead == state'[leader] = LEADING 
                  bc   == zabState'[leader] = BROADCAST
              IN \/ ~on \/ ~lead \/ ~bc 
                 \/ /\ lead 
                    /\ bc
                     => /\ index >= Len(committedLog)
                        /\ TxnEqualHelper(history'[leader], committedLog, 1, Minimum({index, Len(committedLog)}))

\* Commit consistency:  In Broadcast, a follower's committed history must be the leader's committed history prefix. 
CommitConsistency == \A i, j \in Server:
                        /\ state'[i] = LEADING   /\ zabState'[i] = BROADCAST
                        /\ state'[j] = FOLLOWING /\ zabState'[j] = BROADCAST
                        /\ currentEpoch'[i] = acceptedEpoch'[i]
                        /\ currentEpoch'[i] = currentEpoch'[j]
                     => LET minCommit == Minimum({lastCommitted'[i].index, lastCommitted'[j].index})
                        IN /\ lastCommitted'[i].index >= lastCommitted'[j].index
                           /\ \/ minCommit = 0
                              \/ /\ minCommit > 0
                                 /\ \A index \in 1..minCommit: TxnEqual(history'[i][index], history'[j][index])

\* History consistency: In Broadcast, a follower's history must be the leader's history prefix.                                   
HistoryConsistency == \A i, j \in Server: 
                        /\ state'[i] = LEADING   /\ zabState'[i] = BROADCAST
                        /\ state'[j] = FOLLOWING /\ zabState'[j] = BROADCAST
                        /\ currentEpoch'[i] = acceptedEpoch'[i]
                        /\ currentEpoch'[i] = currentEpoch'[j]
                     => /\ Len(history'[i]) >= Len(history'[j]) 
                        /\ TxnEqualHelper(history'[i], history'[j], 1, Minimum({Len(history'[i]), Len(history'[j])}))

UpdateAfterAction == /\ aaInv' = [  leadership          |-> Leadership1 /\ Leadership2,
                                    integrity           |-> Integrity,
                                    agreement           |-> Agreement,
                                    totalOrder          |-> TotalOrder,
                                    localPrimaryOrder   |-> LocalPrimaryOrder,
                                    globalPrimaryOrder  |-> GlobalPrimaryOrder,
                                    primaryIntegrity    |-> PrimaryIntegrity,
                                    commitCompleteness  |-> CommitCompleteness,
                                    commitConsistency   |-> CommitConsistency,
                                    historyConsistency  |-> HistoryConsistency]
                     /\ committedLog' = LET leader == leaderOracle'
                                        IN IF leader \notin Server THEN committedLog
                                           ELSE LET index  == lastCommitted'[leader].index
                                                    on   == status'[leader] = ONLINE
                                                    lead == state'[leader] = LEADING
                                                    bc   == zabState'[leader] = BROADCAST
                                                IN IF /\ on /\ lead /\ bc
                                                   THEN IF index <= 0 THEN << >> 
                                                        ELSE SubSeq(history'[leader], 1, index)
                                                   ELSE committedLog

\* For TLC model checker
AfterActionCheck == \A p \in DOMAIN aaInv: aaInv[p] = TRUE
DuringActionCheck == \A p \in DOMAIN daInv: daInv[p] = TRUE

-----------------------------------------------------------------------------
(***** NETWORK *****)

PendingFOLLOWERINFO(i, j) == /\ rcvBuffer[j][i] /= << >>
                             /\ rcvBuffer[j][i][1].mtype = FOLLOWERINFO
PendingLEADERINFO(i, j)   == /\ rcvBuffer[j][i] /= << >>
                             /\ rcvBuffer[j][i][1].mtype = LEADERINFO
PendingACKEPOCH(i, j)     == /\ rcvBuffer[j][i] /= << >>
                             /\ rcvBuffer[j][i][1].mtype = ACKEPOCH
PendingNEWLEADER(i, j)    == /\ rcvBuffer[j][i] /= << >>
                             /\ rcvBuffer[j][i][1].mtype = NEWLEADER
PendingACKLD(i, j)        == /\ rcvBuffer[j][i] /= << >>
                             /\ rcvBuffer[j][i][1].mtype = ACKLD
PendingUPTODATE(i, j)     == /\ rcvBuffer[j][i] /= << >>
                             /\ rcvBuffer[j][i][1].mtype = UPTODATE
PendingPROPOSAL(i, j)     == /\ rcvBuffer[j][i] /= << >>
                             /\ rcvBuffer[j][i][1].mtype = PROPOSAL
PendingACK(i, j)          == /\ rcvBuffer[j][i] /= << >>
                             /\ rcvBuffer[j][i][1].mtype = ACK
PendingCOMMIT(i, j)       == /\ rcvBuffer[j][i] /= << >>
                             /\ rcvBuffer[j][i][1].mtype = COMMIT

AddMsg(msg, toAdd, from, to) == IF partition[from][to] = FALSE
                                THEN msg \o toAdd
                                ELSE msg

\* Add a message to rcvBuffer - add a message m to rcvBuffer.
Send(i, j, m) == rcvBuffer' = [rcvBuffer EXCEPT ![i][j] = AddMsg(@, <<m>>, i, j) ]

SendPackets(i, j, ms, needDiscard) ==
        rcvBuffer' = [rcvBuffer EXCEPT ![i][j] = AddMsg(@, ms, i, j),
                                       ![j][i] = IF needDiscard = TRUE THEN Tail(@)
                                                                       ELSE @ ]

\* Remove a message from rcvBuffer - discard head of rcvBuffer.
Discard(i, j) == rcvBuffer' = IF rcvBuffer[i][j] /= << >> THEN [rcvBuffer EXCEPT ![i][j] = Tail(@)]
                                                          ELSE rcvBuffer
\* Leader broadcasts a message(PROPOSAL/COMMIT) to all other servers in forwardingFollowers.
Broadcast(i, j, m, needDiscard) ==
        rcvBuffer' = [rcvBuffer EXCEPT ![j][i] = IF needDiscard = TRUE THEN Tail(@)
                                                             ELSE @ ,
                             ![i] = [v \in Server |-> IF /\ v \in forwarding[i]
                                                         /\ v /= i
                                                      THEN AddMsg(rcvBuffer[i][v], <<m>>, i, v)
                                                      ELSE rcvBuffer[i][v]] ]          
\* Leader broadcasts LEADERINFO to all other servers in connectingFollowers.
BroadcastLEADERINFO(i, j, m, needDiscard) ==
        LET new_connecting_quorum == {c \in connecting'[i]: c.connected = TRUE }
            new_sid_connecting == {c.sid: c \in new_connecting_quorum }
        IN 
        rcvBuffer' = [rcvBuffer EXCEPT ![j][i] = IF needDiscard = TRUE THEN Tail(@)
                                                             ELSE @ ,
                             ![i] = [v \in Server |-> IF /\ v \in new_sid_connecting
                                                         /\ v \in learners[i] 
                                                         /\ v /= i
                                                      THEN AddMsg(rcvBuffer[i][v], <<m>>, i, v)
                                                      ELSE rcvBuffer[i][v] ] ]
\* Leader broadcasts UPTODATE to all other servers in newLeaderProposal.
BroadcastUPTODATE(i, j, m, needDiscard) ==
        LET new_ackldRecv_quorum == {a \in ackldRecv'[i]: a.connected = TRUE }
            new_sid_ackldRecv == {a.sid: a \in new_ackldRecv_quorum}
        IN
        rcvBuffer' = [rcvBuffer EXCEPT ![j][i] = IF needDiscard = TRUE THEN Tail(@)
                                                             ELSE @ ,
                             ![i] = [v \in Server |-> IF /\ v \in new_sid_ackldRecv
                                                         /\ v \in learners[i] 
                                                         /\ v /= i
                                                      THEN AddMsg(rcvBuffer[i][v], <<m>>, i, v)
                                                      ELSE rcvBuffer[i][v] ] ]
\* Combination of Send and Discard - discard head of rcvBuffer[j][i] and add m into rcvBuffer.
Reply(i, j, m) == rcvBuffer' = [rcvBuffer EXCEPT ![j][i] = Tail(@),
                                                 ![i][j] = AddMsg(@, <<m>>, i, j) ]

\* Shuffle input buffer.
Clean(i, j) == rcvBuffer' = [rcvBuffer EXCEPT ![j][i] = << >>, ![i][j] = << >>]     

CleanInputBuffer(S) == rcvBuffer' = [s \in Server |-> 
                                     [v \in Server |-> IF v \in S THEN << >>
                                                       ELSE rcvBuffer[s][v] ] ]  

-----------------------------------------------------------------------------
\* Common dependencies

\* Assuming that everytime committing two txns, node takes snapshot.
ShouldSnapshot(i) == lastCommitted[i].index - lastSnapshot[i].index >= 2

(* There are mainly three places where calling takeSnapshot():
   1. zk.loadData() in lead() when node becomes leader;
   2. syncRequestProcessor.run() tells when to snapshot;
   3. node processing NEWLEADER in learner.syncWithLeader();
 *)
 TakeSnapshot(i) == /\ lastSnapshot' = [ lastSnapshot EXCEPT ![i] = lastCommitted[i] ]
                    /\ UNCHANGED daInv

=============================================================================
----------------------------- MODULE zk_core -----------------------------
(* Core specification for Zab's implementation of ZooKeeper. *)

(* This spec focuses on:
    - Zab's three core phases: discovery, sync, and broadcast. Most actions are modeled as an upon-do process: upon receiving a message, do local processing and reply.
    - Failures: node start/crash, network partition/recovery
    - Abstraction of non-core phases like election and message forwarding
    - All trasactions refer to the operation setData
*)

EXTENDS zk_utils

-----------------------------------------------------------------------------
baseVars == <<coreVars>>

-----------------------------------------------------------------------------   
BaseTypeOK == CoreTypeOK

-----------------------------------------------------------------------------
BaseInit == CoreInit
          
-----------------------------------------------------------------------------
\* return -1: this zxid appears at least twice; Len(his) + 1: does not exist;
\* 1 ~ Len(his): exists and appears just once.
RECURSIVE ZxidToIndexHepler(_,_,_,_)
ZxidToIndexHepler(his, zxid, cur, appeared) == 
        IF cur > Len(his) THEN cur  
        ELSE IF TxnZxidEqual(his[cur], zxid) 
             THEN CASE appeared = TRUE -> -1
                  []   OTHER           -> Minimum( { cur, 
                            ZxidToIndexHepler(his, zxid, cur + 1, TRUE) } ) 
             ELSE ZxidToIndexHepler(his, zxid, cur + 1, appeared)

ZxidToIndex(his, zxid) == IF ZxidEqualPredicate( zxid, <<0, 0>> ) THEN 0
                          ELSE IF Len(his) = 0 THEN 1
                               ELSE LET len == Len(his) IN
                                    IF \E idx \in 1..len: TxnZxidEqual(his[idx], zxid)
                                    THEN ZxidToIndexHepler(his, zxid, 1, FALSE)
                                    ELSE len + 1

RECURSIVE TruncZxidToIndexHepler(_,_,_)
TruncZxidToIndexHepler(his, zxid, cur) == 
        IF cur > Len(his) THEN cur - 1  
        ELSE IF TxnZxidEqual(his[cur], zxid) THEN cur
        ELSE IF ZxidComparePredicate(his[cur].zxid, zxid) THEN cur - 1
        ELSE TruncZxidToIndexHepler(his, zxid, cur + 1) 

TruncZxidToIndex(his, zxid) == IF ZxidEqualPredicate( zxid, <<0, 0>> ) THEN 0
                               ELSE IF Len(his) = 0 THEN 1
                               ELSE LET len == Len(his) IN
                                    IF \E idx \in 1..len: (ZxidComparePredicate(his[idx].zxid, zxid) \/ TxnZxidEqual(his[idx], zxid))
                                    THEN TruncZxidToIndexHepler(his, zxid, 1)
                                    ELSE len + 1

RECURSIVE UpdateConnectingHelper(_)
UpdateConnectingHelper(idSet) == 
        IF idSet = { } THEN { }
        ELSE LET chosen == CHOOSE id \in idSet: TRUE
             IN { [sid       |-> chosen,
                   connected |-> TRUE] } 
                \union UpdateConnectingHelper(idSet \ {chosen})

RECURSIVE UpdateElectingHelper(_,_)
UpdateElectingHelper(idSet, needSync) ==
        IF idSet = { } THEN { }
        ELSE LET chosen == CHOOSE id \in idSet: TRUE 
             IN { [sid          |-> chosen,
                   peerLastZxid |-> IF needSync 
                                    THEN lastProcessed'[chosen].zxid
                                    ELSE <<-1, -1>>,
                   inQuorum     |-> TRUE] } 
                \union UpdateElectingHelper(idSet \ {chosen}, needSync)

RECURSIVE UpdateAckldRecvHelper(_)
UpdateAckldRecvHelper(idSet) ==
        IF idSet = { } THEN { }
        ELSE LET chosen == CHOOSE id \in idSet: TRUE
             IN { [sid       |-> chosen,
                   connected |-> TRUE] }
                \union UpdateAckldRecvHelper(idSet \ {chosen})

\* Processing of idTable and order comparing
RECURSIVE InitializeIdTable(_)
InitializeIdTable(Remaining) == IF Remaining = {} THEN {}
                                ELSE LET chosen == CHOOSE i \in Remaining: TRUE
                                         re     == Remaining \ {chosen}
                                     IN {<<chosen, Cardinality(Remaining)>>} \union InitializeIdTable(re)

IdTable == InitializeIdTable(Server) 

IdComparePredicate(s1, s2) == LET item1 == CHOOSE item \in IdTable: item[1] = s1
                                  item2 == CHOOSE item \in IdTable: item[1] = s2
                              IN item1[2] > item2[2]

\* TotalOrderPredicate(s1, s2) = TRUE represents s1 is at least as up-to-date as s2.
TotalOrderPredicate(s1, s2) == \/ currentEpoch[s1] > currentEpoch[s2]
                               \/ /\ currentEpoch[s1] = currentEpoch[s2]
                                  /\ \/ ZxidComparePredicate(lastProcessed[s1].zxid, lastProcessed[s2].zxid)
                                     \/ /\ ZxidEqualPredicate(lastProcessed[s1].zxid, lastProcessed[s2].zxid)
                                        /\ IdComparePredicate(s1, s2)

InitialConnectInfo == [sid        |-> NullPoint,
                       syncMode   |-> NONE,
                       nlRcv      |-> FALSE ]

SetConnectInfo(l, mode, rcvNl) == [ sid        |-> l,
                                    syncMode   |-> mode,
                                    nlRcv      |-> rcvNl ]

-----------------------------------------------------------------------------
InitLastProcessed(i) == IF Len(history'[i]) = 0 THEN [ index |-> 0, 
                                                      zxid  |-> <<0, 0>> ]
                        ELSE LET lastIndex == Len(history'[i])
                                 entry     == history'[i][lastIndex]
                             IN [ index |-> lastIndex,
                                  zxid  |-> entry.zxid ]
    
RECURSIVE InitAcksidInTxns(_,_)
InitAcksidInTxns(txns, src) == IF Len(txns) = 0 THEN << >>
                               ELSE LET newTxn == [ zxid   |-> txns[1].zxid,
                                                    value  |-> txns[1].value,
                                                    ackSid |-> {src},
                                                    epoch  |-> txns[1].epoch ]
                                    IN <<newTxn>> \o InitAcksidInTxns( Tail(txns), src)

InitHistory(i) == LET newState == state'[i] IN 
                    IF newState = LEADING THEN InitAcksidInTxns(history[i], i)
                    ELSE history[i]

GetLastCommitted(i) == LET completeHis == history[i] \o packetsSync[i].notCommitted
                           lastIdx ==  Len(packetsSync[i].committed)
                           toBeCommitted == packetsSync[i].committed[lastIdx]
                           commitIndex == ZxidToIndex(completeHis, toBeCommitted)
                       IN [ index |-> commitIndex, zxid  |-> toBeCommitted ]

Shutdown(S, crashSet) ==
        /\ state'         = [s \in Server |-> IF s \in S THEN LOOKING ELSE state[s] ]
        /\ zabState'      = [s \in Server |-> IF s \in S THEN ELECTION ELSE zabState[s] ]
        /\ servingState'  = [s \in Server |-> IF s \in S THEN SHUTDOWN ELSE servingState[s] ]
        /\ connectInfo'   = [s \in Server |-> IF s \in S THEN InitialConnectInfo ELSE connectInfo[s] ]
        /\ CleanInputBuffer(S)
        \* If SyncRequestProcessor starts, it logs all pending txns if not crashed
        /\ history' = [s \in Server |-> 
                        LET inCluster == s \in S
                            inCrashSet == s \in crashSet
                            syncProcessorReady == servingState[s] /= SHUTDOWN
                            pengdingProposal == packetsSync[s].notCommitted /= << >>
                        IN IF /\ inCluster 
                              /\ ~inCrashSet
                              /\ syncProcessorReady
                              /\ pengdingProposal
                           THEN history[s] \o packetsSync[s].notCommitted
                           ELSE history[s] ]
        /\ initialHistory' = [s \in Server |-> IF s \in S THEN history'[s] 
                                                ELSE initialHistory[s] ]
        /\ lastCommitted' = [s \in Server |-> IF s \in S THEN [ index |-> 0, zxid  |-> <<0, 0>> ] 
                                                         ELSE lastCommitted[s] ]  
        \* clear volatile data
        /\ packetsSync' = [s \in Server |-> IF s \in S THEN [ notCommitted |-> << >>,
                                                              committed |-> << >> ]
                                                       ELSE packetsSync[s] ]
        /\ lastProcessed' = [s \in Server |-> IF s \in S THEN InitLastProcessed(s)
                                                         ELSE lastProcessed[s] ]
        \* see ZooKeeperServer.loadData()
        /\ hzxid' = [s \in Server |-> IF s \in S THEN lastProcessed'[s].zxid ELSE hzxid[s]]

FollowerShutdown(i, isCrash) ==
        /\ state'           = [state        EXCEPT ![i] = LOOKING]
        /\ zabState'        = [zabState     EXCEPT ![i] = ELECTION]
        /\ servingState'    = [servingState EXCEPT ![i] = SHUTDOWN]
        /\ connectInfo'     = [connectInfo  EXCEPT ![i] = InitialConnectInfo]
        \* If SyncRequestProcessor starts, it logs all pending txns if not crashed
        /\ history' = [history EXCEPT ![i] = 
                        IF \/ isCrash 
                           \/ servingState[i] = SHUTDOWN 
                           \/ packetsSync[i].notCommitted = << >>
                        THEN @ 
                        ELSE @ \o packetsSync[i].notCommitted ]
        /\ initialHistory' = [initialHistory EXCEPT ![i] = history'[i] ]
        /\ lastCommitted' = [lastCommitted EXCEPT ![i] = [ index |-> 0,
                                                           zxid  |-> <<0, 0>> ] ]
        \* clear volatile data
        /\ packetsSync' = [packetsSync EXCEPT ![i].notCommitted = << >>, 
                                              ![i].committed = << >>]
        \* in version 3.7+, lastProcessed will be modified when turning to LOOKING
        /\ lastProcessed' = [lastProcessed EXCEPT ![i] = InitLastProcessed(i)]
        /\ hzxid' = [hzxid EXCEPT ![i] = lastProcessed'[i].zxid]

LeaderShutdown(i, crashSet) ==
        /\ LET cluster == {i} \union learners[i]
           IN Shutdown(cluster, crashSet)
        /\ learners'   = [learners   EXCEPT ![i] = {}]
        /\ forwarding' = [forwarding EXCEPT ![i] = {}]
        /\ leaderOracle' = NullPoint

RemoveElecting(set, sid) ==
        LET sid_electing == {s.sid: s \in set }
        IN IF sid \notin sid_electing THEN set
           ELSE LET info == CHOOSE s \in set: s.sid = sid
                    new_info == [ sid          |-> sid,
                                  peerLastZxid |-> <<-1, -1>>,
                                  inQuorum     |-> info.inQuorum ]
                IN (set \ {info}) \union {new_info}
RemoveConnectingOrAckldRecv(set, sid) ==
        LET sid_set == {s.sid: s \in set}
        IN IF sid \notin sid_set THEN set
           ELSE LET info == CHOOSE s \in set: s.sid = sid
                    new_info == [ sid       |-> sid,
                                  connected |-> FALSE ]
                IN (set \ {info}) \union {new_info}

\* See removeLearnerHandler for details.
RemoveLearner(i, j) ==
        /\ learners'   = [learners   EXCEPT ![i] = @ \ {j}] 
        /\ forwarding' = [forwarding EXCEPT ![i] = IF j \in forwarding[i] 
                                                   THEN @ \ {j} ELSE @ ]
        /\ electing'   = [electing   EXCEPT ![i] = RemoveElecting(@, j) ]
        /\ connecting' = [connecting EXCEPT ![i] = RemoveConnectingOrAckldRecv(@, j) ]
        /\ ackldRecv'  = [ackldRecv  EXCEPT ![i] = RemoveConnectingOrAckldRecv(@, j) ]

\* Assuming there only exists two conditions that may trigger partition:
\* 1. leader and learner that follows it. 2. looking and looking
PartitionStart(i, j) == 
        /\ CheckExternalEventExecute(<<"PartitionStart", i, j>>)
        /\ CheckPartition
        /\ i /= j
        /\ IsON(i) 
        /\ IsON(j)
        /\ \lnot HasPartitioned(i, j)
        /\ \/ /\ IsLeader(i)   /\ IsMyLearner(i, j)
              /\ IsFollower(j) /\ IsMyLeader(j, i)
              /\ LET newCluster == learners[i] \ {j}
                 IN \/ /\ IsQuorum(newCluster)    \* just remove this learner
                       /\ RemoveLearner(i, j) 
                       /\ FollowerShutdown(j, FALSE)
                       /\ Clean(i, j)
                       /\ UNCHANGED electionVars
                    \/ /\ ~IsQuorum(newCluster)   \* leader switches to looking
                       /\ LeaderShutdown(i, {})
                       /\ UNCHANGED <<electing, connecting, ackldRecv>>
           \/ /\ IsLooking(i) 
              /\ IsLooking(j)
              /\ IdComparePredicate(i, j) \* to compress state space
              /\ UNCHANGED <<state, zabState, servingState, lastProcessed, hzxid, connecting, noDisVars,
                             history, initialHistory, lastCommitted, connectInfo, packetsSync, netVars, electionVars>>
        /\ partition' = [partition EXCEPT ![i][j] = TRUE, ![j][i] = TRUE ]
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, lastSnapshot, tempMaxEpoch, status, verifyVars, daInv>>
        /\ UpdateRecorder(<<"PartitionStart", i, j>>)
         

PartitionRecover(i, j) == 
        /\ CheckExternalEventExecute(<<"PartitionRecover", i, j>>)
        /\ IsON(i)
        /\ IsON(j)
        /\ IdComparePredicate(i, j) \* to compress state space
        /\ HasPartitioned(i, j)
        /\ partition' = [partition EXCEPT ![i][j] = FALSE, ![j][i] = FALSE ]
        /\ UNCHANGED <<serverVars, logVars, leaderVars, followerVars, electionVars, netVars,
                status, verifyVars, daInv>>
        /\ UpdateRecorder(<<"PartitionRecover", i, j>>)
         

NodeCrash(i) ==
        /\ CheckExternalEventExecute(<<"NodeCrash", i>>)
        /\ CheckCrash(i)
        /\ IsON(i)
        /\ status' = [status EXCEPT ![i] = OFFLINE ]
        /\ \/ /\ IsLooking(i)
              /\ UNCHANGED <<state, zabState, servingState, lastProcessed, hzxid, connecting, noDisVars,
                             history, initialHistory, lastCommitted, connectInfo, packetsSync, netVars, electionVars>>
           \/ /\ IsFollower(i)
              /\ LET connectedWithLeader == leaderOracle /= NullPoint /\ i \in learners[leaderOracle]
                    \*  connectedWithLeader == HasLeader(i)
                 IN \/ /\ connectedWithLeader
                       /\ LET leader == leaderOracle
                            \*   leader == connectInfo[i].sid
                              newCluster == learners[leader] \ {i}
                          IN 
                          \/ /\ IsQuorum(newCluster)
                             /\ RemoveLearner(leader, i) 
                             /\ FollowerShutdown(i, TRUE)
                             /\ Clean(leader, i)
                             /\ UNCHANGED electionVars
                          \/ /\ ~IsQuorum(newCluster)
                             /\ LeaderShutdown(leader, {i})
                             /\ UNCHANGED <<electing, connecting, ackldRecv>>
                    \/ /\ ~connectedWithLeader 
                       /\ FollowerShutdown(i, TRUE)
                       /\ CleanInputBuffer({i})
                       /\ UNCHANGED <<connecting, noDisVars, electionVars>>
           \/ /\ IsLeader(i)
              /\ LeaderShutdown(i, {i})
              /\ UNCHANGED <<connecting, electing, ackldRecv>>
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, lastSnapshot, tempMaxEpoch, partition, verifyVars, daInv>>
        /\ UpdateRecorder(<<"NodeCrash", i>>)
         

NodeStart(i) == 
        /\ CheckExternalEventExecute(<<"NodeStart", i>>)
        /\ IsOFF(i)
        /\ status'          = [status       EXCEPT ![i] = ONLINE ]
        /\ state'           = [state        EXCEPT ![i] = LOOKING ]
        /\ zabState'        = [zabState     EXCEPT ![i] = ELECTION ]
        /\ servingState'    = [servingState EXCEPT ![i] = SHUTDOWN]
        /\ UNCHANGED <<history>>
        /\ lastProcessed'   = [lastProcessed  EXCEPT ![i] = InitLastProcessed(i)]
        /\ lastCommitted'   = [lastCommitted EXCEPT ![i] = [ index |-> 0,
                                                             zxid  |-> <<0, 0>> ] ]
        /\ hzxid'           = [hzxid  EXCEPT ![i] = lastProcessed'[i].zxid]
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, initialHistory, lastSnapshot,
                       leaderVars, followerVars, electionVars, netVars, partition,
                       verifyVars, daInv>>                                                   
        /\ UpdateRecorder(<<"NodeStart", i>>)

-----------------------------------------------------------------------------
\* All node elecion + discovery, sync + broadcast and commit <1, 1>,
\* leader broadcasts <1, 2>.
SetInitState == 
        /\ recorder["step"] = 0
        /\ LET l == CHOOSE i \in Server: \A s \in (Server\{i}): TotalOrderPredicate(i, s)
               f == Server \ {l}
           IN 
           /\ state' = [s \in Server |-> IF s = l THEN LEADING ELSE FOLLOWING]
           /\ zabState' = [s \in Server |-> BROADCAST]
           /\ servingState' = [s \in Server |-> RUNNING]
           /\ acceptedEpoch' = [s \in Server |-> 1]
           /\ currentEpoch' = [s \in Server |-> 1]
           /\ LET txn_1 == [zxid   |-> <<1, 1>>, value |-> 101, \* create session, omit
                            ackSid |-> Server,   epoch |-> 1 ] \* create key, committed
                  txn_2 == [zxid   |-> <<1, 2>>, value |-> 102,
                            ackSid |-> {l},      epoch |-> 1 ] \* set data, not commit
              IN history' = [s \in Server |-> 
                                IF s = l THEN <<txn_1, txn_2>> 
                                ELSE <<txn_1>> ]
           /\ lastCommitted' = [s \in Server |-> [ index |-> 1,
                                                   zxid  |-> <<1, 1>> ]]
           /\ lastProcessed' = [s \in Server |-> [ index |-> 1,
                                                   zxid  |-> <<1, 1>> ]]
           /\ hzxid' = [s \in Server |-> IF s = l THEN <<1, 2>> ELSE <<1, 1>> ]
           /\ tempMaxEpoch' = [tempMaxEpoch EXCEPT ![l] = 1]
           /\ learners' = [learners EXCEPT ![l] = Server]  
           /\ connecting' = [connecting EXCEPT ![l] = { [ sid       |-> l,
                                                          connected |-> TRUE ] } 
                                                   \union UpdateConnectingHelper(f) ]
           /\ electing' = [electing EXCEPT ![l] = { [ sid          |-> l,
                                                      peerLastZxid |-> <<-1,-1>>,
                                                      inQuorum     |-> TRUE ] }
                                                   \union UpdateElectingHelper(f, FALSE) ]
           /\ ackldRecv' = [ackldRecv EXCEPT ![l] = {[ sid       |-> l,
                                                       connected |-> TRUE ]}
                                                   \union UpdateConnectingHelper(f) ]
           /\ forwarding' = [forwarding EXCEPT ![l] = f]
           /\ connectInfo'  = [s \in Server |-> IF s \in f THEN SetConnectInfo(l, NONE, TRUE) ELSE connectInfo[s] ]
           /\ leaderOracle' = l 
           /\ LET pp2 == [mtype |-> PROPOSAL, mzxid |-> <<1, 2>>, mdata |-> 102]
              IN rcvBuffer' = [rcvBuffer EXCEPT ![l] = [v \in Server |-> IF v \in f
                                                                         THEN <<pp2>>
                                                                         ELSE << >>]]
           /\ epochLeader' = [epochLeader EXCEPT ![1] = {l}]
           /\ LET p1 == [source |-> l, epoch |-> 1, zxid |-> <<1, 1>>, data |-> 101]
                  p2 == [source |-> l, epoch |-> 1, zxid |-> <<1, 2>>, data |-> 102]
              IN proposalMsgsLog' = {p1, p2}
           /\ UNCHANGED <<initialHistory, lastSnapshot, packetsSync, envVars, daInv>>
           /\ UpdateRecorder(<<"SetInitState", l, f>>)

-----------------------------------------------------------------------------
\* ld: leader, fs: set of followers
UpdateStateToPhaseDiscovery(ld, fs) ==
        /\ state'          = [s \in Server |-> IF s = ld THEN LEADING 
                                               ELSE IF s \in fs THEN FOLLOWING 
                                                                ELSE state[s] ]
        /\ zabState'       = [s \in Server |-> IF (s = ld \/ s \in fs) /\ (zabState[s] = ELECTION) THEN DISCOVERY
                                                                     ELSE zabState[s] ]
        /\ initialHistory' = [s \in Server |-> IF s = ld THEN InitHistory(s)
                                               ELSE IF s \in fs THEN history[s] 
                                                                ELSE initialHistory[s] ]
        \* initialize leader
        /\ history'        = [history      EXCEPT ![ld] = InitHistory(ld) ]
        /\ learners'       = [learners     EXCEPT ![ld] = {ld} \union fs ]
        /\ connecting'     = [connecting   EXCEPT ![ld] = { [ sid       |-> ld,
                                                              connected |-> TRUE ] } ]
        /\ electing'       = [electing     EXCEPT ![ld] = { [ sid          |-> ld,
                                                              peerLastZxid |-> <<-1,-1>>,
                                                              inQuorum     |-> TRUE ] } ]
        /\ ackldRecv'      = [ackldRecv    EXCEPT ![ld] = { [ sid       |-> ld,
                                                              connected |-> TRUE ] }]
        /\ forwarding'     = [forwarding   EXCEPT ![ld] = {} ]   
        /\ tempMaxEpoch'   = [tempMaxEpoch EXCEPT ![ld] = acceptedEpoch[ld] + 1]
        \* initialize follower
        /\ packetsSync'    = [s \in Server |-> IF s \in fs THEN [notCommitted |-> << >>,
                                                                 committed    |-> << >> ]
                                                           ELSE packetsSync[s] ]

Election(i, S) ==
        \* /\ CheckEpoch
        /\ i \in S 
        /\ IsQuorum(S)
        /\ \A s \in S: /\ IsON(s)
                       /\ ~HasPartitioned(i, s)
                       /\ IsLooking(s)
        /\ \A s \in (Server\S): \/ IsOFF(s)
                                \/ HasPartitioned(i, s)
                                \/ ~IsLooking(s)
        /\ \A s \in (S\{i}): TotalOrderPredicate(i, s)
        /\ leaderOracle' = i
        /\ UpdateStateToPhaseDiscovery(i, S\{i})
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, epochLeader, connectInfo>>
        /\ UNCHANGED <<servingState, lastCommitted, lastProcessed, hzxid, lastSnapshot,
                       netVars, envVars, proposalMsgsLog, daInv>>
        /\ UpdateRecorder(<<"Election", i, S\{i}, currentEpoch[i], lastProcessed'[i], currentEpoch'[i]  >>)
         
FollowLeader(i, j) ==
        /\ IsON(i)
        /\ IsON(j)
        /\ ~HasPartitioned(i, j)
        /\ IsLooking(i)
        /\ IsLeader(j)
        /\ leaderOracle = j
        /\ state'    = [state    EXCEPT ![i] = FOLLOWING]
        /\ zabState' = [zabState EXCEPT ![i] = DISCOVERY]
        /\ UNCHANGED <<history>>
        /\ initialHistory' = [initialHistory EXCEPT ![i] = history[i]]
        /\ lastProcessed'  = [lastProcessed  EXCEPT ![i] = InitLastProcessed(i)]
        /\ packetsSync'    = [packetsSync    EXCEPT ![i].notCommitted = << >>, 
                                                    ![i].committed = << >> ]
        /\ learners'       = [learners     EXCEPT ![j] = learners[j] \union {i} ] 
        /\ UNCHANGED <<disVars, electing, ackldRecv, forwarding, connectInfo>>
        /\ UNCHANGED <<servingState, acceptedEpoch, currentEpoch, lastCommitted, lastSnapshot, hzxid, electionVars, netVars, envVars, verifyVars, daInv>> 
        /\ UpdateRecorder(<<"FollowLeader", i, j>>)
         

-----------------------------------------------------------------------------
(* Establish connection between leader and follower, containing actions like 
   addLearnerHandler, findLeader, connectToLeader.*)
ConnectAndFollowerSendFOLLOWERINFO(i, j) ==
        /\ IsON(i)     /\ IsON(j)
        /\ IsLeader(i) 
        \* /\ \lnot IsMyLearner(i, j)
        /\ IsFollower(j) 
        /\ HasNoLeader(j) 
        /\ learners'   = [learners   EXCEPT ![i] = learners[i] \union {j}] 
        /\ connectInfo' = [connectInfo EXCEPT ![j].sid = i]
        /\ Send(j, i, [ mtype |-> FOLLOWERINFO,
                        mzxid |-> <<acceptedEpoch[j], 0>> ])  
        /\ UNCHANGED <<daInv, logVars>>
        /\ UNCHANGED <<serverVars, electionVars, disVars, 
                       electing, ackldRecv, forwarding,
                       verifyVars, envVars, packetsSync>>
        /\ UpdateRecorder(<<"ConnectAndFollowerSendFOLLOWERINFO", i, j>>)
         

\* waitingForNewEpoch in Leader
WaitingForNewEpoch(i, set) == (i \in set /\ IsQuorum(set)) = FALSE
WaitingForNewEpochTurnToFalse(i, set) == /\ i \in set
                                         /\ IsQuorum(set) 

\* There may exists some follower in connecting but shuts down and
\* connects again. So when leader broadcasts LEADERINFO, the
\* follower will receive LEADERINFO, and receive it again after
\* sending FOLLOWERINFO. So connected makes sure each follower
\* will only receive LEADERINFO at most once before timeout. 
UpdateConnectingOrAckldRecv(oldSet, sid) ==
        LET sid_set == {s.sid: s \in oldSet}
        IN IF sid \in sid_set
           THEN LET old_info == CHOOSE info \in oldSet: info.sid = sid
                    follower_info == [ sid       |-> sid,
                                       connected |-> TRUE ]
                IN (oldSet \ {old_info} ) \union {follower_info}
           ELSE LET follower_info == [ sid       |-> sid,
                                       connected |-> TRUE ]
                IN oldSet \union {follower_info}

(* Leader waits for receiving FOLLOWERINFO from a quorum including itself,
   and chooses a new epoch e' as its own epoch and broadcasts LEADERINFO.
   See getEpochToPropose in Leader for details. *)
LeaderProcessFOLLOWERINFO(i, j) ==
        /\ CheckEpoch  
        /\ IsON(i)
        /\ IsLeader(i)
        /\ PendingFOLLOWERINFO(i, j)
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLearner(i, j)
               lastAcceptedEpoch == msg.mzxid[1]
               sid_connecting == {c.sid: c \in connecting[i]}
           IN 
           /\ infoOk
           /\ \/ \* 1. has not broadcast LEADERINFO 
                 /\ WaitingForNewEpoch(i, sid_connecting)
                 /\ \/ /\ zabState[i] = DISCOVERY
                       /\ UNCHANGED daInv
                    \/ /\ zabState[i] /= DISCOVERY
                       /\ PrintT("Exception: waitingFotNewEpoch true," \o
                          " while zabState not DISCOVERY.")
                       /\ daInv' = [daInv EXCEPT !.stateConsistent = FALSE]
                 /\ tempMaxEpoch' = [tempMaxEpoch EXCEPT ![i] = IF lastAcceptedEpoch >= tempMaxEpoch[i] 
                                                                THEN lastAcceptedEpoch + 1
                                                                ELSE @]
                 /\ connecting'   = [connecting   EXCEPT ![i] = UpdateConnectingOrAckldRecv(@, j) ]
                 /\ LET new_sid_connecting == {c.sid: c \in connecting'[i]}
                    IN
                    \/ /\ WaitingForNewEpochTurnToFalse(i, new_sid_connecting)
                       /\ acceptedEpoch' = [acceptedEpoch EXCEPT ![i] = tempMaxEpoch'[i]]
                       /\ LET newLeaderZxid == <<acceptedEpoch'[i], 0>>
                              m == [ mtype |-> LEADERINFO,
                                     mzxid |-> newLeaderZxid ]
                          IN /\ hzxid' = [hzxid EXCEPT ![i] = newLeaderZxid]
                             /\ BroadcastLEADERINFO(i, j, m, TRUE)
                    \/ /\ ~WaitingForNewEpochTurnToFalse(i, new_sid_connecting)
                       /\ Discard(j, i)
                       /\ UNCHANGED <<acceptedEpoch, hzxid>>
              \/  \* 2. has broadcast LEADERINFO 
                 /\ ~WaitingForNewEpoch(i, sid_connecting)
                 /\ Reply(i, j, [ mtype |-> LEADERINFO,
                                  mzxid |-> <<acceptedEpoch[i], 0>> ] )
                 /\ UNCHANGED <<tempMaxEpoch, connecting, acceptedEpoch, hzxid, daInv>>
        /\ UNCHANGED <<servingState, state, zabState, currentEpoch, history, initialHistory, lastCommitted, lastProcessed, lastSnapshot, noDisVars, followerVars, electionVars, envVars, verifyVars>>
        /\ UpdateRecorder(<<"LeaderProcessFOLLOWERINFO", i, j>>)
         

(* Follower receives LEADERINFO. If newEpoch >= acceptedEpoch, then follower 
   updates acceptedEpoch and sends ACKEPOCH back, containing currentEpoch and
   lastProcessedZxid. After this, zabState turns to SYNC. 
   See registerWithLeader in Learner for details.*)
FollowerProcessLEADERINFO(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingLEADERINFO(i, j)
        /\ LET msg      == rcvBuffer[j][i][1]
               newEpoch == msg.mzxid[1]
               infoOk   == IsMyLeader(i, j)
               epochOk  == newEpoch >= acceptedEpoch[i]
               stateOk  == zabState[i] = DISCOVERY
           IN /\ infoOk
              /\ \/ \* 1. Normal case
                    /\ epochOk   
                    /\ \/ /\ stateOk
                          /\ \/ /\ newEpoch > acceptedEpoch[i]
                                /\ acceptedEpoch' = [acceptedEpoch EXCEPT ![i] = newEpoch]
                                /\ LET epochBytes == currentEpoch[i]
                                       m == [ mtype  |-> ACKEPOCH,
                                              mzxid  |-> lastProcessed[i].zxid, 
                                              mepoch |-> epochBytes ] 
                                   IN Reply(i, j, m)
                             \/ /\ newEpoch = acceptedEpoch[i]
                                /\ LET m == [ mtype  |-> ACKEPOCH,
                                              mzxid  |-> lastProcessed[i].zxid,
                                              mepoch |-> -1 ]
                                   IN Reply(i, j, m)
                                /\ UNCHANGED acceptedEpoch
                          /\ zabState' = [zabState EXCEPT ![i] = SYNCHRONIZATION]
                          /\ UNCHANGED daInv
                       \/ /\ ~stateOk
                          /\ PrintT("Exception: Follower receives LEADERINFO," \o
                             " whileZabState not DISCOVERY.")
                          /\ daInv' = [daInv EXCEPT !.stateConsistent = FALSE]
                          /\ Discard(j, i)
                          /\ UNCHANGED <<acceptedEpoch, zabState>>
                    /\ UNCHANGED <<state, servingState, history, initialHistory, lastProcessed, lastCommitted, hzxid, packetsSync, connecting, noDisVars, connectInfo, electionVars>>
                 \/ \* 2. Abnormal case - go back to election
                    /\ ~epochOk 
                    /\ LET newCluster == learners[j] \ {i}
                       IN \/ /\ IsQuorum(newCluster)    \* just remove this learner
                             /\ RemoveLearner(j, i) 
                             /\ FollowerShutdown(i, FALSE)
                             /\ Clean(i, j)
                             /\ UNCHANGED electionVars
                          \/ /\ ~IsQuorum(newCluster)   \* leader switches to looking
                             /\ LeaderShutdown(j, {})
                             /\ UNCHANGED <<electing, connecting, ackldRecv>>
                    /\ UNCHANGED <<acceptedEpoch, daInv>>
        /\ UNCHANGED <<currentEpoch, lastSnapshot, tempMaxEpoch, envVars, verifyVars>>
        /\ UpdateRecorder(<<"FollowerProcessLEADERINFO", i, j>>)
         

----------------------------------------------------------------------------- 
RECURSIVE UpdateAckSidHelper(_,_,_,_)
UpdateAckSidHelper(his, cur, end, target) ==
        IF cur > end THEN his
        ELSE LET curTxn == [ zxid   |-> his[1].zxid,
                             value  |-> his[1].value,
                             ackSid |-> IF target \in his[1].ackSid THEN his[1].ackSid
                                        ELSE his[1].ackSid \union {target},
                             epoch  |-> his[1].epoch ]
             IN <<curTxn>> \o UpdateAckSidHelper(Tail(his), cur + 1, end, target)

\* There originally existed one bug in LeaderProcessACK when 
\* monotonicallyInc = FALSE, and it is we did not add ackSid of 
\* history in SYNC. So we update ackSid in syncFollower.
UpdateAckSid(his, lastSeenIndex, target) ==
        IF Len(his) = 0 \/ lastSeenIndex = 0 THEN his
        ELSE UpdateAckSidHelper(his, 1, Minimum( { Len(his), lastSeenIndex} ), target)

\* Find index idx which meets: 
\* history[idx].zxid <= zxid < history[idx + 1].zxid
RECURSIVE IndexOfZxidHelper(_,_,_,_)
IndexOfZxidHelper(his, zxid, cur, end) ==
        IF cur > end THEN end
        ELSE IF ZxidComparePredicate(his[cur].zxid, zxid) THEN cur - 1
             ELSE IndexOfZxidHelper(his, zxid, cur + 1, end)

IndexOfZxid(his, zxid) == IF Len(his) = 0 THEN 0
                          ELSE LET idx == ZxidToIndex(his, zxid)
                                   len == Len(his)
                               IN 
                               IF idx <= len THEN idx
                               ELSE IndexOfZxidHelper(his, zxid, 1, len)

RECURSIVE queuePackets(_,_,_,_,_)
queuePackets(queue, his, cur, committed, end) == 
        IF cur > end THEN queue
        ELSE CASE cur > committed ->
                LET m_proposal == [ mtype |-> PROPOSAL, 
                                    mzxid |-> his[cur].zxid,
                                    mdata |-> his[cur].value ]
                IN queuePackets(Append(queue, m_proposal), his, cur + 1, committed, end)
             []   cur <= committed ->
                LET m_proposal == [ mtype |-> PROPOSAL, 
                                    mzxid |-> his[cur].zxid,
                                    mdata |-> his[cur].value ]
                    m_commit   == [ mtype |-> COMMIT,
                                    mzxid |-> his[cur].zxid ]
                    newQueue   == queue \o <<m_proposal, m_commit>>
                IN queuePackets(newQueue, his, cur + 1, committed, end)

RECURSIVE setPacketsForChecking(_,_,_,_,_,_)
setPacketsForChecking(set, src, ep, his, cur, end) ==
        IF cur > end THEN set
        ELSE LET m_proposal == [ source |-> src,
                                 epoch  |-> ep,
                                 zxid   |-> his[cur].zxid,
                                 data   |-> his[cur].value ]
             IN setPacketsForChecking((set \union {m_proposal}), src, ep, his, cur + 1, end)

\* Func lead() calls zk.loadData(), which will call takeSnapshot().
LastSnapshot(i) == IF zabState[i] = BROADCAST THEN lastSnapshot[i]
                   ELSE CASE IsLeader(i) -> 
                            LET lastIndex == Len(history[i])
                            IN IF lastIndex = 0 THEN [ index |-> 0,
                                                       zxid  |-> <<0, 0>> ]
                               ELSE [ index |-> lastIndex,
                                      zxid  |-> history[i][lastIndex].zxid ]
                        []   OTHER -> lastSnapshot[i]

\* To compress state space, 
\* 1. we merge sending SNAP and outputing snapshot buffer into sending SNAP, and
\* 2. substitute sub sequence of history for snapshot of data tree.
SerializeSnapshot(i, idx) == IF idx <= 0 THEN << >>
                             ELSE SubSeq(history[i], 1, idx)

(* See queueCommittedProposals in LearnerHandler and startForwarding in Leader
   for details. For proposals in committedLog and toBeApplied, send <PROPOSAL,
   COMMIT>. For proposals in outstandingProposals, send PROPOSAL only. *)
SendSyncMsgs(i, j, lastSeenZxid, lastSeenIndex, mode, needRemoveHead, maxCommittedLog) ==
        /\ LET lastCommittedIndex == IF zabState[i] = BROADCAST 
                                     THEN lastCommitted[i].index
                                     ELSE Len(history[i])
               lastProposedIndex  == Len(history[i])
               queue_origin == IF lastSeenIndex >= lastProposedIndex 
                               THEN << >>
                               ELSE queuePackets(<< >>, history[i], 
                                    lastSeenIndex + 1, lastCommittedIndex,
                                    lastProposedIndex)
               set_forChecking == IF lastSeenIndex >= lastProposedIndex 
                                  THEN {}
                                  ELSE setPacketsForChecking( { }, i, 
                                        acceptedEpoch[i], history[i],
                                        lastSeenIndex + 1, lastProposedIndex)
               m_trunc == [ mtype |-> TRUNC, mzxid |-> lastSeenZxid ]
               m_diff  == [ mtype |-> DIFF,  mzxid |-> maxCommittedLog, mindex |-> ZxidToIndex(history[i], lastSeenZxid) ]
               m_snap  == [ mtype |-> SNAP,  mzxid |-> lastSeenZxid,
                                             msnapshot |-> SerializeSnapshot(i, lastSeenIndex) ]
               newLeaderZxid == <<acceptedEpoch[i], 0>>
               m_newleader == [ mtype |-> NEWLEADER,
                                mzxid |-> newLeaderZxid ]
               queue_toSend == CASE mode = TRUNC -> (<<m_trunc>> \o queue_origin) \o <<m_newleader>>
                               []   mode = DIFF  -> (<<m_diff>>  \o queue_origin) \o <<m_newleader>>
                               []   mode = SNAP  -> (<<m_snap>>  \o queue_origin) \o <<m_newleader>>
           IN /\ \/ /\ needRemoveHead
                    /\ SendPackets(i, j, queue_toSend, TRUE) 
                 \/ /\ ~needRemoveHead
                    /\ SendPackets(i, j, queue_toSend, FALSE)
              /\ proposalMsgsLog' = proposalMsgsLog \union set_forChecking
        /\ forwarding' = [forwarding EXCEPT ![i] = @ \union {j} ]
        /\ \/ /\ mode = TRUNC \/ mode = DIFF 
              /\ history' = [history EXCEPT ![i] = UpdateAckSid(@, lastSeenIndex, j) ]
           \/ /\ mode = SNAP
              /\ UNCHANGED history \* txns before minCommitted don't need to be committed again

(* Leader syncs with follower by sending DIFF/TRUNC/SNAP/PROPOSAL/COMMIT/NEWLEADER.
   See syncFollower in LearnerHandler for details. *)
SyncFollower(i, j, peerLastZxid, needRemoveHead) ==
        LET IsPeerNewEpochZxid == peerLastZxid[2] = 0
            lastProcessedZxid == lastProcessed[i].zxid
            minCommittedIdx   == lastSnapshot[i].index + 1
            maxCommittedIdx   == IF zabState[i] = BROADCAST THEN lastCommitted[i].index
                                 ELSE Minimum( { Len(history[i]), 
                                        TruncZxidToIndex(history[i], lastProcessedZxid) } ) 
            committedLogEmpty == minCommittedIdx > maxCommittedIdx
            minCommittedLog   == IF committedLogEmpty THEN lastProcessedZxid
                                 ELSE history[i][minCommittedIdx].zxid
            maxCommittedLog   == IF committedLogEmpty THEN lastProcessedZxid
                                 ELSE IF maxCommittedIdx = 0 THEN << 0, 0>>
                                      ELSE history[i][maxCommittedIdx].zxid

            \* Hypothesis: 1. minCommittedLog : txn with index of lastSnapshot + 1
            \*             2. maxCommittedLog : LastCommitted, to compress state space.
            \*             3. merge queueCommittedProposals,startForwarding and 
            \*                sending NEWLEADER into SendSyncMsgs.

        IN \/ \* case1. peerLastZxid = lastProcessedZxid,
              \*        send DIFF & StartForwarding(lastProcessedZxid)
              /\ ZxidEqualPredicate(peerLastZxid, lastProcessedZxid)
              /\ SendSyncMsgs(i, j, peerLastZxid, lastProcessed[i].index, 
                                    DIFF, needRemoveHead, maxCommittedLog)
           \/ /\ ~ZxidEqualPredicate(peerLastZxid, lastProcessedZxid)
              /\ \/ \* case2. peerLastZxid > maxCommittedLog && !isPeerNewEpochZxid
                    \*        send TRUNC(maxCommittedLog) & StartForwarding
                    /\ ZxidComparePredicate(peerLastZxid, maxCommittedLog)
                    /\ ~IsPeerNewEpochZxid
                    /\ SendSyncMsgs(i, j, maxCommittedLog, maxCommittedIdx, 
                                          TRUNC, needRemoveHead, maxCommittedLog)
                 \/ \* case3. minCommittedLog <= peerLastZxid <= maxCommittedLog
                    /\ ~ZxidComparePredicate(peerLastZxid, maxCommittedLog)
                    /\ ~ZxidComparePredicate(minCommittedLog, peerLastZxid)
                    /\ LET lastSeenIndex == ZxidToIndex(history[i], peerLastZxid)
                           exist == /\ lastSeenIndex >= minCommittedIdx
                                    /\ lastSeenIndex <= Len(history[i])
                           lastIndex == IF exist THEN lastSeenIndex
                                        ELSE TruncZxidToIndex(history[i], peerLastZxid)
                           \* Maximum zxid that < peerLastZxid
                           lastZxid  == IF exist THEN peerLastZxid
                                        ELSE IF lastIndex = 0 THEN <<0, 0>>
                                             ELSE history[i][lastIndex].zxid
                       IN 
                       \/ \* case 3.1. peerLastZxid exists in committedLog,
                          \*           DIFF + queueCommittedProposals(peerLastZxid + 1)
                          \*                + StartForwarding
                          /\ exist
                          /\ SendSyncMsgs(i, j, peerLastZxid, lastSeenIndex, 
                                                DIFF, needRemoveHead, maxCommittedLog)
                       \/ \* case 3.2. peerLastZxid does not exist in committedLog,
                          \*           TRUNC(lastZxid) + queueCommittedProposals(lastZxid + 1)
                          \*                           + StartForwarding
                          /\ ~exist
                          /\ SendSyncMsgs(i, j, lastZxid, lastIndex, 
                                                TRUNC, needRemoveHead, maxCommittedLog)
                 \/ \* case4. peerLastZxid < minCommittedLog,
                    \*        send SNAP(lastProcessed) + StartForwarding
                    /\ ZxidComparePredicate(minCommittedLog, peerLastZxid)
                    /\ SendSyncMsgs(i, j, lastProcessedZxid, maxCommittedIdx,
                                          SNAP, needRemoveHead, maxCommittedLog)

\* compare state summary of two servers
IsMoreRecentThan(ss1, ss2) == \/ ss1.currentEpoch > ss2.currentEpoch
                              \/ /\ ss1.currentEpoch = ss2.currentEpoch
                                 /\ ZxidComparePredicate(ss1.lastZxid, ss2.lastZxid)

\* electionFinished in Leader
ElectionFinished(i, set) == /\ i \in set
                            /\ IsQuorum(set)

\* There may exist some follower shuts down and connects again, while
\* it has sent ACKEPOCH or updated currentEpoch last time. This means
\* sid of this follower has existed in elecingFollower but its info 
\* is old. So we need to make sure each sid in electingFollower is 
\* unique and latest(newest).
UpdateElecting(oldSet, sid, peerLastZxid, inQuorum) ==
        LET sid_electing == {s.sid: s \in oldSet }
        IN IF sid \in sid_electing 
           THEN LET old_info == CHOOSE info \in oldSet : info.sid = sid
                    follower_info == 
                             [ sid          |-> sid,
                               peerLastZxid |-> peerLastZxid,
                               inQuorum     |-> (inQuorum \/ old_info.inQuorum) ]
                IN (oldSet \ {old_info} ) \union {follower_info}
           ELSE LET follower_info == 
                             [ sid          |-> sid,
                               peerLastZxid |-> peerLastZxid,
                               inQuorum     |-> inQuorum ]
                IN oldSet \union {follower_info}

LeaderTurnToSynchronization(i) ==
        /\ currentEpoch' = [currentEpoch EXCEPT ![i] = acceptedEpoch[i]]
        /\ zabState'     = [zabState     EXCEPT ![i] = SYNCHRONIZATION]

(* Leader waits for receiving ACKEPOPCH from a quorum, and check whether it has most recent
   state summary from them. After this, leader's zabState turns to SYNCHRONIZATION.
   See waitForEpochAck in Leader for details. *)

LeaderProcessACKEPOCH(i, j) ==
        /\ IsON(i)
        /\ IsLeader(i)
        /\ PendingACKEPOCH(i, j)
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLearner(i, j)           
               leaderStateSummary   == [ currentEpoch |-> currentEpoch[i], 
                                         lastZxid     |-> lastProcessed[i].zxid ]
               followerStateSummary == [ currentEpoch |-> msg.mepoch,  
                                         lastZxid     |-> msg.mzxid ]
               logOk == \* whether follower is no more up-to-date than leader
                        ~IsMoreRecentThan(followerStateSummary, leaderStateSummary)
               electing_quorum == {e \in electing[i]: e.inQuorum = TRUE }
               sid_electing == {s.sid: s \in electing_quorum }
           IN /\ infoOk
              /\ \/ \* electionFinished = true, jump ouf of waitForEpochAck. 
                    \* Different from code, here we still need to record info
                    \* into electing, to help us perform syncFollower afterwards.
                    \* Since electing already meets quorum, it does not break
                    \* consistency between code and spec.
                    /\ ElectionFinished(i, sid_electing)
                    /\ electing' = [electing EXCEPT ![i] = UpdateElecting(@, j, msg.mzxid, FALSE) ]
                    /\ Discard(j, i)
                    /\ UNCHANGED <<state, zabState, currentEpoch, lastProcessed, hzxid, learners,
                                forwarding, connectInfo, epochLeader, daInv, electionVars>>
                 \/ /\ ~ElectionFinished(i, sid_electing)
                    /\ \/ /\ zabState[i] = DISCOVERY
                          /\ UNCHANGED daInv
                       \/ /\ zabState[i] /= DISCOVERY
                          /\ PrintT("Exception: electionFinished false," \o
                             " while zabState not DISCOVERY.")
                          /\ daInv' = [daInv EXCEPT !.stateConsistent = FALSE ]
                    /\ \/ /\ followerStateSummary.currentEpoch = -1
                          /\ electing' = [electing EXCEPT ![i] = UpdateElecting(@, j, 
                                                                msg.mzxid, FALSE) ]
                          /\ Discard(j, i)
                          /\ UNCHANGED <<state, zabState, currentEpoch, lastProcessed, hzxid, learners,
                                forwarding, connectInfo, epochLeader, electionVars>>
                       \/ /\ followerStateSummary.currentEpoch > -1
                          /\ \/ \* normal follower 
                                /\ logOk
                                /\ electing' = [electing EXCEPT ![i] = 
                                            UpdateElecting(@, j, msg.mzxid, TRUE) ]
                                /\ LET new_electing_quorum == {e \in electing'[i]: e.inQuorum = TRUE }
                                       new_sid_electing == {s.sid: s \in new_electing_quorum }
                                   IN 
                                   \/ \* electionFinished = true, jump out of waitForEpochAck,
                                      \* update currentEpoch and zabState.
                                      /\ ElectionFinished(i, new_sid_electing) 
                                      /\ LeaderTurnToSynchronization(i)
                                      /\ LET newLeaderEpoch == acceptedEpoch[i]
                                         IN epochLeader' = [epochLeader EXCEPT ![newLeaderEpoch]
                                                = @ \union {i} ] \* for checking invariants
                                   \/ \* there still exists electionFinished = false.
                                      /\ ~ElectionFinished(i, new_sid_electing)
                                      /\ UNCHANGED <<currentEpoch, zabState, epochLeader>>
                                /\ Discard(j, i)
                                /\ UNCHANGED <<state, lastProcessed, hzxid, connectInfo, learners, forwarding, electionVars>>
                             \/ \* Exists follower more recent than leader
                                /\ ~logOk 
                                /\ LeaderShutdown(i, {})
                                /\ UNCHANGED <<electing, epochLeader, currentEpoch>>
        /\ UNCHANGED <<servingState, acceptedEpoch, history, initialHistory, lastCommitted, lastSnapshot, disVars, ackldRecv, packetsSync, envVars, proposalMsgsLog>>
        /\ UpdateRecorder(<<"LeaderProcessACKEPOCH", i, j>>)
         

\* Strip syncFollower from LeaderProcessACKEPOCH.
\* Only when electionFinished = true and there exists some
\* learnerHandler has not perform syncFollower, this 
\* action will be called.
LeaderSyncFollower(i, j) == 
        /\ IsON(i)
        /\ IsLeader(i)
        /\ LET electing_quorum == {e \in electing[i]: e.inQuorum = TRUE }
               electionFinished == ElectionFinished(i, {s.sid: s \in electing_quorum } )
               toSync == {s \in electing[i] : /\ ~ZxidEqualPredicate( s.peerLastZxid, <<-1, -1>>)
                                              /\ s.sid \in learners[i] }
               canSync == toSync /= {}
           IN
           /\ electionFinished
           /\ canSync
           /\ \E s \in toSync: s.sid = j
           /\ LET chosen == CHOOSE s \in toSync: s.sid = j
                  newChosen == [ sid          |-> chosen.sid,
                                 peerLastZxid |-> <<-1, -1>>, \* <<-1,-1>> means has handled.
                                 inQuorum     |-> chosen.inQuorum ] 
              IN /\ SyncFollower(i, chosen.sid, chosen.peerLastZxid, FALSE)
                 /\ electing' = [electing EXCEPT ![i] = (@ \ {chosen}) \union {newChosen} ]
        /\ currentEpoch' = [currentEpoch EXCEPT ![i] = acceptedEpoch[i]]
        /\ UNCHANGED <<state, zabState, servingState, acceptedEpoch, initialHistory, lastCommitted, lastProcessed, hzxid, lastSnapshot, disVars, learners, ackldRecv, followerVars, electionVars, envVars, epochLeader, daInv>>
        /\ UpdateRecorder(<<"LeaderSyncFollower", i, j>>)
         

TruncateLog(his, index) == IF index <= 0 THEN << >>
                           ELSE SubSeq(his, 1, index)

(* Follower receives DIFF/TRUNC/SNAP, and then may receives PROPOSAL,COMMIT,NEWLEADER,
   and UPTODATE. See syncWithLeader in Learner for details. *)
FollowerProcessSyncMessage(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ rcvBuffer[j][i] /= << >>
        /\ \/ rcvBuffer[j][i][1].mtype = DIFF 
           \/ rcvBuffer[j][i][1].mtype = TRUNC
           \/ rcvBuffer[j][i][1].mtype = SNAP
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               stateOk == zabState[i] = SYNCHRONIZATION
           IN /\ infoOk
              /\ \/ \* Follower should receive packets in SYNC.
                    /\ ~stateOk
                    /\ PrintT("Exception: Follower receives DIFF/TRUNC/SNAP," \o
                             " whileZabState not SYNCHRONIZATION.")
                    /\ daInv' = [daInv EXCEPT !.stateConsistent = FALSE]
                    /\ UNCHANGED <<logVars, connectInfo>>
                 \/ /\ stateOk
                    /\ \/ /\ msg.mtype = DIFF   
                          /\ connectInfo' = [connectInfo EXCEPT ![i].syncMode = DIFF]                       
                          /\ UNCHANGED <<history, lastProcessed, lastCommitted>>
                          /\ initialHistory' = [initialHistory EXCEPT ![i] = history'[i]] 
                          /\ UNCHANGED <<daInv>>         
                       \/ /\ msg.mtype = TRUNC
                          /\ connectInfo' = [connectInfo EXCEPT ![i].syncMode = TRUNC]
                          /\ LET truncZxid == msg.mzxid
                                 truncIndex == TruncZxidToIndex(history[i], truncZxid)
                                 truncOk    == truncIndex <= Len(history[i])
                             IN
                             \/ /\ ~truncOk
                                /\ PrintT("Exception: TRUNC error.")
                                /\ daInv' = [daInv EXCEPT !.proposalConsistent = FALSE ]
                                /\ UNCHANGED <<history, initialHistory, lastProcessed, lastCommitted>>
                             \/ /\ truncOk
                                /\ history' = [history EXCEPT 
                                                    ![i] = TruncateLog(history[i], truncIndex)]
                                /\ initialHistory' = [initialHistory EXCEPT ![i] = history'[i]]
                                /\ lastProcessed' = [lastProcessed EXCEPT 
                                                    ![i] = [ index |-> truncIndex,
                                                             zxid  |-> truncZxid] ]
                                /\ UNCHANGED lastCommitted
                                /\ UNCHANGED <<daInv>>
                       \/ /\ msg.mtype = SNAP
                          /\ connectInfo' = [connectInfo EXCEPT ![i].syncMode = SNAP]
                          /\ LET index == Len(msg.msnapshot)
                             IN \/ /\ index = 0
                                   /\ history' = [history EXCEPT ![i] = msg.msnapshot] 
                                \/ /\ index > 0
                                   /\ history' = [history EXCEPT ![i] = msg.msnapshot, ![j][index]["ackSid"] = @ \union {i} ] 
                          /\ initialHistory' = [initialHistory EXCEPT ![i] = history'[i]]
                          /\ lastProcessed' = [lastProcessed EXCEPT 
                                                    ![i] = [ index |-> Len(history'[i]),
                                                             zxid  |-> msg.mzxid] ]
                          /\ UNCHANGED lastCommitted
                          /\ UNCHANGED <<daInv>>
        /\ Discard(j, i)
        /\ UNCHANGED <<lastSnapshot, hzxid, serverVars, leaderVars, packetsSync, electionVars, envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessSyncMessage", i, j, msg.mzxid, msg.mtype>>)
         

\* See variable snapshotNeeded in Learner for details.
SnapshotNeeded(i) == \/ connectInfo[i].syncMode = TRUNC
                     \/ connectInfo[i].syncMode = SNAP

\* See variable writeToTxnLog in Learner for details.
WriteToTxnLog(i) == IF \/ connectInfo[i].syncMode = DIFF
                       \/ connectInfo[i].nlRcv = TRUE
                    THEN TRUE ELSE FALSE
                    
\* See lastProposed in Leader for details.
LastProposed(i) == IF Len(history[i]) = 0 THEN [ index |-> 0, 
                                                 zxid  |-> <<0, 0>> ]
                   ELSE
                   LET lastIndex == Len(history[i])
                       entry     == history[i][lastIndex]
                   IN [ index |-> lastIndex,
                        zxid  |-> entry.zxid ]

LastQueued(i) == IF ~IsFollower(i) THEN LastProposed(i)
                 ELSE LET completeHis == history[i] \o packetsSync[i].notCommitted
                          totalLen == Len(completeHis)
                      IN IF totalLen = Len(history[i]) THEN LastProposed(i)
                         ELSE [ index |-> totalLen,
                                zxid  |-> completeHis[totalLen].zxid ]

IsNextZxid(curZxid, nextZxid) ==
            \/ \* first PROPOSAL in this epoch
               /\ nextZxid[2] = 1
               /\ curZxid[1] < nextZxid[1]
            \/ \* not first PROPOSAL in this epoch
               /\ nextZxid[2] > 1
               /\ curZxid[1] = nextZxid[1]
               /\ curZxid[2] + 1 = nextZxid[2]

FollowerProcessPROPOSALInSync(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingPROPOSAL(i, j)
        /\ zabState[i] = SYNCHRONIZATION
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               isNext == IsNextZxid(LastQueued(i).zxid, msg.mzxid)
               newTxn == [ zxid   |-> msg.mzxid,
                           value  |-> msg.mdata,
                           ackSid |-> {},    \* follower do not consider ackSid
                           epoch  |-> acceptedEpoch[i] ] \* epoch of this round
           IN /\ infoOk
              /\ \/ /\ isNext
                    /\ packetsSync' = [packetsSync EXCEPT ![i].notCommitted 
                                = Append(packetsSync[i].notCommitted, newTxn) ]
                    /\ UNCHANGED daInv
                 \/ /\ ~isNext
                    /\ PrintT("Warn: Follower receives PROPOSAL," \o
                        " while zxid != lastQueued + 1.")
                    /\ daInv' = [daInv EXCEPT !.proposalConsistent = FALSE ]
                    /\ UNCHANGED packetsSync
        \* logRequest -> SyncRequestProcessor -> SendAckRequestProcessor -> reply ack
        \* So here we do not need to send ack to leader.
        /\ Discard(j, i)
        /\ UNCHANGED <<serverVars, logVars, leaderVars, connectInfo, electionVars, 
                envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessPROPOSALInSync", i, j, msg.mzxid>>)
         

RECURSIVE IndexOfFirstTxnWithEpoch(_,_,_,_)
IndexOfFirstTxnWithEpoch(his, epoch, cur, end) == 
            IF cur > end THEN cur 
            ELSE IF his[cur].epoch = epoch THEN cur
                 ELSE IndexOfFirstTxnWithEpoch(his, epoch, cur + 1, end)

LastCommitted(i) == IF zabState[i] = BROADCAST THEN lastCommitted[i]
                    ELSE CASE IsLeader(i)   -> 
                            LET lastInitialIndex == Len(initialHistory[i])
                            IN IF lastInitialIndex = 0 THEN [ index |-> 0,
                                                              zxid  |-> <<0, 0>> ]
                               ELSE [ index |-> lastInitialIndex,
                                      zxid  |-> history[i][lastInitialIndex].zxid ]
                         []   IsFollower(i) ->
                            LET completeHis == history[i] \o packetsSync[i].notCommitted
                                packetsCommitted == packetsSync[i].committed
                                lenCommitted == Len(packetsCommitted)
                            IN IF lenCommitted = 0 \* return last one in history
                               THEN LET lastIndex == Len(history[i])
                                        lastInitialIndex == Len(initialHistory[i])
                                    IN IF lastIndex = lastInitialIndex
                                       THEN IF lastIndex = 0
                                            THEN [ index |-> 0,
                                                   zxid  |-> <<0, 0>> ]
                                            ELSE [ index |-> lastIndex ,
                                                   zxid  |-> history[i][lastIndex].zxid ]
                                       ELSE IF lastInitialIndex < lastCommitted[i].index
                                            THEN lastCommitted[i]
                                            ELSE IF lastInitialIndex = 0
                                                 THEN [ index |-> 0,
                                                        zxid  |-> <<0, 0>> ]
                                                 ELSE [ index |-> lastInitialIndex,
                                                        zxid  |-> history[i][lastInitialIndex].zxid ]
                               ELSE                \* return tail of packetsCommitted
                                    LET committedIndex == ZxidToIndex(completeHis, 
                                                     packetsCommitted[lenCommitted] )
                                    IN [ index |-> committedIndex, 
                                         zxid  |-> packetsCommitted[lenCommitted] ]
                         []   OTHER -> lastCommitted[i]
                         
TxnWithIndex(i, idx) == IF ~IsFollower(i) \/ zabState[i] /= SYNCHRONIZATION 
                        THEN history[i][idx]
                        ELSE LET completeHis == history[i] \o packetsSync[i].notCommitted
                             IN completeHis[idx]

FollowerProcessCOMMITInSync(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingCOMMIT(i, j)
        /\ zabState[i] = SYNCHRONIZATION
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               committedIndex == LastCommitted(i).index + 1
               exist == /\ committedIndex <= LastQueued(i).index
                        /\ IsNextZxid(LastCommitted(i).zxid, msg.mzxid)
               match == ZxidEqualPredicate(msg.mzxid, TxnWithIndex(i, committedIndex).zxid )
           IN /\ infoOk 
              /\ \/ /\ exist
                    /\ \/ /\ match
                          /\ LET writeToTxnLog == WriteToTxnLog(i)
                             IN
                             \/ /\ ~writeToTxnLog \* zk.processTxn() & packetsNotCommitted.remove()
                                /\ LET committedTxn == packetsSync[i].notCommitted[1]
                                   IN 
                                   /\ history' = [ history EXCEPT ![i] 
                                               = Append(@, committedTxn)]
                                   /\ lastCommitted' = [ lastCommitted EXCEPT ![i]
                                                     = [index |-> Len(history'[i]),
                                                        zxid  |-> committedTxn.zxid ] ]
                                   /\ lastProcessed' = [ lastProcessed EXCEPT ![i]
                                                     = lastCommitted'[i] ]
                                   /\ packetsSync' = [ packetsSync EXCEPT ![i].notCommitted
                                                   = Tail(@) ]
                             \/ /\ writeToTxnLog  \* packetsCommitted.add()
                                /\ packetsSync' = [ packetsSync EXCEPT ![i].committed
                                                = Append(packetsSync[i].committed, msg.mzxid) ]
                                /\ UNCHANGED <<history, lastCommitted, lastProcessed>>
                          /\ UNCHANGED daInv
                       \/ /\ ~match
                          /\ PrintT("Warn: Follower receives COMMIT," \o
                               " but zxid not the next committed zxid in COMMIT.")
                          /\ daInv' = [daInv EXCEPT !.commitConsistent = FALSE ]
                          /\ UNCHANGED <<history, lastCommitted, lastProcessed, packetsSync>>
                 \/ /\ ~exist
                    /\ PrintT("Warn: Follower receives COMMIT," \o
                         " but no packets with its zxid exists.")
                    /\ daInv' = [daInv EXCEPT !.commitConsistent = FALSE ]
                    /\ UNCHANGED <<history, lastCommitted, lastProcessed, packetsSync>>
        /\ Discard(j, i)
        /\ UNCHANGED <<serverVars, initialHistory, lastSnapshot, hzxid, leaderVars, connectInfo, electionVars, 
                envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessCOMMITInSync", i, j, msg.mzxid>>)

RECURSIVE ACKInBatches(_,_)
ACKInBatches(queue, packets) ==
        IF packets = << >> THEN queue
        ELSE LET head == packets[1]
                 newPackets == Tail(packets)
                 m_ack == [ mtype |-> ACK,
                            mzxid |-> head.zxid ]
             IN ACKInBatches( Append(queue, m_ack), newPackets )

(* Update currentEpoch, and logRequest every packets in
   packetsNotCommitted and clear it. As syncProcessor will 
   be called in logRequest, we have to reply acks here. *)
FollowerProcessNEWLEADER(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               packetsInSync == packetsSync[i].notCommitted
               m_ackld == [ mtype |-> ACK,
                            mzxid |-> msg.mzxid ]
               ms_ack  == ACKInBatches( << >>, packetsInSync )
               queue_toSend == <<m_ackld>> \o ms_ack \* send ACK-NEWLEADER first.
               \*    latest == IF lastProcessed[i].zxid[2] = 0 THEN LastProposed(i) ELSE lastProcessed[i]
           IN /\ infoOk
              /\ \/ /\ SnapshotNeeded(i)
                    /\ TakeSnapshot(i)
                 \/ /\ ~SnapshotNeeded(i)
                    /\ UNCHANGED <<lastSnapshot, daInv>>
              /\ currentEpoch' = [currentEpoch EXCEPT ![i] = acceptedEpoch[i] ]
              /\ connectInfo'  = [connectInfo  EXCEPT ![i].nlRcv = TRUE,
                                                      ![i].syncMode = NONE ]
              /\ servingState' = [servingState EXCEPT ![i] = INITIAL ]
              /\ history'      = [history      EXCEPT ![i] = @ \o packetsInSync ]
              /\ packetsSync'  = [packetsSync  EXCEPT ![i].notCommitted = << >> ]
              /\ lastCommitted' = [lastCommitted EXCEPT ![i] = lastProcessed[i]]
              /\ SendPackets(i, j, queue_toSend, TRUE)
        /\ UNCHANGED <<state, zabState, acceptedEpoch, initialHistory, lastProcessed, hzxid, 
                leaderVars, electionVars, envVars,verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessNEWLEADER", i, j, msg.mzxid>>)
        

\* quorumFormed in Leader
QuorumFormed(i, set) == i \in set /\ IsQuorum(set)

UpdateElectionVote(i, epoch) == TRUE
    \* UpdateProposal(i, currentVote[i].proposedLeader, currentVote[i].proposedZxid, epoch)

\* See startZkServer in Leader for details.
\* It is ok that set lastCommitted to lastProposed, since now leader just converts to
\* broadcast so it has not offer service.
StartZkServer(i) ==
        LET latest == LastProposed(i)
        IN /\ lastCommitted' = [lastCommitted EXCEPT ![i] = latest]
           /\ lastProcessed' = [lastProcessed EXCEPT ![i] = [ index |-> lastProcessed[i].index, 
                                                              zxid  |-> hzxid[i] ]]
           /\ lastSnapshot'  = [lastSnapshot  EXCEPT ![i] = latest]
           /\ UpdateElectionVote(i, acceptedEpoch[i])

LeaderTurnToBroadcast(i) ==
        /\ StartZkServer(i)
        /\ zabState' = [zabState EXCEPT ![i] = BROADCAST]
        /\ servingState' = [servingState EXCEPT ![i] = RUNNING]

TxnsWithPreviousEpoch(i) ==
            LET completeHis == IF ~IsFollower(i) \/ zabState[i] /= SYNCHRONIZATION 
                               THEN history[i] 
                               ELSE history[i] \o packetsSync[i].notCommitted
                end   == Len(completeHis)
                first == IndexOfFirstTxnWithEpoch(completeHis, acceptedEpoch[i], 1, end)
            IN IF first > end THEN completeHis
               ELSE SubSeq(completeHis, 1, first - 1)

TxnsRcvWithCurEpoch(i) ==
            LET completeHis == IF ~IsFollower(i) \/ zabState[i] /= SYNCHRONIZATION 
                               THEN history[i] 
                               ELSE history[i] \o packetsSync[i].notCommitted
                end   == Len(completeHis)
                first == IndexOfFirstTxnWithEpoch(completeHis, acceptedEpoch[i], 1, end)
            IN IF first > end THEN << >>
               ELSE SubSeq(completeHis, first, end) \* completeHis[first : end]

\* Txns received in current epoch but not committed.
\* See pendingTxns in FollowerZooKeeper for details.
PendingTxns(i) == IF ~IsFollower(i) \/ zabState[i] /= SYNCHRONIZATION 
                  THEN SubSeq(history[i], lastCommitted[i].index + 1, Len(history[i]))
                  ELSE LET packetsCommitted == packetsSync[i].committed
                           completeHis == history[i] \o packetsSync[i].notCommitted
                       IN IF Len(packetsCommitted) = 0 
                          THEN SubSeq(completeHis, Len(initialHistory[i]) + 1, Len(completeHis))
                          ELSE SubSeq(completeHis, LastCommitted(i).index + 1, Len(completeHis))

CommittedTxns(i) == IF ~IsFollower(i) \/ zabState[i] /= SYNCHRONIZATION 
                    THEN SubSeq(history[i], 1, lastCommitted[i].index)
                    ELSE LET packetsCommitted == packetsSync[i].committed
                             completeHis == history[i] \o packetsSync[i].notCommitted
                         IN IF Len(packetsCommitted) = 0 THEN initialHistory[i]
                            ELSE SubSeq( completeHis, 1, LastCommitted(i).index )

\* Each zxid of packetsCommitted equals to zxid of 
\* corresponding txn in txns.
RECURSIVE TxnsAndCommittedMatch(_,_)
TxnsAndCommittedMatch(txns, packetsCommitted) ==
        LET len1 == Len(txns)
            len2 == Len(packetsCommitted)
        IN IF len2 = 0 THEN TRUE 
           ELSE IF len1 < len2 THEN FALSE 
                ELSE /\ ZxidEqualPredicate(txns[len1].zxid, packetsCommitted[len2])
                     /\ TxnsAndCommittedMatch( SubSeq(txns, 1, len1 - 1), 
                                               SubSeq(packetsCommitted, 1, len2 - 1) )

FollowerLogRequestInBatches(i, leader, ms_ack, packetsNotCommitted) ==
        /\ history' = [history EXCEPT ![i] = @ \o packetsNotCommitted ]
        /\ SendPackets(i, leader, ms_ack, TRUE)

\* Since commit will call commitProcessor.commit, which will finally 
\* update lastProcessed, we update it here atomically.
FollowerCommitInBatches(i) ==
        LET committedTxns == CommittedTxns(i)
            packetsCommitted == packetsSync[i].committed
            match == TxnsAndCommittedMatch(committedTxns, packetsCommitted)
        IN 
        \/ /\ match 
           /\ lastCommitted' = [lastCommitted EXCEPT ![i] = LastCommitted(i)]
           /\ lastProcessed' = [lastProcessed EXCEPT ![i] = lastCommitted'[i]]
           /\ UNCHANGED daInv
        \/ /\ ~match
           /\ PrintT("Warn: Committing zxid without matched txn. /" \o 
                "Committing zxid != pending txn zxid.")
           /\ daInv' = [daInv EXCEPT !.commitConsistent = FALSE ]
           /\ UNCHANGED <<lastCommitted, lastProcessed>>

(* Follower jump out of outerLoop here, and log the stuff that came in
   between snapshot and uptodate, which means calling logRequest and 
   commit to clear packetsNotCommitted and packetsCommitted. *)
FollowerProcessUPTODATE(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingUPTODATE(i, j)
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               packetsNotCommitted == packetsSync[i].notCommitted
               m_ack  == [ mtype |-> ACK,
                           mzxid |-> <<currentEpoch[i], 0>> ]
               ms_ack == ACKInBatches(<< >>, packetsNotCommitted)
               queue_toSend == <<m_ack>> \o ms_ack \* send ACK-UPTODATE first.
           IN /\ infoOk
              /\ UpdateElectionVote(i, acceptedEpoch[i])
              /\ history' = [history EXCEPT ![i] = @ \o packetsNotCommitted ]
              /\ FollowerCommitInBatches(i)
              /\ packetsSync' = [packetsSync EXCEPT ![i].notCommitted = << >>,
                                                    ![i].committed = << >> ]
              /\ zabState' = [zabState EXCEPT ![i] = BROADCAST ]
              /\ servingState' = [servingState EXCEPT ![i] = RUNNING ]
              /\ SendPackets(i, j, queue_toSend, TRUE)
        /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, initialHistory, lastSnapshot, hzxid, leaderVars,
                connectInfo, electionVars, envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessUPTODATE", i, j, msg.mzxid>>)
         
-----------------------------------------------------------------------------
IncZxid(s, zxid) == IF currentEpoch[s] = zxid[1] THEN <<zxid[1], zxid[2] + 1>>
                    ELSE <<currentEpoch[s], 1>>

(* Leader receives client propose and broadcasts PROPOSAL. See processRequest
   in ProposalRequestProcessor and propose in Leader for details. Since 
   prosalProcessor.processRequest -> syncProcessor.processRequest ->
   ackProcessor.processRequest -> leader.processAck, we initially set 
   txn.ackSid = {i}, assuming we have done leader.processAck.
   Note: In production, any server in traffic can receive requests and 
         forward it to leader if necessary. We choose to let leader be
         the sole one who can receive write requests, to simplify spec 
         and keep correctness at the same time.
*)
LeaderProcessRequest(i) == 
        /\ CheckTransactionNum 
        /\ IsON(i)
        /\ IsLeader(i)
        /\ zabState[i] = BROADCAST
        /\ LET inBroadcast == {s \in forwarding[i]: zabState[s] = BROADCAST} \union {i}
           IN IsQuorum(inBroadcast)
        /\ LET request_value == GetRecorder("nClientRequest") \* unique value
            \*    newZxid == IncZxid(i, LastProposed(i).zxid)
               newHzxid == <<hzxid[i][1], hzxid[i][2] + 1>>
               newTxn == [ zxid   |-> newHzxid,
                           value  |-> request_value, 
                           ackSid |-> {i}, \* assume we have done leader.processAck
                           epoch  |-> acceptedEpoch[i] ]
               m_proposal == [ mtype |-> PROPOSAL,
                               mzxid |-> newTxn.zxid,
                               mdata |-> request_value ]
               m_proposal_for_checking == [ source |-> i,
                                            epoch  |-> acceptedEpoch[i],
                                            zxid   |-> newTxn.zxid,
                                            data   |-> request_value ]
           IN /\ history' = [history EXCEPT ![i] = Append(@, newTxn) ]
              /\ \/ /\ ShouldSnapshot(i)
                    /\ TakeSnapshot(i)
                 \/ /\ ~ShouldSnapshot(i)
                    /\ UNCHANGED <<lastSnapshot, daInv>>
              /\ hzxid' = [hzxid EXCEPT ![i] = newHzxid]
              /\ Broadcast(i, i, m_proposal, FALSE)
              /\ proposalMsgsLog' = proposalMsgsLog \union {m_proposal_for_checking}
        /\ UNCHANGED <<serverVars, initialHistory, lastCommitted, lastProcessed, leaderVars,
                followerVars, electionVars, envVars, epochLeader>>
        /\ LET len == Len(history'[i])
               newZxid == history'[i][len].zxid 
           IN UpdateRecorder(<<"LeaderProcessRequest", i, newZxid>>)
         

(* Follower processes PROPOSAL in BROADCAST. See processPacket
   in Follower for details. *)
FollowerProcessPROPOSAL(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingPROPOSAL(i, j)
        /\ zabState[i] = BROADCAST
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               isNext == IsNextZxid( LastQueued(i).zxid, msg.mzxid)
               newTxn == [ zxid   |-> msg.mzxid,
                           value  |-> msg.mdata,
                           ackSid |-> {},
                           epoch  |-> acceptedEpoch[i] ]
               m_ack  == [ mtype |-> ACK,
                           mzxid |-> msg.mzxid ]
          IN /\ infoOk 
             /\ \/ /\ isNext
                   /\ \/ /\ ShouldSnapshot(i)
                         /\ TakeSnapshot(i)
                      \/ /\ ~ShouldSnapshot(i)
                         /\ UNCHANGED <<lastSnapshot, daInv>>
                \/ /\ ~isNext
                   /\ PrintT("Exception: Follower receives PROPOSAL, while" \o 
                        " the transaction is not the next.")
                   /\ daInv' = [daInv EXCEPT !.proposalConsistent = FALSE ]
                   /\ UNCHANGED <<lastSnapshot>>
             /\ history' = [history EXCEPT ![i] = Append(@, newTxn)]
             /\ Reply(i, j, m_ack)
        /\ UNCHANGED <<serverVars, initialHistory, lastCommitted, lastProcessed, hzxid, leaderVars,
                followerVars, electionVars, envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessPROPOSAL", i, j, msg.mzxid>>)
         

\* See outstandingProposals in Leader
OutstandingProposals(i) == IF zabState[i] /= BROADCAST THEN << >>
                           ELSE SubSeq( history[i], lastCommitted[i].index + 1,
                                 Len(history[i]) )

LastAckIndexFromFollower(i, j) == 
        LET set_index == {idx \in 1..Len(history[i]): j \in history[i][idx].ackSid }
        IN Maximum(set_index)

\* See commit in Leader for details.
LeaderCommit(s, follower, index, zxid) ==
        /\ lastCommitted' = [lastCommitted EXCEPT ![s] = [ index |-> index,
                                                           zxid  |-> zxid ] ]
        /\ LET m_commit == [ mtype |-> COMMIT,
                             mzxid |-> zxid ]
           IN Broadcast(s, follower, m_commit, TRUE)

\* Try to commit one operation, called by LeaderProcessAck.
\* See tryToCommit in Leader for details.
\* commitProcessor.commit -> processWrite -> toBeApplied.processRequest
\* -> finalProcessor.processRequest, finally processTxn will be implemented
\* and lastProcessed will be updated. So we update it here.
LeaderTryToCommit(s, index, zxid, newTxn, follower) ==
        LET allTxnsBeforeCommitted == lastCommitted[s].index >= index - 1
                    \* Only when all proposals before zxid has been committed,
                    \* this proposal can be permitted to be committed.
            hasAllQuorums == IsQuorum(newTxn.ackSid)
                    \* In order to be committed, a proposal must be accepted
                    \* by a quorum.
            ordered == lastCommitted[s].index + 1 = index
                    \* Commit proposals in order.
        IN \/ /\ \* Current conditions do not satisfy committing the proposal.
                 \/ ~allTxnsBeforeCommitted
                 \/ ~hasAllQuorums
              /\ Discard(follower, s)
              /\ UNCHANGED <<daInv, lastCommitted, lastProcessed>>
           \/ /\ allTxnsBeforeCommitted
              /\ hasAllQuorums
              /\ \/ /\ ~ordered
                    /\ PrintT("Warn: Committing zxid " \o ToString(zxid) \o " not first.")
                    /\ daInv' = [daInv EXCEPT !.commitConsistent = FALSE]
                 \/ /\ ordered
                    /\ UNCHANGED daInv
              /\ LeaderCommit(s, follower, index, zxid)
              /\ lastProcessed' = [lastProcessed EXCEPT ![s] = [ index |-> index,
                                                                 zxid  |-> zxid ] ]

RECURSIVE LeaderUpdateAckSid(_,_,_,_,_)
LeaderUpdateAckSid(ackSid, first, last, oldHis, newHis) ==
    IF first > last THEN newHis \o SubSeq(oldHis, last + 1, Len(oldHis))
    ELSE LET txn == oldHis[first]
             txnAfterAddAck == [ zxid   |-> txn.zxid,
                                 value  |-> txn.value,
                                 ackSid |-> txn.ackSid \union {ackSid} ,
                                 epoch  |-> txn.epoch ]
         IN LeaderUpdateAckSid(ackSid, first + 1, last, oldHis, Append(newHis, txnAfterAddAck))

(* Leader Keeps a count of acks for a particular proposal, and try to
   commit the proposal. See case Leader.ACK in LearnerHandler,
   processRequest in AckRequestProcessor, and processAck in Leader for
   details. *)
LeaderProcessACK(i, j) ==
        /\ IsON(i)
        /\ IsLeader(i)
        /\ PendingACK(i, j)
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLearner(i, j)
               match  == ZxidEqualPredicate(msg.mzxid, <<acceptedEpoch[i], 0>>)
               m_uptodate == [ mtype |-> UPTODATE,
                               mzxid |-> <<acceptedEpoch[i], 0>> ] \* not important
               sid_ackldRecv == {a.sid: a \in ackldRecv[i]}
               inAckldRecv == j \in sid_ackldRecv
               ackUptodate == msg.mzxid[2] = 0
               outstanding == LastCommitted(i).index < LastProposed(i).index
                        \* outstandingProposals not null
               hasCommitted == ~ZxidComparePredicate( msg.mzxid, LastCommitted(i).zxid)
                        \* namely, lastCommitted >= zxid
               index == ZxidToIndex(history[i], msg.mzxid)
               exist == index >= 1 /\ index <= LastProposed(i).index
                        \* the proposal exists in history
            \*    ackIndex == LastAckIndexFromFollower(i, j)
            \*    monotonicallyInc == \/ ackIndex = -1
            \*                        \/ ackIndex + 1 = index
                        \* TCP makes everytime ackIndex should just increase by 1
           IN /\ infoOk 
              /\ \/ /\ ~QuorumFormed(i, sid_ackldRecv) 
                    /\ ~inAckldRecv
                    \* May be fake ACKLD here.
                    /\ ackldRecv' = [ackldRecv EXCEPT ![i] = UpdateConnectingOrAckldRecv(@, j) ]
                    \* /\ history' = [history EXCEPT ![i] = LeaderUpdateAckSid(j, 1, Len(history[j]), history[i], << >>) ] 
                    /\ UNCHANGED <<history>>
                    /\ \/ /\ match
                          /\ LET new_sid_ackldRecv == {a.sid: a \in ackldRecv'[i]}
                             IN
                             \/ \* jump out of waitForNewLeaderAck, and do startZkServer,
                                \* setZabState, and reply UPTODATE.
                                /\ QuorumFormed(i, new_sid_ackldRecv)
                                /\ LeaderTurnToBroadcast(i)
                                /\ BroadcastUPTODATE(i, j, m_uptodate, TRUE)
                             \/ \* still wait in waitForNewLeaderAck.
                                /\ ~QuorumFormed(i, new_sid_ackldRecv)
                                /\ Discard(j, i)
                                /\ UNCHANGED <<zabState, servingState, lastCommitted, lastProcessed, lastSnapshot>>
                          /\ UNCHANGED daInv
                       \/ /\ ~match
                          /\ PrintT("Error: not expected NEWLEADER ACK!")
                          /\ daInv' = [daInv EXCEPT !.ackConsistent = FALSE ]
                          /\ Discard(j, i)
                          /\ UNCHANGED <<zabState, servingState, lastCommitted, lastProcessed, lastSnapshot>>
                 \/ /\ QuorumFormed(i, sid_ackldRecv) 
                    /\ ~inAckldRecv
                    /\ ackldRecv' = [ackldRecv EXCEPT ![i] = UpdateConnectingOrAckldRecv(@, j) ]
                    /\ Reply(i, j, m_uptodate)
                    \* /\ history' = [history EXCEPT ![i] = LeaderUpdateAckSid(j, 1, Len(history[j]), history[i], << >>) ] 
                    /\ UNCHANGED <<history>>
                    /\ UNCHANGED <<zabState, servingState, lastCommitted, lastProcessed, lastSnapshot, daInv>>
                 \/ /\ QuorumFormed(i, sid_ackldRecv) 
                    /\ inAckldRecv
                    /\ UNCHANGED <<ackldRecv, zabState, servingState, lastSnapshot>>
                    /\ \/ /\ ackUptodate
                          /\ Discard(j, i)
                          /\ UNCHANGED <<history, lastCommitted, lastProcessed>>
                          /\ LET committedIdx == IndexOfZxidHelper(history[i], msg.mzxid, 1, Len(history[i]))
                                 committedMatch == LastCommitted(j).index >= committedIdx
                             IN \/ /\ ~committedMatch
                                   /\ PrintT("Exception: follower's lastProcessedZxid is not up-to-date! ")
                                   /\ daInv' = [daInv EXCEPT !.stateConsistent = FALSE ]
                                \/ /\ committedMatch
                                   /\ UNCHANGED daInv
                       \/ /\ ~ackUptodate
                          /\ exist
                        \*   /\ monotonicallyInc
                          /\ LET txn == history[i][index]
                                 txnAfterAddAck == [ zxid   |-> txn.zxid,
                                                     value  |-> txn.value,
                                                     ackSid |-> txn.ackSid \union {j} ,
                                                     epoch  |-> txn.epoch ]   
                             IN \* p.addAck(sid)
                             /\ history' = [history EXCEPT ![i][index] = txnAfterAddAck ] 
                             /\ \/ /\ \* Note: outstanding is 0. 
                                      \* / proposal has already been committed.
                                      \/ ~outstanding
                                      \/ hasCommitted
                                   /\ Discard(j, i)
                                   /\ UNCHANGED <<lastCommitted, lastProcessed, daInv>>
                                \/ /\ outstanding
                                   /\ ~hasCommitted
                                   /\ LeaderTryToCommit(i, index, msg.mzxid, txnAfterAddAck, j)
                       \/ /\ ~ackUptodate
                          /\ ~exist
                            \*  \/ ~monotonicallyInc
                          /\ PrintT("Exception: No such zxid. " \o 
                                 " / ackIndex doesn't inc monotonically.")
                          /\ daInv' = [daInv EXCEPT !.ackConsistent = FALSE ]
                          /\ Discard(j, i)
                          /\ UNCHANGED <<ackldRecv, zabState, servingState, history, lastCommitted, lastProcessed, lastSnapshot>>
        /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, initialHistory, hzxid, disVars, learners, electing, forwarding, followerVars, electionVars, envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN  UpdateRecorder(<<"LeaderProcessACK", i, j, msg.mzxid>>)
         

(* Follower processes COMMIT in BROADCAST. See processPacket
   in Follower for details. *)
FollowerProcessCOMMIT(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingCOMMIT(i, j)
        /\ zabState[i] = BROADCAST
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               pendingTxns == PendingTxns(i)
               noPending == Len(pendingTxns) = 0
           IN
           /\ infoOk  
           /\ \/ /\ noPending
                 /\ PrintT("Warn: Committing zxid without seeing txn.")
                 /\ UNCHANGED <<lastCommitted, lastProcessed, daInv>>
              \/ /\ ~noPending
                 /\ LET firstElementZxid == pendingTxns[1].zxid
                        match == ZxidEqualPredicate(firstElementZxid, msg.mzxid)
                    IN 
                    \/ /\ ~match
                       /\ PrintT("Exception: Committing zxid not equals" \o
                                " next pending txn zxid.")
                       /\ daInv' = [daInv EXCEPT !.commitConsistent = FALSE]
                       /\ UNCHANGED <<lastCommitted, lastProcessed>>
                    \/ /\ match
                       /\ lastCommitted' = [lastCommitted EXCEPT 
                                ![i] = [ index |-> lastCommitted[i].index + 1,
                                         zxid  |-> firstElementZxid ] ]
                       /\ lastProcessed' = [lastProcessed EXCEPT 
                                ![i] = [ index |-> lastCommitted[i].index + 1,
                                         zxid  |-> firstElementZxid ] ]
                       /\ UNCHANGED daInv
        /\ Discard(j, i)
        /\ UNCHANGED <<serverVars, history, initialHistory, lastSnapshot, hzxid, leaderVars, followerVars,
                electionVars, envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN  UpdateRecorder(<<"FollowerProcessCOMMIT", i, j, msg.mzxid>>)
        

-----------------------------------------------------------------------------
(* Used to discard some messages which should not exist in network channel.
   This action should not be triggered. *)
FilterNonexistentMessage(i) ==
        /\ \E j \in Server \ {i}: /\ rcvBuffer[j][i] /= << >>
                                  /\ LET msg == rcvBuffer[j][i][1]
                                     IN 
                                        \/ /\ IsLeader(i)
                                           /\ LET infoOk == IsMyLearner(i, j)
                                              IN
                                              \/ msg.mtype = LEADERINFO
                                              \/ msg.mtype = NEWLEADER
                                              \/ msg.mtype = UPTODATE
                                              \/ msg.mtype = PROPOSAL
                                              \/ msg.mtype = COMMIT
                                              \/ /\ ~infoOk
                                                 /\ \/ msg.mtype = FOLLOWERINFO
                                                    \/ msg.mtype = ACKEPOCH
                                                    \/ msg.mtype = ACKLD
                                                    \/ msg.mtype = ACK
                                        \/ /\ IsFollower(i)
                                           /\ LET infoOk == IsMyLeader(i, j) 
                                              IN
                                              \/ msg.mtype = FOLLOWERINFO
                                              \/ msg.mtype = ACKEPOCH
                                              \/ msg.mtype = ACKLD
                                              \/ msg.mtype = ACK
                                              \/ /\ ~infoOk
                                                 /\ \/ msg.mtype = LEADERINFO
                                                    \/ msg.mtype = NEWLEADER
                                                    \/ msg.mtype = UPTODATE
                                                    \/ msg.mtype = PROPOSAL
                                                    \/ msg.mtype = COMMIT   
                                        \/ IsLooking(i)
                                  /\ Discard(j, i)
        /\ daInv' = [daInv EXCEPT !.messageLegal = FALSE ]
        /\ UNCHANGED <<serverVars, logVars, leaderVars, followerVars, electionVars,
                envVars, verifyVars>>
        /\ UnchangeRecorder      
           

-----------------------------------------------------------------------------
\* Next
BaseNext ==
        (* Set initial state *) 
        \/ /\ recorder["step"] = 0
           /\ SetInitState
           /\ UpdateAfterAction
        \/ /\ recorder["step"] > 0
           /\ AfterActionCheck
           /\ DuringActionCheck
           /\ 
              (* FLE module *)
              \/ \E i \in Server, S \in Quorums: Election(i, S) 
              \/ \E i, j \in Server: FollowLeader(i, j)
              (* Zab - Discovery *)
              \/ \E i, j \in Server: ConnectAndFollowerSendFOLLOWERINFO(i, j)
              \/ \E i, j \in Server: LeaderProcessFOLLOWERINFO(i, j)
              \/ \E i, j \in Server: FollowerProcessLEADERINFO(i, j)
              \/ \E i, j \in Server: LeaderProcessACKEPOCH(i, j)
              (* Zab - Synchronization *)
              \/ \E i, j \in Server: LeaderSyncFollower(i, j)
              \/ \E i, j \in Server: FollowerProcessSyncMessage(i, j)
              \/ \E i, j \in Server: FollowerProcessPROPOSALInSync(i, j)
              \/ \E i, j \in Server: FollowerProcessCOMMITInSync(i, j)
              \/ \E i, j \in Server: FollowerProcessNEWLEADER(i, j)
              \/ \E i, j \in Server: FollowerProcessUPTODATE(i, j)
              (* Zab - Broadcast *)
              \/ \E i \in Server:    LeaderProcessRequest(i)
              \/ \E i, j \in Server: FollowerProcessPROPOSAL(i, j)
              \/ \E i, j \in Server: LeaderProcessACK(i, j) \* Sync + Broadcast
              \/ \E i, j \in Server: FollowerProcessCOMMIT(i, j)
              (* Filter redundant messages in network *)
              \/ \E i \in Server:    FilterNonexistentMessage(i)
              (* Failures like node crash and network partition *)
              \/ \E i, j \in Server: PartitionStart(i, j)
              \/ \E i, j \in Server: PartitionRecover(i, j)
              \/ \E i \in Server:    NodeCrash(i)
              \/ \E i \in Server:    NodeStart(i)
           /\ UpdateAfterAction

BaseSpec == BaseInit /\ [][BaseNext]_baseVars

=============================================================================
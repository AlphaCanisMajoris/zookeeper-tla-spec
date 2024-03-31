----------------------------- MODULE zk_pr_2152 -----------------------------
(* 
    Specification for verifying the code fix in 
        https://github.com/apache/zookeeper/pull/2152
    Targeting: Jira 3023, 4394, 4643, 4646 & 4685 in ZooKeeper. 
*)

EXTENDS zk_test_thread

-----------------------------------------------------------------------------
\* VARIABLES

varsFix == <<coreVars, threadVars>>

-----------------------------------------------------------------------------

InitFix == /\ CoreInit
           /\ InitThreadVars

-----------------------------------------------------------------------------
\* Utils
RECURSIVE packetsToCommitInSync(_,_,_)
packetsToCommitInSync(packets, ZxidsToCommit, selected) ==
        IF ZxidsToCommit = << >> THEN <<packets, selected>>
        ELSE IF packets = << >> THEN packetsToCommitInSync(<< >>, Tail(ZxidsToCommit), selected)
        ELSE LET firstZxidToCommit == ZxidsToCommit[1]
                 firstPacket == packets[1]
                 match == TxnZxidEqual(firstPacket, firstZxidToCommit)
             IN IF ~match
                THEN packetsToCommitInSync(packets, Tail(ZxidsToCommit), selected)
                ELSE packetsToCommitInSync(Tail(packets), Tail(ZxidsToCommit), Append(selected, firstPacket))

\* See lastProposed in Leader for details.
LastNewProposed(i) == IF Len(history'[i]) = 0 THEN [ index |-> 0, 
                                                     zxid  |-> <<0, 0>> ]
                      ELSE
                      LET lastIndex == Len(history'[i])
                          entry     == history'[i][lastIndex]
                      IN [ index |-> lastIndex,
                           zxid  |-> entry.zxid ]

FollowerSyncAndCommitInitialLogEntries(i) ==
        LET packets == packetsSync[i].notCommitted
            ZxidsToCommit == packetsSync[i].committed
            packetsLeftAndToCommit == packetsToCommitInSync(packets, ZxidsToCommit, << >>)
            packetsLeft == packetsLeftAndToCommit[1]
            packetsToCommit == packetsLeftAndToCommit[2]
        IN /\ history' =  [history EXCEPT ![i] = @ \o packetsToCommit]
           /\ initialHistory' =  [initialHistory EXCEPT ![i] = history'[i]]
           /\ lastCommitted' = [lastCommitted EXCEPT ![i] = LastNewProposed(i) ] 
           /\ lastProcessed' = [lastProcessed EXCEPT ![i] = lastCommitted'[i]]
           /\ packetsSync'  = [packetsSync EXCEPT ![i] = [ notCommitted |-> packetsLeft, 
                                                           committed |-> << >> ]]
           /\ UNCHANGED <<queuedRequests, committedRequests>>

-----------------------------------------------------------------------------
\* Fix in https://github.com/apache/zookeeper/pull/2152

(* Persist and commit requests according to "packetsCommitted". *)
FollowerProcessNEWLEADER_pr2152_1(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ currentEpoch[i] /= acceptedEpoch[i]
        /\ connectInfo[i].nlRcv = FALSE
        /\ LET infoOk == IsMyLeader(i, j)
           IN /\ infoOk
              /\ \/ /\ SnapshotNeeded(i)
                    /\ TakeSnapshot(i)
                 \/ /\ ~SnapshotNeeded(i)
                    /\ UNCHANGED <<lastSnapshot, daInv>>
              /\ FollowerSyncAndCommitInitialLogEntries(i)
              /\ connectInfo'  = [ connectInfo  EXCEPT ![i].nlRcv = TRUE ]
              /\ UNCHANGED currentEpoch
              /\ UNCHANGED <<servingState>>
        /\ UNCHANGED <<rcvBuffer>> 
        /\ UNCHANGED <<state, zabState, acceptedEpoch, hzxid, leaderVars, electionVars, envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessNEWLEADER_pr2152_1", i, j, msg.mzxid>>)
        /\ UpdateAfterAction 

(* Update currentEpoch after persisting committed history. *)
FollowerProcessNEWLEADER_pr2152_2(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ currentEpoch[i] /= acceptedEpoch[i]
        /\ connectInfo[i].nlRcv = TRUE
        /\ UNCHANGED <<lastSnapshot, daInv>>
        /\ currentEpoch' = [currentEpoch EXCEPT ![i] = acceptedEpoch[i] ]
        /\ servingState' = [servingState EXCEPT ![i] = INITIAL ]
        /\ connectInfo'  = [connectInfo  EXCEPT ![i].syncMode = NONE ]
        /\ UNCHANGED <<history, initialHistory, lastCommitted, lastProcessed, packetsSync, queuedRequests, committedRequests>>
        /\ UNCHANGED <<rcvBuffer>> 
        /\ UNCHANGED <<state, zabState, acceptedEpoch, hzxid, leaderVars, electionVars, envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessNEWLEADER_pr2152_2", i, j, msg.mzxid>>)
        /\ UpdateAfterAction 

(* Reply ACK-NEWLEADER at last of processing NEWLEADER. *)
FollowerProcessNEWLEADER_pr2152_3(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ currentEpoch[i] = acceptedEpoch[i]
        /\ connectInfo[i].nlRcv = TRUE
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               m_ackld == [ mtype |-> ACK,
                            mzxid |-> msg.mzxid ]
           IN /\ infoOk
              /\ Reply(i, j, m_ackld)
        /\ UNCHANGED <<currentEpoch, queuedRequests, connectInfo, packetsSync>>
        /\ UNCHANGED <<state, zabState, servingState, acceptedEpoch, initialHistory, lastCommitted, lastProcessed, lastSnapshot, hzxid, committedRequests, history, leaderVars, electionVars, envVars, verifyVars, daInv>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessNEWLEADER_pr2152_3", i, j, msg.mzxid>>)
        /\ UpdateAfterAction  

-----------------------------------------------------------------------------

Shutdown_fix(S, crashSet) ==
        /\ state'          = [s \in Server |-> IF s \in S THEN LOOKING ELSE state[s] ]
        /\ zabState'      = [s \in Server |-> IF s \in S THEN ELECTION ELSE zabState[s] ]
        /\ servingState'  = [s \in Server |-> IF s \in S THEN SHUTDOWN ELSE servingState[s] ]
        /\ connectInfo'   = [s \in Server |-> IF s \in S THEN InitialConnectInfo ELSE connectInfo[s] ]
        /\ CleanInputBuffer(S)
        \* If SyncRequestProcessor starts, it logs all pending txns if not crashed
        /\ history' = [s \in Server |-> 
                        LET inCluster == s \in S
                            inCrashSet == s \in crashSet
                            syncProcessorReady == servingState[s] /= SHUTDOWN
                            pengdingProposal == \/ queuedRequests[s] /= << >>
                                                \/ packetsSync[s].notCommitted /= << >>
                        IN IF /\ inCluster 
                              /\ ~inCrashSet
                              /\ syncProcessorReady
                              /\ pengdingProposal
                              /\ IsLeader(s) \* Actually Leader's SyncRequestProcessor is not modeled in this spec, so its queuedRequests[s] and packetsSync[s].notCommitted are empty
                           THEN history[s] \o queuedRequests[s] \o packetsSync[s].notCommitted
                           ELSE history[s] ]
        /\ initialHistory' = [s \in Server |-> IF s \in S THEN history'[s] 
                                                ELSE initialHistory[s] ]
        /\ lastCommitted' = [s \in Server |-> IF s \in S THEN [ index |-> 0, zxid  |-> <<0, 0>> ] 
                                                         ELSE lastCommitted[s] ] 
        \* clear volatile data
        \* TODO: 
        /\ queuedRequests' = [s \in Server |-> IF s \in S THEN << >> ELSE queuedRequests[s] ]
        /\ committedRequests' = [s \in Server |-> IF s \in S THEN << >>
                                                             ELSE committedRequests[s] ]
        /\ packetsSync' = [s \in Server |-> IF s \in S THEN [ notCommitted |-> << >>,
                                                              committed |-> << >> ]
                                                       ELSE packetsSync[s] ]
        /\ lastProcessed' = [s \in Server |-> IF s \in S THEN InitLastProcessed(s)
                                                         ELSE lastProcessed[s] ]
        \* see ZooKeeperServer.loadData()
        /\ hzxid' = [s \in Server |-> IF s \in S THEN lastProcessed'[s].zxid ELSE hzxid[s]]
        
FollowerShutdown_fix(i, isCrash) ==
        /\ state'           = [state        EXCEPT ![i] = LOOKING]
        /\ zabState'        = [zabState     EXCEPT ![i] = ELECTION]
        /\ servingState'    = [servingState EXCEPT ![i] = SHUTDOWN]
        /\ connectInfo'     = [connectInfo  EXCEPT ![i] = InitialConnectInfo]
        /\ lastCommitted' = [lastCommitted EXCEPT ![i] = [ index |-> 0,
                                                           zxid  |-> <<0, 0>> ] ]
        \* If SyncRequestProcessor starts, it logs all pending txns if not crashed
        /\ history' = [history EXCEPT ![i] = 
                        IF \/ isCrash 
                           \/ servingState[i] = SHUTDOWN 
                           \/ /\ queuedRequests[i] = << >>
                              /\ packetsSync[i].notCommitted = << >>
                        THEN @ 
                        ELSE @ \o queuedRequests[i] \o packetsSync[i].notCommitted ]
        /\ initialHistory' =  [initialHistory EXCEPT ![i] = history'[i]]
        \* SyncRequestProcessor will process this synchronously
        /\ queuedRequests' = [queuedRequests EXCEPT ![i] = << >>]
        \* CommitProcessor will process this synchronously
        /\ committedRequests' = [committedRequests EXCEPT ![i] = << >>]
        /\ packetsSync' = [packetsSync EXCEPT ![i].notCommitted = << >>, 
                                              ![i].committed = << >>]
        \* in version 3.7+, lastProcessed will be modified when turning to LOOKING
        /\ lastProcessed' = [lastProcessed EXCEPT ![i] = InitLastProcessed(i)]
        /\ hzxid' = [hzxid EXCEPT ![i] = lastProcessed'[i].zxid]

LeaderShutdown_fix(i, crashSet) ==
        /\ LET cluster == {i} \union learners[i]
           IN Shutdown_fix(cluster, crashSet)
        /\ learners'   = [learners   EXCEPT ![i] = {}]
        /\ forwarding' = [forwarding EXCEPT ![i] = {}]
        /\ leaderOracle' = NullPoint

PartitionStart_fix(i, j) == 
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
                       /\ FollowerShutdown_fix(j, FALSE)
                       /\ Clean(i, j)
                       /\ UNCHANGED electionVars
                    \/ /\ ~IsQuorum(newCluster)   \* leader switches to looking
                       /\ LeaderShutdown_fix(i, {})
                       /\ UNCHANGED <<electing, connecting, ackldRecv>>
           \/ /\ IsLooking(i) 
              /\ IsLooking(j)
              /\ IdComparePredicate(i, j) \* to compress state space
              /\ UNCHANGED <<threadVars>>
              /\ UNCHANGED <<state, zabState, servingState, lastProcessed, hzxid, connecting, noDisVars,
                             history, initialHistory, lastCommitted, connectInfo, packetsSync, netVars, electionVars>>
        /\ partition' = [partition EXCEPT ![i][j] = TRUE, ![j][i] = TRUE ]
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, lastSnapshot, tempMaxEpoch, status, verifyVars, daInv>>
        /\ UpdateRecorder(<<"PartitionStart", i, j>>)

NodeCrash_fix(i) ==
        /\ CheckExternalEventExecute(<<"NodeCrash", i>>)
        /\ CheckCrash(i)
        /\ IsON(i)
        /\ status' = [status EXCEPT ![i] = OFFLINE ]
        /\ \/ /\ IsLooking(i)
              /\ UNCHANGED <<threadVars>>
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
                             /\ FollowerShutdown_fix(i, TRUE)
                             /\ Clean(leader, i)
                             /\ UNCHANGED electionVars
                          \/ /\ ~IsQuorum(newCluster)
                             /\ LeaderShutdown_fix(leader, {i})
                             /\ UNCHANGED <<electing, connecting, ackldRecv>>
                    \/ /\ ~connectedWithLeader 
                       /\ FollowerShutdown_fix(i, TRUE)
                       /\ CleanInputBuffer({i})
                       /\ UNCHANGED <<connecting, noDisVars, electionVars>>
           \/ /\ IsLeader(i)
              /\ LeaderShutdown_fix(i, {i})
              /\ UNCHANGED <<connecting, electing, ackldRecv>>
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, lastSnapshot, tempMaxEpoch, partition, verifyVars, daInv>>
        /\ UpdateRecorder(<<"NodeCrash", i>>)

-----------------------------------------------------------------------------
\* Next
NextFix == 
        (* Set initial state *) 
        \/ /\ recorder["step"] = 0
           /\ SetInitState
           /\ UpdateAfterAction
        \/ /\ recorder["step"] > 0
           /\ AfterActionCheck
           /\ DuringActionCheck
           /\
              (* FLE and Discovery *)
              \/ \E i \in Server, S \in Quorums: ElectionAndDiscovery(i, S)
              (* Zab - Synchronization *)
              \/ \E i, j \in Server: LeaderSyncFollower(i, j)
              \/ \E i, j \in Server: FollowerProcessSyncMessage(i, j)
              \/ \E i, j \in Server: FollowerProcessPROPOSALInSync(i, j)
              \/ \E i, j \in Server: FollowerProcessCOMMITInSync(i, j)
              \/ \E i, j \in Server: FollowerProcessNEWLEADER_pr2152_1(i, j)
              \/ \E i, j \in Server: FollowerProcessNEWLEADER_pr2152_2(i, j)
              \/ \E i, j \in Server: FollowerProcessNEWLEADER_pr2152_3(i, j)
              \/ \E i, j \in Server: FollowerProcessUPTODATE(i, j)
              (* Zab - Broadcast *)
              \/ \E i \in Server:    LeaderProcessRequest(i)
              \/ \E i, j \in Server: FollowerProcessPROPOSAL(i, j)
              \/ \E i, j \in Server: LeaderProcessACK(i, j) \* Sync + Broadcast
              \/ \E i, j \in Server: FollowerProcessCOMMIT(i, j)
              (* Internal event: save a request to disk and reply ack, commit a request *)
              \/ \E i, j \in Server: FollowerSyncProcessorLogRequest(i, j)
              \/ \E i, j \in Server: FollowerCommitProcessorCommit(i, j)
              (* Filter redundant messages in network *)
              \/ \E i \in Server:    FilterNonexistentMessage(i)
              (* Failures like node crash and network partition *)
              \/ \E i, j \in Server: PartitionStart_fix(i, j)
              \/ \E i, j \in Server: PartitionRecover(i, j)
              \/ \E i \in Server:    NodeCrash_fix(i)
              \/ \E i \in Server:    NodeStart(i)
           /\ UpdateAfterAction

SpecFix == InitFix /\ [][NextFix]_varsFix

=============================================================================
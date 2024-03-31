----------------------------- MODULE pr_2111 -----------------------------
(* 
    Specification for verifying the code fix in 
        https://github.com/apache/zookeeper/pull/2111 
*)

EXTENDS zk_test_thread

-----------------------------------------------------------------------------
\* VARIABLES

VARIABLE requestsToAck

vars2111 == <<coreVars, threadVars, requestsToAck>>

-----------------------------------------------------------------------------

Init2111 == /\ CoreInit
            /\ InitThreadVars
            /\ requestsToAck = [v \in Server |-> << >>] 

-----------------------------------------------------------------------------
(* log Requests. *)
FollowerProcessNEWLEADER_pr2111_1(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ currentEpoch[i] /= acceptedEpoch[i]
        /\ connectInfo[i].nlRcv = FALSE
        /\ LET infoOk == IsMyLeader(i, j)
               packetsInSync == packetsSync[i].notCommitted
           IN /\ infoOk
              /\ \/ /\ SnapshotNeeded(i)
                    /\ TakeSnapshot(i)
                 \/ /\ ~SnapshotNeeded(i)
                    /\ UNCHANGED <<lastSnapshot, daInv>>
              /\ connectInfo'  = [connectInfo  EXCEPT ![i].nlRcv = TRUE,
                                                      ![i].syncMode = NONE ]
              /\ servingState' = [servingState EXCEPT ![i] = INITIAL ]
            \* persist all pending txns in packetsSync[i].notCommitted to disk
            \* Need to keep all pending acks
              /\ history'      = [history      EXCEPT ![i] = @ \o packetsInSync ]
              /\ requestsToAck' = [requestsToAck EXCEPT ![i] = ACKInBatches( << >>, packetsInSync)]
              /\ packetsSync'  = [packetsSync  EXCEPT ![i].notCommitted = << >> ]
              /\ lastCommitted' = [lastCommitted EXCEPT ![i] = lastProcessed[i]]
              /\ UNCHANGED currentEpoch
              /\ UNCHANGED <<initialHistory, lastProcessed, queuedRequests, committedRequests>>
        /\ UNCHANGED <<rcvBuffer>> 
        /\ UNCHANGED <<state, zabState, acceptedEpoch, hzxid, leaderVars, electionVars, envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessNEWLEADER_pr2111_1", i, j, msg.mzxid>>)
        /\ UpdateAfterAction 

(* Update currentEpoch. *)
FollowerProcessNEWLEADER_pr2111_2(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ currentEpoch[i] /= acceptedEpoch[i]
        /\ connectInfo[i].nlRcv = TRUE
        /\ UNCHANGED <<lastSnapshot, daInv>>
        /\ currentEpoch' = [currentEpoch EXCEPT ![i] = acceptedEpoch[i] ]
        /\ UNCHANGED <<connectInfo, servingState, requestsToAck>>
        /\ UNCHANGED <<history, initialHistory, lastCommitted, lastProcessed, packetsSync, queuedRequests, committedRequests>>
        /\ UNCHANGED <<rcvBuffer>> 
        /\ UNCHANGED <<state, zabState, acceptedEpoch, hzxid, leaderVars, electionVars, envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessNEWLEADER_pr2111_2", i, j, msg.mzxid>>)
        /\ UpdateAfterAction 

(* Reply ACK-NEWLEADER at last of processing NEWLEADER. *)
FollowerProcessNEWLEADER_pr2111_3(i, j) ==
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
        /\ UNCHANGED requestsToAck
        /\ UNCHANGED <<currentEpoch, queuedRequests, connectInfo, packetsSync>>
        /\ UNCHANGED <<state, zabState, servingState, acceptedEpoch, initialHistory, lastCommitted, lastProcessed, lastSnapshot, hzxid, committedRequests, history, leaderVars, electionVars, envVars, verifyVars, daInv>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessNEWLEADER_pr2111_3", i, j, msg.mzxid>>)
        /\ UpdateAfterAction  

FollowerProcessUPTODATE_pr2111(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingUPTODATE(i, j)
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               packetsNotCommitted == packetsSync[i].notCommitted
               packetsCommitted == packetsSync[i].committed
               m_ack  == [ mtype |-> ACK,
                           mzxid |-> <<currentEpoch[i], 0>> ]
               queue_toSend == <<m_ack>> \o requestsToAck[i]
           IN /\ infoOk
              /\ servingState' = [servingState EXCEPT ![i] = RUNNING ]
              /\ UpdateElectionVote(i, acceptedEpoch[i])
              /\ queuedRequests' = [queuedRequests EXCEPT ![i] = @ \o packetsNotCommitted ]
              /\ committedRequests' = [committedRequests EXCEPT ![i] = @ \o packetsCommitted ]
              /\ packetsSync' = [packetsSync EXCEPT ![i].notCommitted = << >>,
                                                    ![i].committed = << >> ]
              /\ zabState' = [zabState EXCEPT ![i] = BROADCAST ]
              /\ requestsToAck' = [requestsToAck EXCEPT ![i] =  << >>]
              /\ SendPackets(i, j, queue_toSend, TRUE)
              /\ UNCHANGED <<daInv>>
        /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, initialHistory, lastSnapshot, hzxid, leaderVars,
                connectInfo, electionVars, envVars, verifyVars>>
        /\ UNCHANGED <<history, lastCommitted, lastProcessed, hzxid>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessUPTODATE_pr2111", i, j, msg.mzxid>>)
-----------------------------------------------------------------------------
\* Next
Next2111 == 
        (* Set initial state *) 
        \/ /\ recorder["step"] = 0
           /\ SetInitState
           /\ UpdateAfterAction 
           /\ UNCHANGED requestsToAck
        \/ /\ recorder["step"] > 0
           /\ AfterActionCheck
           /\ DuringActionCheck
           /\
              (* FLE and Discovery *)
              \/ \E i \in Server, S \in Quorums: ElectionAndDiscovery(i, S) 
              (* Zab - Synchronization-part 1 *)
              \/ \E i, j \in Server: LeaderSyncFollower(i, j)
              \/ \E i, j \in Server: FollowerProcessSyncMessage(i, j)
              \/ \E i, j \in Server: FollowerProcessPROPOSALInSync(i, j)
              \/ \E i, j \in Server: FollowerProcessCOMMITInSync(i, j)
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
              \/ \E i, j \in Server: PartitionStart(i, j)
              \/ \E i, j \in Server: PartitionRecover(i, j)
              \/ \E i \in Server:    NodeCrash(i)
              \/ \E i \in Server:    NodeStart(i)
           /\ UNCHANGED requestsToAck
           /\ UpdateAfterAction
        \/ /\ recorder["step"] > 0
           /\ AfterActionCheck
           /\ DuringActionCheck
           /\
              (* Zab - Synchronization-part 2 *)
              \/ \E i, j \in Server: FollowerProcessNEWLEADER_pr2111_1(i, j)
              \/ \E i, j \in Server: FollowerProcessNEWLEADER_pr2111_2(i, j)
              \/ \E i, j \in Server: FollowerProcessNEWLEADER_pr2111_3(i, j)
              \/ \E i, j \in Server: FollowerProcessUPTODATE_pr2111(i, j)
           /\ UpdateAfterAction

Spec2111 == Init2111 /\ [][Next2111]_vars2111

=============================================================================
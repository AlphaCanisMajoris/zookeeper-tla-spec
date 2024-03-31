----------------------------- MODULE zk_atom --------------------------------
(* 
    Specification targeting non-atomic updates during sync in ZooKeeper 3.7+. 
*)

EXTENDS zk_test_sync

-----------------------------------------------------------------------------
atomVars == <<coreVars>>

-----------------------------------------------------------------------------   
AtomTypeOK == CoreTypeOK

----------------------------------------------------------------------------- 
AtomInit == CoreInit

----------------------------------------------------------------------------- 
FollowerProcessPROPOSALInSync_refined(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingPROPOSAL(i, j)
        /\ zabState[i] = SYNCHRONIZATION
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
            \*    isNext == IsNextZxid(LastQueued(i).zxid, msg.mzxid)
               newTxn == [ zxid   |-> msg.mzxid,
                           value  |-> msg.mdata,
                           ackSid |-> {},    \* follower do not consider ackSid
                           epoch  |-> acceptedEpoch[i] ] \* epoch of this round
           IN /\ infoOk
              /\ packetsSync' = [packetsSync EXCEPT ![i].notCommitted 
                                = Append(packetsSync[i].notCommitted, newTxn) ]
              /\ UNCHANGED daInv
            \*   /\ \/ /\ isNext
            \*         /\ packetsSync' = [packetsSync EXCEPT ![i].notCommitted 
            \*                     = Append(packetsSync[i].notCommitted, newTxn) ]
            \*         /\ UNCHANGED daInv
            \*      \/ /\ ~isNext
            \*         /\ PrintT("Warn: Follower receives PROPOSAL," \o
            \*             " while zxid != lastQueued + 1.")
            \*         /\ daInv' = [daInv EXCEPT !.proposalConsistent = FALSE ]
            \*         /\ UNCHANGED packetsSync
        \* logRequest -> SyncRequestProcessor -> SendAckRequestProcessor -> reply ack
        \* So here we do not need to send ack to leader.
        /\ Discard(j, i)
        /\ UNCHANGED <<serverVars, logVars, leaderVars, connectInfo, electionVars, 
                envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessPROPOSALInSync_refined", i, j, msg.mzxid>>)

FollowerProcessCOMMITInSync_refined(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingCOMMIT(i, j)
        /\ zabState[i] = SYNCHRONIZATION
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               committedIndex == LastCommitted(i).index + 1
               existNotCommitted == Len(packetsSync[i].notCommitted) > 0 
           IN /\ infoOk 
              /\ \/ /\ ~existNotCommitted 
                    /\ PrintT("Error: Follower receives COMMIT during SYNC," \o
                               " but packetsNotCommitted is empty!")
                    /\ daInv' = [daInv EXCEPT !.commitConsistent = FALSE ]
                    /\ UNCHANGED <<history, lastCommitted, lastProcessed, packetsSync>>
                 \/ /\ existNotCommitted 
                    /\ UNCHANGED daInv
                    /\ LET writeToTxnLog == WriteToTxnLog(i)
                           committedTxn == packetsSync[i].notCommitted[1]
                           matchNotCommitted == ZxidEqualPredicate(msg.mzxid, committedTxn.zxid) 
                       IN \/ /\ ~writeToTxnLog \* zk.processTxn() & packetsNotCommitted.remove()
                             /\ \/ /\ ~matchNotCommitted
                                   /\ UNCHANGED <<history, lastCommitted, lastProcessed, packetsSync>>
                                \/ /\ matchNotCommitted
                                   /\ history' = [ history EXCEPT ![i] 
                                               = Append(@, committedTxn)]
                                   /\ lastCommitted' = [ lastCommitted EXCEPT ![i]
                                                     = [index |-> Len(history'[i]),
                                                        zxid  |-> committedTxn.zxid ] ]
                                   /\ lastProcessed' = [ lastProcessed EXCEPT ![i] = lastCommitted'[i] ]
                                   /\ packetsSync' = [ packetsSync EXCEPT ![i].notCommitted = Tail(@) ]
                          \/ /\ writeToTxnLog  \* packetsCommitted.add()
                             /\ packetsSync' = [ packetsSync EXCEPT ![i].committed
                                             = Append(packetsSync[i].committed, msg.mzxid) ]
                             /\ UNCHANGED <<history, lastCommitted, lastProcessed>>
        /\ Discard(j, i)
        /\ UNCHANGED <<serverVars, initialHistory, lastSnapshot, hzxid, leaderVars, connectInfo, electionVars, 
                envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessCOMMITInSync_refined", i, j, msg.mzxid>>) 

(* Update currentEpoch. *)
FollowerUpdateCurrentEpoch(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ currentEpoch[i] /= acceptedEpoch[i]
        /\ LET infoOk == IsMyLeader(i, j)
           IN /\ infoOk
              /\ \/ /\ SnapshotNeeded(i)
                    /\ TakeSnapshot(i)
                 \/ /\ ~SnapshotNeeded(i)
                    /\ UNCHANGED <<lastSnapshot, daInv>>
              /\ currentEpoch' = [currentEpoch EXCEPT ![i] = acceptedEpoch[i] ]
              /\ connectInfo'  = [connectInfo  EXCEPT ![i].nlRcv = TRUE,
                                                      ![i].syncMode = NONE ]
              /\ servingState' = [servingState EXCEPT ![i] = INITIAL ]
        /\ UNCHANGED <<history, packetsSync, rcvBuffer>> 
        /\ UNCHANGED <<state, zabState, acceptedEpoch, initialHistory, lastCommitted, lastProcessed, hzxid, 
                leaderVars, electionVars, envVars, verifyVars>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerUpdateCurrentEpoch", i, j, msg.mzxid>>)
         

(* logRequest every packets in packetsNotCommitted and clear it. 
   As syncProcessor will be called in logRequest, 
   we reply acks here. *)
FollowerProcessNEWLEADERAfterCurrentEpochUpdated(i, j) ==
        /\ IsON(i)
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ currentEpoch[i] = acceptedEpoch[i]
        /\ servingState[i] = INITIAL
        /\ LET msg == rcvBuffer[j][i][1]
               infoOk == IsMyLeader(i, j)
               packetsInSync == packetsSync[i].notCommitted
               m_ackld == [ mtype |-> ACK,
                            mzxid |-> msg.mzxid ]
               ms_ack  == ACKInBatches( << >>, packetsInSync )
               queue_toSend == <<m_ackld>> \o ms_ack \* send ACK-NEWLEADER first.
           IN /\ infoOk
              /\ history'      = [history      EXCEPT ![i] = @ \o packetsInSync ]
              /\ packetsSync'  = [packetsSync  EXCEPT ![i].notCommitted = << >> ]
              /\ SendPackets(i, j, queue_toSend, TRUE)
        /\ UNCHANGED <<lastSnapshot, daInv, currentEpoch, connectInfo, servingState>> 
        /\ UNCHANGED <<state, zabState, servingState, acceptedEpoch, initialHistory, lastCommitted, lastProcessed, hzxid, leaderVars, electionVars, envVars,verifyVars, daInv>>
        /\ LET msg == rcvBuffer[j][i][1]
           IN UpdateRecorder(<<"FollowerProcessNEWLEADERAfterCurrentEpochUpdated", i, j, msg.mzxid>>)
         

-----------------------------------------------------------------------------
\* Next
AtomNext == 
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
              \/ \E i, j \in Server: FollowerProcessPROPOSALInSync_refined(i, j)
              \/ \E i, j \in Server: FollowerProcessCOMMITInSync_refined(i, j)
              \/ \E i, j \in Server: FollowerUpdateCurrentEpoch(i, j)
              \/ \E i, j \in Server: FollowerProcessNEWLEADERAfterCurrentEpochUpdated(i, j)
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

AtomSpec == AtomInit /\ [][AtomNext]_atomVars

=============================================================================
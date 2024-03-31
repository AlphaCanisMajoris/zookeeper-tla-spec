----------------------------- MODULE zk_sync --------------------------------
(* Specification targeting log replication in ZooKeeper 3.7+. *)

EXTENDS zk_core

-----------------------------------------------------------------------------
syncVars == <<coreVars>>

-----------------------------------------------------------------------------   
SyncTypeOK == CoreTypeOK

-----------------------------------------------------------------------------
SyncInit == CoreInit       

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
\* ld: leader, fs: set of followers
UpdateStateToPhaseSync(ld, fs) ==
        /\ state'          = [s \in Server |-> IF s = ld THEN LEADING 
                                               ELSE IF s \in fs THEN FOLLOWING 
                                                                ELSE state[s] ]
        /\ zabState'       = [s \in Server |-> IF s = ld \/ s \in fs THEN SYNCHRONIZATION
                                                                     ELSE zabState[s] ]
        /\ initialHistory' = [s \in Server |-> IF s = ld THEN InitHistory(s)
                                               ELSE IF s \in fs THEN history[s] 
                                                                ELSE initialHistory[s] ]
        /\ UNCHANGED <<lastProcessed>>
        /\ LET S == {ld} \union fs
               finalTempMaxEpoch == Maximum({acceptedEpoch[s]: s \in S }) + 1 
           IN 
           acceptedEpoch'  = [s \in Server |-> IF s \in S THEN finalTempMaxEpoch
                                                          ELSE acceptedEpoch[s] ]
        \* initialize leader
        /\ currentEpoch'   = [currentEpoch EXCEPT ![ld] = acceptedEpoch'[ld]]
        /\ history'        = [history      EXCEPT ![ld] = InitHistory(ld) ]
        /\ learners'       = [learners     EXCEPT ![ld] = {ld} \union fs ]
        /\ connecting'     = [connecting   EXCEPT ![ld] = { [ sid       |-> ld,
                                                              connected |-> TRUE ] } 
                                                            \union UpdateConnectingHelper(fs) ]
        /\ electing'       = [electing     EXCEPT ![ld] = { [ sid          |-> ld,
                                                              peerLastZxid |-> <<-1,-1>>,
                                                              inQuorum     |-> TRUE ] }
                                                            \union UpdateElectingHelper(fs, TRUE) ]
        /\ ackldRecv'      = [ackldRecv    EXCEPT ![ld] = { [ sid       |-> ld,
                                                              connected |-> TRUE ] }]
        /\ forwarding'     = [forwarding   EXCEPT ![ld] = {} ]   
        /\ LET newEpoch == acceptedEpoch'[ld]
           IN /\ tempMaxEpoch' = [tempMaxEpoch EXCEPT ![ld] = newEpoch]
              /\ hzxid'        = [hzxid        EXCEPT ![ld] = <<newEpoch, 0>>]
              /\ epochLeader'  = [epochLeader  EXCEPT ![newEpoch] = @ \union {ld}] 
        \* initialize follower
        /\ packetsSync'    = [s \in Server |-> IF s \in fs THEN [notCommitted |-> << >>,
                                                                 committed    |-> << >> ]
                                                           ELSE packetsSync[s] ]
        /\ connectInfo'   = [s \in Server |-> IF s \in fs THEN SetConnectInfo(ld, NONE, FALSE) ELSE connectInfo[s] ]

\* Since now we do not care bugs in election and discovery, here we merge all actions in 
\* these two modules into one action.
ElectionAndDiscovery(i, S) ==
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
        /\ UpdateStateToPhaseSync(i, S\{i})
        \* Election and connection finished, then complete discovery
        /\ UNCHANGED <<servingState, lastCommitted, lastSnapshot,
                       netVars, envVars, proposalMsgsLog, daInv>>
        /\ UpdateRecorder(<<"ElectionAndDiscovery", i, S\{i}, currentEpoch[i], lastProcessed'[i], currentEpoch'[i]  >>)
         
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
\* Next
SyncNext == 
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

SyncSpec == SyncInit /\ [][SyncNext]_syncVars

=============================================================================
----------------------- MODULE ViewStampedReplication -----------------------
\* NOTE - All optimization are tagged with OPT#Num

\* NOTE - For ensuring weak fairness conditions by just declaring it on VRNext as below (to stop infinite stuttering), we require
\* each sub step (in VRNext) to be disabled ("not enabled") in case it has already been executed and rexecuting it will not change
\* the state.
\*      Declaration as follows - WF_vars(VRNext)
\*
\* If the sub-step is left enabled after execution, TLC will allow behaviours that stutter at this sub-step (making it difficult
\* to debug if certain states are eventually reached when adding new functionality in the spec). A workaround to avoiding this is
\* would be to declare weak fairness on each sub-step (as below), but that is cumbersome for two reasons -
\*   1. Required changing the fairness condition when new steps are added, old ones renamed/removed.
\*   2. If a sub-step has a parameters (say process id), then we have to specify WF conditions for all possible sub-steps as below.
\*
\*      Workaround declaration is as follows - \A p_id \in NumProcesses: WF_vars(sendPrepares(p_id)) /\ WF_vars(sendPrepares(p_id)) and so on...
\*
\* This trick is called the WfSimplifier in the spec to succinctly point out conditions added for exactly just this purpose.

\* TODOs -
\*   1. Test VR with flexible quorums (just for fun to check if the spec still works fine)?
\*   2. Reconfiguration protocol
\*   3. Run TLC with a rogue process to prove that it is easy to break correctness with byzantine failures.
\*   4. Allow state transfer (catch-up)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT
    \* The total number of processes; Index of each process falls in 0..NumProcesses-1
    NumProcesses,

    \* ClientCommands is a set of distinct client commands. The specification doesn't bother to maintain a client table as
    \* mentioned in the paper as it is not relevant to the correctness of the core consensus algorithm - which is to arrive
    \* at a specific order for the client commands in presence of failures. The client table is essential to maintain exactly
    \* once semantics of client requests which is an orthogonal problem to consensus.
    ClientCommands,

    \* The maximum view number any process in any bhaviour can attain (this is to restrict the allowed behaviours that TLC
    \* scans through). This can also be enforced by specifying a State Constraint when running TLC.
    MaxViewNum,

    \* Maximum number of process failures allowed in the behaviour (this is again to restrict the allowed behaviours that TLC
    \* scans through).
    MaxFailures

VARIABLES
    (* A set of message records. Refer the VRTypeOk invariant to understand the format of this variable. *)
    messages,

    (* A function mapping process ids to their record. Refer the VRTypeOk invariant to understand the format of this variable. *)
    processState,

    (*
        This is used to check that every behaviour conforms with some intended behaviour specified by the LinearizableOrdering spec.

        For this, the ordering variable needs to be updated on every step to reflect the ordering of executed commands
        visible to an external user.
    *)
    ordering

vars == <<messages, processState, ordering>>

PossibleLogSeqences(S) ==
    {possible_seq \in UNION {
        [1..n -> S] : n \in 0..Cardinality(S)}:
            (\A a, b \in 1..Len(possible_seq):
                (a = b \/ possible_seq[a] # possible_seq[b]))}

VRTypeOk ==
    /\ processState \in [0..NumProcesses-1 -> [
        view_num : 0..MaxViewNum,
        commit_num: 0..Cardinality(ClientCommands),
        status: {"normal", "view_change", "do_view_change_sent", "recovering"},
        last_active_view_num: 0..MaxViewNum,
        log: PossibleLogSeqences(ClientCommands),
        nonce: 0..MaxFailures]]
    /\ messages \in SUBSET (UNION {
        [type: {"PREPARE"}, \* No "to" field as it is a broadcast msg. No "from" as view_num is enough to identify the sender
         cmd: ClientCommands,
         view_num: 0..MaxViewNum,
         commit_num: 0..Cardinality(ClientCommands),
         log_num: 0..Cardinality(ClientCommands)
        ],
        [type: {"PREPAREOK"}, \* No "to" field as view_num is enough to identify the receiver
         from: 0..NumProcesses-1,
         view_num: 0..MaxViewNum,
         log_num: 0..Cardinality(ClientCommands)
        ],
        [type: {"COMMIT"}, \* No "to" field as it is a broadcast msg. No "from" as view_num is enough to identify the sender
         view_num: 0..MaxViewNum,
         commit_num: 0..Cardinality(ClientCommands)
        ],
        [type: {"START-VIEW-CHANGE"}, \* No "to" field as it is a broadcast msg
         from: 0..NumProcesses-1,
         view_num: 0..MaxViewNum
        ],
        [type: {"DO-VIEW-CHANGE"}, \* No "to" field as view_num is enough to identify the receiver
         from: 0..NumProcesses-1,
         view_num: 0..MaxViewNum,
         log: PossibleLogSeqences(ClientCommands),
         commit_num: 0..Cardinality(ClientCommands),
         last_active_view_num: 0..MaxViewNum
        ],
        [type: {"START-VIEW"}, \* No "from" field as view_num is enough to identify the sender. Also, no "to" field as it is a
                               \* broadcast message.
         log: PossibleLogSeqences(ClientCommands),
         view_num: 0..MaxViewNum,
         commit_num: 0..Cardinality(ClientCommands)
        ],
        [type: {"RECOVERY"},
         from: 0..NumProcesses-1,
         nonce: 0..MaxFailures
        ],
        [type: {"RECOVERYRESPONSE"},
         from: 0..NumProcesses-1,
         to: 0..NumProcesses-1,
         view_num: 0..MaxViewNum,
         commit_num: 0..Cardinality(ClientCommands),
         log: PossibleLogSeqences(ClientCommands),
         nonce: 0..MaxFailures
        ],
        [type: {"RECOVERYRESPONSE"},
         from: 0..NumProcesses-1,
         to: 0..NumProcesses-1,
         view_num: 0..MaxViewNum,
         nonce: 0..MaxFailures
        ]})

(* Utility operators *)

Maximum(S) ==
    IF S = {} THEN 0
    ELSE CHOOSE x \in S: \A y \in S: x >= y

Pick(S) == CHOOSE s \in S : TRUE
RECURSIVE SetReduce(_, _, _)

\* When running TLC on large models, comment the assertion for checking commutativity.
SetReduce(Op(_, _), S, value) ==
  IF S = {} THEN value
  ELSE LET s == Pick(S)
       IN IF Op(s, value) = Op(value, s)
       THEN SetReduce(Op, S \ {s}, Op(s, value))
       ELSE Assert(FALSE, "oh no")

Sum(S) ==
    LET _op(a, b) == a + b
    IN SetReduce(_op, S, 0)

\* Fetch a subset of messages in the network based on the params filter.
subsetOfMsgs(params) ==
    {log_entry \in messages: \A field \in DOMAIN params:
        field \in DOMAIN log_entry /\ log_entry[field] = params[field]}

\* isLeader return True if p thinks it is the leader.
isLeader(p) == processState[p].view_num % NumProcesses = p

sendMsgs(msgs) == messages' = messages \cup msgs

(* Normal case operation *)
sendPrepares(p) ==
    \E cmd \in ClientCommands: (
       /\ (
           LET set[i \in 0..Len(processState[p].log)] ==
                 IF i = 0 THEN {}
                 ELSE set[i-1] \cup {processState[p].log[i]}
           IN ~ (cmd \in set[Len(processState[p].log)]))
       /\ processState' = [processState EXCEPT ![p].log = Append(processState[p].log, cmd)]
       /\ sendMsgs(
               {
                   [type |-> "PREPARE",
                    cmd |-> cmd,
                    view_num |-> processState[p].view_num,
                    commit_num |-> processState[p].commit_num,
                    log_num |-> Len(processState[p].log)+1]
               }
            )
     )

sendCommits(p) ==
      /\ subsetOfMsgs(
            [type |-> "COMMIT", view_num |-> processState[p].view_num,
             commit_num |-> processState[p].commit_num]) = {} \* WfSimplifier condition
      /\ sendMsgs(
            {
                [type |-> "COMMIT",
                 view_num |-> processState[p].view_num,
                 commit_num |-> processState[p].commit_num]
            }
          )

\* Check if there are atleast NumProcesses/2 PREPAREOKs. Note that there is an implicit self PREPAREOK which completes the majority.
majorityPREPAREOKs(p, log_num) ==
    LET mset == {
            msg \in messages: /\ msg.type = "PREPAREOK"
              /\ msg.view_num = processState[p].view_num
              /\ msg.log_num = log_num
       }
    IN Cardinality(mset) >= NumProcesses \div 2

acceptPrepare(p) ==
    \E msg \in messages:
        /\ msg.type = "PREPARE"
        /\ processState[p].view_num = msg.view_num
        /\ Len(processState[p].log) = msg.log_num - 1
        /\ processState' = [processState EXCEPT ![p].log = Append(processState[p].log, msg.cmd),
             ![p].commit_num = Maximum({msg.commit_num, processState[p].commit_num})] \* The commit_num on the process
                 \* might be > the commit_num in the message. Similar to the case when an older leader receives a
                 \* START-VIEW message. Refer updateBasedOnStartView step.
        /\ sendMsgs({
                        [type |-> "PREPAREOK",
                         from |-> p,
                         view_num |-> processState[p].view_num,
                         log_num |-> Len(processState[p].log)+1]
                    })

acceptCommit(p) == \E msg \in messages:
                     /\ msg.type = "COMMIT"
                     /\ processState[p].view_num = msg.view_num
                     /\ Len(processState[p].log) >= msg.commit_num
                     /\ processState[p].commit_num < msg.commit_num
                     /\ processState' = [processState EXCEPT ![p].commit_num = msg.commit_num]

(* View change steps *)
sendStartViewChange(p, new_view_num) ==
    /\ new_view_num > processState[p].view_num
    /\ processState' = [processState EXCEPT ![p].status = "view_change",
                                            ![p].view_num = new_view_num]
    /\ sendMsgs({
          [type |-> "START-VIEW-CHANGE",
           from |-> p,
           view_num |-> new_view_num]
       })

sendDoViewChange(p) == sendMsgs({
    [
        type |-> "DO-VIEW-CHANGE",
        from |-> p,
        view_num |-> processState[p].view_num,
        log |-> processState[p].log,
        commit_num |-> processState[p].commit_num,
        last_active_view_num |-> processState[p].last_active_view_num
    ]})

updateBasedOnStartView(p, msg) ==
    /\ processState' = [processState EXCEPT ![p].status = "normal",
          ![p].commit_num = Maximum({msg.commit_num, processState[p].commit_num}), \* It might happen that the process p was a leader before
                \* and has commit_num greater than that in the START-VIEW message.
          ![p].log = msg.log, \* msg.log will surely be >= Maximum(msg.commit_num, processState[p].commit_num) in length.
          ![p].last_active_view_num = msg.view_num,
          ![p].view_num = msg.view_num]
    /\ \* Send PREPAREOKs for uncommitted entries.
        sendMsgs(
            [type: {"PREPAREOK"},
             from: {p},
             view_num: {msg.view_num},
             log_num: (msg.commit_num+1)..Len(msg.log)])

viewChangeTransitions(p) ==
      \/ (
            /\ ~(processState[p].status = "view_change")
            /\ (
                    \* Timer triggered view change. Can't be done by node which thinks its the leader.
                    /\ ~isLeader(p)
                    /\ processState[p].view_num+1 <= MaxViewNum
                    /\ sendStartViewChange(p, processState[p].view_num+1)
               )
         )
      \/ (
            \* Wait for majority to say view_change and then perform DO-VIEW-CHANGE
            /\ processState[p].status = "view_change"
            /\ LET mset == {
                        msg \in messages: /\ msg.type = "START-VIEW-CHANGE"
                                          /\ msg.view_num = processState[p].view_num
                                          /\ msg.from # p
                    }
               IN Cardinality(mset) >= NumProcesses \div 2
            /\ sendDoViewChange(p)
            /\ processState' = [processState EXCEPT ![p].status = "do_view_change_sent"]
         )
      \/ (
            \* In view_change status, but got view_change with higher number.
            \* Got larger start_view_change msg from another node.
            \E msg \in messages:
               /\ msg.type = "START-VIEW-CHANGE"
               /\ msg.view_num > processState[p].view_num
               /\ sendStartViewChange(p, msg.view_num)
         )
      \/ (
            \* In case a start_view msg is received
            /\ (
                  \/ (
                      /\ \E msg \in messages: msg.type = "START-VIEW" /\ msg.view_num > processState[p].view_num
                          /\ updateBasedOnStartView(p, msg)
                     )
                  \/ (
                      \* TODO - Find the invariant to check the case where "normal" wasn't checked when updating with start_view
                      \* message of same view_num
                      /\ ~(processState[p].status = "normal")
                      /\ \E msg \in messages: msg.type = "START-VIEW" /\ msg.view_num = processState[p].view_num
                          /\ updateBasedOnStartView(p, msg)
                     )
               )
            /\ UNCHANGED <<>>
         )

\* There is no "to" field in start_view as it is for all replicas.
sendStartView(p, v, maxLogMsg) == sendMsgs(
                                    {
                                        [type |-> "START-VIEW",
                                         log |-> maxLogMsg.log,
                                         view_num |-> v,
                                         commit_num |-> maxLogMsg.commit_num]
                                    }
                                 )

recvMajortiyDoViewChange(p, v) == LET
                                        mset == {
                                            msg \in messages: /\ msg.type = "DO-VIEW-CHANGE"
                                                              /\ msg.view_num = v
                                        }
                                        maxLogMsg == IF mset = {} THEN -1
                                            ELSE CHOOSE msg \in mset : \A msg2 \in mset :
                                                (\/ (msg.last_active_view_num > msg2.last_active_view_num)
                                                 \/ (/\ msg.last_active_view_num = msg2.last_active_view_num /\ Len(msg.log) \geq Len(msg2.log)))
                                  IN /\ Cardinality(mset) >= ((NumProcesses \div 2) + 1)
                                     /\ processState' = [processState EXCEPT ![p].view_num = v,
                                                                             ![p].status = "normal",
                                                                             ![p].log = maxLogMsg.log,
                                                                             ![p].commit_num = maxLogMsg.commit_num,
                                                                             ![p].last_active_view_num = v]
                                     /\ sendStartView(p, v, maxLogMsg)

NormalCaseOperation(p) ==
    \/
       \* A process, which thinks it is the leader, sends PREPARE messages.
       /\ isLeader(p)
       /\ sendPrepares(p)
       /\ UNCHANGED <<>>

    \/
       \* A process, which thinks it is the leader, sends COMMIT messages.
       /\ isLeader(p)
       /\ sendCommits(p)
       /\ UNCHANGED <<processState>>

    \/ \* A process, which thinks it is the leader, advances its commit number if majority PREPAREOKs have been received.
       \* Note that a leader can advance commit numbers non-sequentially.
       /\ isLeader(p)
       /\ \E log_num \in (processState[p].commit_num+1)..Len(processState[p].log):
            /\ majorityPREPAREOKs(p, log_num)
            /\ processState' = [processState EXCEPT ![p].commit_num = log_num]
       /\ UNCHANGED <<messages>>

    \/ \* Normal case operation of a replica node.
       /\ ~isLeader(p)
       /\
          \/
             /\ acceptPrepare(p)
             /\ UNCHANGED <<>>
          \/
             /\ acceptCommit(p)
             /\ UNCHANGED <<messages>>

    \/ \* Respond to RECOVERY messages.
       /\ \E msg \in messages:
            /\ msg.type = "RECOVERY"
            /\
               \/
                  /\ isLeader(p)
                  /\ subsetOfMsgs([type |-> "RECOVERYRESPONSE", from |-> p, to |-> msg.from,
                         view_num |-> processState[p].view_num, commit_num |-> processState[p].commit_num,
                         log |-> processState[p].log, nonce |-> msg.nonce]) = {} \* WfSimplifier condition
                  /\ sendMsgs(
                     {
                       [type |-> "RECOVERYRESPONSE",
                        from |-> p,
                        to |-> msg.from,
                        view_num |-> processState[p].view_num,
                        commit_num |-> processState[p].commit_num,
                        log |-> processState[p].log,
                        nonce |-> msg.nonce]
                     })
                \/
                   /\ ~isLeader(p)
                   /\ subsetOfMsgs([type |-> "RECOVERYRESPONSE", from |-> p, to |-> msg.from,
                         view_num |-> processState[p].view_num,
                         nonce |-> msg.nonce]) = {} \* WfSimplifier condition
                   /\ sendMsgs(
                      {
                        [type |-> "RECOVERYRESPONSE",
                         from |-> p,
                         to |-> msg.from,
                         view_num |-> processState[p].view_num,
                         nonce |-> msg.nonce]
                      })
            /\ UNCHANGED <<processState>>

FailuresTriggeredTillNow ==
    Sum({processState[p_id].nonce: p_id \in 0..NumProcesses-1}) +
        Sum({p_id \in 0..NumProcesses-1: processState[p_id].status = "recovering"})

\* When a node fails, it loses all data and goes into recovering status.
FailNode(p) == /\ FailuresTriggeredTillNow < MaxFailures
               /\ processState' = [processState EXCEPT ![p].commit_num = 0,
                                                       ![p].view_num = 0,
                                                       ![p].last_active_view_num = 0,
                                                       ![p].log = <<>>,
                                                       ![p].status = "recovering"]
               /\ sendMsgs(
                                {
                                    [type |-> "RECOVERY",
                                     from |-> p,
                                     nonce |-> processState[p].nonce]
                                }
                             )

\* There are a few ways to handle nonce, this spec follows the first one -
\* 1. Store it on disk and increment it just before a node marks itself "normal".
\* 2. Store it on disk and increment it whenever a node restarts to come into "recovering" status. But this has higher message
\*    complexity considering this scneario - if an already recovering node restarts, it will ignore the RECOVERYRESPONSE
\*    messages from all other nodes since they are from an ealier nonce, even though using those responses would have not violateed
\*    safety. This will require another set of RECOVERYRESPONSE messages.
\* 3. Use a clock value to generate nonce

Recover(p) == LET
                    \* There might be more than one RECOVERYRESPONSE messages from the same process.
                    mset == {
                        msg \in messages: /\ msg.type = "RECOVERYRESPONSE"
                          /\ msg.nonce = processState[p].nonce
                          /\ msg.to = p
                    }
                    sender_set == {p_id \in 0..NumProcesses-1: (\E msg \in mset: msg.from = p_id)}
                    maxViewMsg == IF mset = {} THEN <<>>
                        ELSE CHOOSE msg \in mset : \A msg2 \in mset :
                          \/ (msg.view_num >= msg2.view_num)
                    maxViewNum == IF maxViewMsg = <<>> THEN -1
                                  ELSE maxViewMsg.view_num
              IN
                 /\ Cardinality(sender_set) >= ((NumProcesses \div 2) + 1)
                 \* Very important -
                 \* Step through all behaviours where process p chooses any of the RECOVERYRESPONSEs from the leader of maxViewNum.
                 /\ \E msg \in mset:
                      /\ msg.from = maxViewNum % NumProcesses
                      /\ msg.view_num = maxViewNum \* This is important, if this check is not included, an older RECOVERYRESPONSE from the leader might be used. TODO - Bring in an invariant
                      /\ processState' = [processState EXCEPT ![p].view_num = maxViewNum,
                              ![p].status = "normal",
                              ![p].log = msg.log,
                              ![p].commit_num = msg.commit_num,
                              ![p].last_active_view_num = maxViewNum,

                              \* Not considering the case where the process increments
                              \* the nonce and then fails before setting status to normal.
                              \* This spec allows behaviours in which switching to normal
                              \* status and nonce incrementing is atomic, but it might not
                              \* be so in some implementation.
                              ![p].nonce = processState[p].nonce + 1]

VRInit == /\ messages = {}
          /\ processState =
                [p \in 0..NumProcesses-1 |-> [
                    view_num |-> 0,
                    log |-> <<>>,
                    commit_num |-> 0,
                    status |-> "normal", \* normal, view_change, do_view_change_sent, recovering
                    last_active_view_num |-> 0,
                    nonce |-> 0
                  ]
                ]
          /\ ordering = <<>>

VRNext ==
      \/ \* Normal case operation. Executed only when status of process is normal
         /\ \E p \in 0..NumProcesses-1:
              /\ processState[p].status = "normal"
              /\ NormalCaseOperation(p)

      \/ \* View change transitions. All except "recovering" status nodes can take this step.
         /\ \E p \in 0..NumProcesses-1:
              /\ processState[p].status # "recovering"
              /\ viewChangeTransitions(p)

      \/ \E p \in 0..NumProcesses-1:
           /\ processState[p].status # "recovering"
           /\ \E v \in 0..MaxViewNum:
                (
                    \* ~isLeader(p) is not kept here because it might happen that a leader again becomes the next leader.
                    \* TODO - What safety check would catch such an error?
                    /\ (
                        \/ v > processState[p].view_num \* TODO - Think of coming up with an invariant which is false in case we just have one condition with v >= processState[p].view_num
                        \/ (v = processState[p].view_num /\ ~(processState[p].status = "normal"))
                       )
                    /\ v % NumProcesses = p
                    /\ recvMajortiyDoViewChange(p, v)
                )

      \/ \* Fail a process. It goes to status "recovering"
         LET
            failed_processes == {p \in 0..NumProcesses-1: processState[p].status = "recovering"}
         IN
            /\ Cardinality(failed_processes) < ((NumProcesses-1) \div 2)
            /\ \E p \in (0..NumProcesses-1 \ failed_processes):
                 /\ FailNode(p)
            /\ UNCHANGED <<>>
      \/ \* Recover a recovering process, if the RECOVERYRESPONSEs have been received.
         \E p \in {p \in 0..NumProcesses-1: processState[p].status = "recovering"}:
            /\ Recover(p)
            /\ UNCHANGED <<messages>>

LatestActiveViewNum ==
    LET
        normal_view_nums == {processState'[p_id].last_active_view_num: p_id \in 0..NumProcesses-1}
    IN
        Maximum(normal_view_nums)

\* VRNextExt is VRNext with the extension of updating the ordering variable.
VRNextExt ==
    /\ VRNext
    /\ \* Set the ordering variable to the ordering as seen at the current leader correponding to the latest active view number.
       \* If the leader of this latest view number has failed (i.e., is in "recovering" status), the ordering doesn't change
       \* until a new leader is chosen and reaches "normal" status.
       \/
           /\ processState'[LatestActiveViewNum % NumProcesses].status # "recovering"
           /\ LET
                  mayBeNewOrdering == SubSeq(processState'[LatestActiveViewNum % NumProcesses].log,
                      1, processState'[LatestActiveViewNum % NumProcesses].commit_num)
              IN \* In case a process just became the leader, it might have a few client commands not yet
                 \* committed which the leader before this process had committed before failing.
                 \* In this case the outside world will still see an ordering which is only extended in future
                 \* as all new client commands will be committed only after the commands committed by the previous
                 \* leader are committed on the new leader i.e., the new leader will catch up in its committed list
                 \* with the same ordering as the previous leader.
                 IF Len(ordering) < Len(mayBeNewOrdering) THEN ordering' = mayBeNewOrdering
                 \* ordering doesn't change till catch up is complete. Also ensure that catch commit list is
                 \* always a prefix of the ordering.
                 ELSE /\ ordering' = ordering
                      /\ Assert(mayBeNewOrdering = SubSeq(ordering, 1, Len(mayBeNewOrdering)), "Old leader forked commit list")
       \/
           /\ processState'[LatestActiveViewNum % NumProcesses].status = "recovering"
           /\ ordering' = ordering

VRFair == VRInit /\ [][VRNextExt]_vars /\ WF_vars(VRNextExt)

(* Invariants *)

(* Invariant - for any two processes, log till lesser commit number is the same (Prefix property) *)

\* True if sequence a is a prefix of b
PrefixOf(a, b) ==
    /\ Len(a) <= Len(b)
    /\ \A i \in 1..Len(a): a[i] = b[i]

PrefixLogConsistency ==
    \A a, b \in 0..NumProcesses-1:
        \/ a = b
        \/ PrefixOf(
            SubSeq(processState[a].log, 1, processState[a].commit_num),
            SubSeq(processState[b].log, 1, processState[b].commit_num))
        \/ PrefixOf(
            SubSeq(processState[b].log, 1, processState[b].commit_num),
            SubSeq(processState[a].log, 1, processState[a].commit_num))

(* Invariant - process with higher view_num in normal state
   has larger log than last committed log of process in lower
   view_num *)
ViewNumCommitNumInv ==
    \A a, b \in 0..NumProcesses-1:
        \/ a = b
        \/ IF /\ processState[a].status = "normal"
              /\ processState[b].status = "normal"
              /\ processState[a].view_num < processState[b].view_num
           THEN processState[a].commit_num <= Len(processState[b].log)
           ELSE TRUE

INSTANCE LinearizableOrdering

LnCompliant == LnInit /\ [] [LnNext]_<<ordering>>
=============================================================================

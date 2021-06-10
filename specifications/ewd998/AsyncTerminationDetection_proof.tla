---------------------- MODULE AsyncTerminationDetection_proof ---------------------
EXTENDS AsyncTerminationDetection, TLAPS

LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK BY NAssumption DEF Init, TypeOK, Node, terminated
<1>2. TypeOK /\ [Next]_vars => TypeOK'
 <2> SUFFICES ASSUME TypeOK,
                     [Next]_vars
              PROVE  TypeOK'
   OBVIOUS
 <2>1. CASE DetectTermination
   BY <2>1 DEF TypeOK, Next, vars, DetectTermination
 <2>2. ASSUME NEW i \in Node,
              NEW j \in Node,
              Terminate(i)
       PROVE  TypeOK'
   BY <2>2 DEF TypeOK, Next, vars, Terminate, terminated
 <2>3. ASSUME NEW i \in Node,
              NEW j \in Node,
              Wakeup(i)
       PROVE  TypeOK'
   BY <2>3 DEF TypeOK, Next, vars, Wakeup
 <2>4. ASSUME NEW i \in Node,
              NEW j \in Node,
              SendMsg(i, j)
       PROVE  TypeOK'
   BY <2>4 DEF TypeOK, Next, vars, SendMsg
 <2>5. CASE UNCHANGED vars
   BY <2>5 DEF TypeOK, Next, vars
 <2>6. QED
   BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Proofs of safety and stability.                                         *)
(***************************************************************************)
Safe == terminationDetected => terminated

THEOREM Safety == Spec => []Safe
<1>. USE DEF terminated, TypeOK, Safe
<1>1. Init => Safe
  BY Zenon DEF Init
<1>2. TypeOK /\ Safe /\ [Next]_vars => Safe'
  <2> SUFFICES ASSUME TypeOK, Safe, [Next]_vars
               PROVE  Safe'
    OBVIOUS
  <2>1. CASE DetectTermination
    BY <2>1 DEF DetectTermination
  <2>2. ASSUME NEW i \in Node, Terminate(i)
        PROVE  Safe'
    BY <2>2, Zenon DEF Terminate
  <2>3. ASSUME NEW i \in Node, Wakeup(i)
        PROVE  Safe'
    BY <2>3 DEF Wakeup
  <2>4. ASSUME NEW i \in Node, NEW j \in Node, SendMsg(i, j)
        PROVE  Safe'
    BY <2>4 DEF SendMsg
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED
  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM Stability == Spec => Stable
\* We show that terminationDetected is never reset to FALSE
<1>1. TypeOK /\ Safe /\ terminationDetected /\ [Next]_vars => terminationDetected'
    BY Zenon
       DEF TypeOK, Safe, terminated, Next, DetectTermination, Terminate, Wakeup, SendMsg, vars
<1>. QED  BY <1>1, TypeCorrect, Safety, PTL DEF Spec, Stable, Safe

=============================================================================
\* Modification History
\* Last modified Wed Jun 02 14:19:14 PDT 2021 by markus
\* Last modified Thu Jan 21 17:38:07 CET 2021 by merz
\* Created Sun Jan 10 15:19:20 CET 2021 by merz

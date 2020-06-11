---------------------------- MODULE EWD998ChanID ----------------------------
(***************************************************************************)
(* This spec differs from EWD998Chan in that:                              *)
(*  - Where EWD998Chan (and EWD998) use naturals to model nodes, this spec *)
(*    uses a kind of identifier such as strings.  The identifiers are      *)
(*    organized into a ring.                                               *)
(*                                                                         *)
(*  - The initiator of tokens no longer is node 0 but an arbitrarily       *)
(*    choosen one.                                                         *)
(*                                                                         *)
(*  - The payload message "pl" contains the message sender "src".          *)
(*                                                                         *)
(* Minor differences:                                                      *)
(*  - In the interest of conciseness, the spec drops a few definitions     *)
(*    that are found in the high-level spec EWD998Chan.                    *)
(*                                                                         *)
(*  - Pull \E n \in Nodes up to the Spec level in preparation of PlusPy    *)
(*    implementation.                                                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Naturals, Utils

CONSTANT Node
ASSUME IsFiniteSet(Node) /\ Node # {}

N == Cardinality(Node)

\* Choose a node to be the initiator of a fresh token. We don't care which one it
\* is as long as it is always the same.
Initiator == CHOOSE n \in Node : TRUE
                                         
\* Organize Nodes in a ring. 
RingOfNodes == 
  CHOOSE r \in [ Node -> Node ]: IsSimpleCycle(Node, r)

Color == {"white", "black"}

VARIABLES 
 active,
 color,
 counter,
 inbox
  
vars == <<active, color, counter, inbox>>

------------------------------------------------------------------------------
 
Init ==
  (* Rule 0 *)
  /\ counter = [n \in Node |-> 0] \* c properly initialized
  /\ inbox = [n \in Node |-> IF n = Initiator 
                              THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >> 
                              ELSE <<>>] \* with empty channels.
  (* EWD840 *) 
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]

InitiateProbe ==
  (* Rule 1 *)
  /\ \E j \in 1..Len(inbox[Initiator]):
      \* Token is at node the Initiator.
      /\ inbox[Initiator][j].type = "tok"
      /\ \* Previous round inconsistent, if:
         \/ inbox[Initiator][j].color = "black"
         \/ color[Initiator] = "black"
         \* Implicit stated in EWD998 as c0 + q > 0 means that termination has not 
         \* been achieved: Initiate a probe if the token's color is white but the
         \* number of in-flight messages is not zero.
         \/ counter[Initiator] + inbox[Initiator][j].q # 0
      /\ inbox' = [inbox EXCEPT ![RingOfNodes[Initiator]] = Append(@, 
           [type |-> "tok", q |-> 0,
             (* Rule 6 *)
             color |-> "white"]), 
             ![Initiator] = RemoveAt(@, j) ] \* consume token message from inbox[0]. 
  (* Rule 6 *)
  /\ color' = [ color EXCEPT ![Initiator] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            
  
PassToken(n) ==
  (* Rule 2 *)
  /\ ~ active[n] \* If machine i is active, keep the token.
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "tok"
          \* the machine nr.i+1 transmits the token to machine nr.i under q := q + c[i+1]
          /\ LET tkn == inbox[n][j]
             IN  inbox' = [inbox EXCEPT ![RingOfNodes[n]] = 
                                       Append(@, [tkn EXCEPT !.q = tkn.q + counter[n],
                                                             !.color = IF color[n] = "black"
                                                                       THEN "black"
                                                                       ELSE tkn.color]),
                                    ![n] = RemoveAt(@, j) ] \* pass on the token.
  (* Rule 7 *)
  /\ color' = [ color EXCEPT ![n] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            

System(n) == \/ /\ n = Initiator
                /\ InitiateProbe
             \/ /\ n # Initiator
                /\ PassToken(n)

-----------------------------------------------------------------------------

SendMsg(n) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[n]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Node \ {n} :
          \* Send a message (not the token) to j.
          /\ inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl", src |-> n ] ) ]
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color>>                            

\* RecvMsg could write the incoming message to a (Java) buffer from which the (Java) implementation consumes it. 
RecvMsg(n) ==
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![n] = "black" ]
  \* Receipt of a message activates node n.
  /\ active' = [ active EXCEPT ![n] = TRUE ]
  \* Consume a message (not the token!).
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "pl"
          /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j) ]
  /\ UNCHANGED <<>>                           

Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment(n) == 
  \/ SendMsg(n)
  \/ RecvMsg(n)
  \/ Deactivate(n)

-----------------------------------------------------------------------------

Next(n) ==
  System(n) \/ Environment(n)

\* Idiomatic/canonical TLA+ has existential quantification down in System and Next.
Spec == Init /\ [][\E n \in Node: Next(n)]_vars
             /\ \A n \in Node: WF_vars(System(n))

OpenSpec == 
        Init /\ [][\E n \in Nodes: Next(n)]_<<active, color>> \* Allow variables inbox
                                                              \* and count to change
                                                              \* even if no actions
                                                              \* of the next-state
                                                              \* relations are enabled.
                                                              \* A lower-level spec,
                                                              \* may want to send
                                                              \* messages (of a new
                                                              \* type).
                                           \* We can't simply rewrite Spec to 
                                           \* I /\ []N_v with v declared as a constant
                                           \* to be able to subst v with vars in model:
                                           \*
                                           \* CONSTANT v
                                           \* Spec == Init /\ [][\E n \in Nodes: Next(n)_v
                                           \*
                                           \* vars is not constant-level and thus rejected
                                           \* by level-checking.  Also, it would mean that
                                           \* the actual meaning of the spec requires us
                                           \* to look at the model.  And what about the
                                           \* fairness constraint anyway?!?
             /\ \A n \in Nodes: WF_vars(System(n))

-----------------------------------------------------------------------------
\* The definitions of the refinement mapping below this line will be
\* ignored by PlusPy.  It can thus make use of RECURSIVE.
\*++:Spec
  
nat2node[i \in 0..N-1 ] == 
  LET RECURSIVE Op(_,_,_)
      Op(p, cnt, nd) ==
         IF p = cnt THEN nd
         ELSE Op(p, cnt - 1, RingOfNodes[nd])
  IN Op(i, N-1, RingOfNodes[Initiator])

Node2Nat(fcn) ==
  [ i \in 0..N-1 |->  fcn[nat2node[i]] ]

MapSeq(seq, Op(_)) ==
    LET F[i \in 0..Len(seq)] == IF i = 0
                                THEN << >>
                                ELSE Append(F[i - 1], Op(seq[i]))
    IN F[Len(seq)]

(***************************************************************************)
(* EWD998ChanID (identifier) refines EWD998Chan where nodes are modelled   *)
(* with naturals \in 0..N-1. To check that EWD998ChanID is a correct       *)
(* refinement _and_ to save us the troubles of rewriting the (inductive)   *)
(* Inv for identifiers, we have TLC check the two theorems below.          *)
(***************************************************************************)
EWD998Chan == INSTANCE EWD998Chan WITH active <- Node2Nat(active),
                                        color <- Node2Nat(color),
                                      counter <- Node2Nat(counter),
                                        inbox <- Node2Nat(
                                            \* Drop the src from the payload
                                            \* message.
                                            [n \in DOMAIN inbox |->
                                                MapSeq(inbox[n], 
                                                LAMBDA m: 
                                                IF m.type = "pl" 
                                                THEN [type |-> "pl"] 
                                                ELSE m) 
                                            ])

EWD998ChanStateConstraint == EWD998Chan!StateConstraint
EWD998ChanSpec == EWD998Chan!Spec

THEOREM Spec => EWD998ChanSpec

=============================================================================

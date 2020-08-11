------------------------ MODULE LinearizableOrdering ------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT
    \* Set of client commands. The specification (as of now) doesn't bother to model different clients and exactly-one semantics
    \* as mentioned in the paper as this is not relevant to the correctness of the core consensus algorithm.
    ClientCommands

VARIABLES
    (* A sequence representing a linearizable ordering of of the client commands *)
    ordering

LnInit == ordering = <<>>

PossiblePermutations(S) == {possible_seq \in [1..Cardinality(S) -> S]: (\A a, b \in 1..Len(possible_seq): (a = b \/ possible_seq[a] # possible_seq[b]))}

LnNext ==
  \/ \* Append a set of client commands to ordering if none of them are added yet.
     /\ \E cmds \in SUBSET ClientCommands:
          /\ cmds # {}
          /\ LET
                 Test(element) == element \in cmds
             IN
                 /\ Len(SelectSeq(ordering, Test)) = 0
                 /\ \E permutation \in PossiblePermutations(cmds): ordering' = ordering \o permutation

PossibleOrderings(S) ==
    {possible_seq \in UNION {
        [1..n -> S] : n \in 0..Cardinality(S)}:
            (\A a, b \in 1..Len(possible_seq): (a = b \/ possible_seq[a] # possible_seq[b]))}

LnTypeOK == ordering \in PossibleOrderings(ClientCommands)
            
=============================================================================
\* Modification History
\* Last modified Mon May 04 19:18:04 CDT 2020 by pkj
\* Created Sun May 03 06:40:45 CDT 2020 by pkj

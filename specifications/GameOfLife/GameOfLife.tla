----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})
                            
Pos == {<<x, y>> : x, y \in 1..N}
TypeOK == grid \in [Pos -> BOOLEAN]

sc[<<x, y>> \in (0 .. N + 1) \X
                (0 .. N + 1)] == CASE \/ x = 0 \/ y = 0
                                      \/ x > N \/ y > N
                                      \/ ~grid[<<x, y>>] -> 0
                                   [] OTHER -> 1

score(p) == LET nbrs == {x \in {-1, 0, 1} \X
                               {-1, 0, 1} : x /= <<0, 0>>}
                points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
            IN Sum(sc, points)
                   
Init == grid \in [Pos -> BOOLEAN]
Next == grid' = [p \in Pos |-> IF \/  (grid[p] /\ score(p) \in {2, 3})
                                  \/ (~grid[p] /\ score(p) = 3)
                                THEN TRUE
                                ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================

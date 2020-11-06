(***************************************************************************)
(* Tower of Hanoi                                                          *)
(*                                                                         *)
(* From https://en.wikipedia.org/wiki/Tower_of_Hanoi:                      *)
(*                                                                         *)
(* The Tower of Hanoi is a mathematical game or puzzle.  It consists of    *)
(* three rods and a number of disks of different sizes, which can slide    *)
(* onto any rod.  The puzzle starts with the disks in a neat stack in      *)
(* ascending order of size on one rod, the smallest at the top, thus       *)
(* making a conical shape.                                                 *)
(*                                                                         *)
(* The objective of the puzzle is to move the entire stack to another rod, *)
(* obeying the following simple rules:                                     *)
(*                                                                         *)
(*   1. Only one disk can be moved at a time.                              *)
(*   2. Each move consists of taking the upper disk from one of the stacks *)
(*      and placing it on top of another stack or on an empty rod.         *)
(*   2. No larger disk may be placed on top of a smaller disk.             *)
(***************************************************************************)

------------------------------ MODULE HanoiSeq ------------------------------
EXTENDS TLC, Sequences, Integers

CONSTANTS A, B, C
VARIABLES towers

(***************************************************************************)
(* We model the three positions where a "tower" of disks can be present as *)
(* sequences of natural numbers.  The numbers represent the sizes of the   *)
(* disks.                                                                  *)
(*                                                                         *)
(* A, B, and C are the initial configurations of the towers. For example:  *)
(*   A == <<1,2,3>>                                                        *)
(*   B == <<>>                                                             *)
(*   C == <<>>                                                             *)
(***************************************************************************)
ASSUME A \in [1..Len(A) -> Nat]
ASSUME B \in [1..Len(B) -> Nat]
ASSUME C \in [1..Len(C) -> Nat]

Init ==
  towers = <<A, B, C>>

(***************************************************************************)
(* A disk can be moved if:                                                 *)
(*  - The source position is different from the destination.               *)
(*  - The source tower is not empty.                                       *)
(*  - The top disk of the source tower is smaller than the top disk of     *)
(*    the destination tower.                                               *)
(***************************************************************************)
CanMove(from, to) ==
  /\ from /= to
  /\ towers[from] /= <<>>
  /\ IF
      towers[to] = <<>>
    THEN
      TRUE
    ELSE
      Head(towers[from]) < Head(towers[to])

(***************************************************************************)
(* Moving a disk means the source tower is left with all but the top disk, *)
(* which is added to the destination tower.                                *)
(***************************************************************************)
Move(from, to) ==
  towers' = [
    towers EXCEPT
      ![from] = Tail(towers[from]),
      ![to] = <<Head(towers[from])>> \o towers[to]
  ]

Next ==
  \E from, to \in 1..Len(towers):
    /\ CanMove(from, to)
    /\ Move(from, to)

(***************************************************************************)
(* This finishes the spec.  The next section are the invariants to check.  *)
(***************************************************************************)

(***************************************************************************)
(* Helper to get the elements of a sequence.                               *)
(***************************************************************************)
Range(sequence) ==
  {sequence[i]: i \in DOMAIN sequence}

(***************************************************************************)
(* `towers` has 3 elements, each a sequence of numbers.                    *)
(***************************************************************************)
TypeOK ==
  /\ DOMAIN towers = 1..3
  /\ \A sequence \in Range(towers):
      sequence \in [1..Len(sequence) -> Nat]

(***************************************************************************)
(* In all towers there should never be elements which were not initially   *)
(* present.                                                                *)
(***************************************************************************)
NoNewElements ==
  LET
    originalElements ==
      UNION {Range(A), Range(B), Range(C)}
    towerElements ==
      UNION {Range(towers[1]), Range(towers[2]), Range(towers[3])}
  IN
    towerElements = originalElements

(***************************************************************************)
(* The total number of disks should stay constant.                         *)
(***************************************************************************)
TotalConstant ==
  LET
    originalTotal ==
      Len(A) + Len(B) + Len(C)
    towerTotal==
      Len(towers[1]) + Len(towers[2]) + Len(towers[3])
  IN
    towerTotal = originalTotal

(***************************************************************************)
(* The final configuration has all disks on the right tower with the disks *)
(* ordered by size.  If a violation of this invariant can be found, the    *)
(* stack trace shows the steps to solve the Hanoi problem.                 *)
(***************************************************************************)
NotSolved ==
  ~(
    /\ towers[1] = <<>>
    /\ towers[2] = <<>>
    /\ towers[3] = [i \in 1..Len(towers[3]) |-> i]
  )
=============================================================================

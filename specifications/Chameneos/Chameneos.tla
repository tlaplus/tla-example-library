----------------------------- MODULE Chameneos -----------------------------
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)

EXTENDS Integers

\* N - number of total meeting after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLE chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

TypeOK == /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
          /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}

Complement(c1, c2) == IF c1 = c2
                      THEN c1
                      ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

Meet(cid) == IF meetingPlace = MeetingPlaceEmpty
             THEN IF numMeetings < N
                       \* chameneos enters meeting empty meeting place
                  THEN /\ meetingPlace' = cid
                       /\ UNCHANGED <<chameneoses, numMeetings>>
                       \* chameneos takes on faded color
                  ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
                       /\ UNCHANGED <<meetingPlace, numMeetings>>
                  \* meeting place is not empty - two chameneoses mutate
             ELSE /\ meetingPlace /= cid
                  /\ meetingPlace' = MeetingPlaceEmpty
                  /\ chameneoses' =
                        LET newColor == Complement(chameneoses[cid][1],
                                                      chameneoses[meetingPlace][1])
                        IN [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                               ![meetingPlace] = <<newColor, @[2] + 1>>]
                  /\ numMeetings' = numMeetings + 1

Init == /\ chameneoses \in [ChameneosID -> Color \X {0}]
        /\ meetingPlace = MeetingPlaceEmpty
        /\ numMeetings = 0

\* repeatedly try to enter meeting place for chameneoses that are not faded yet
Next == /\ \E c \in { x \in ChameneosID : chameneoses[x][1] /= Faded} : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet == numMeetings = N => LET f[c \in ChameneosID] == chameneoses[c][2]
                             IN Sum(f, ChameneosID) = 2 * N

=============================================================================

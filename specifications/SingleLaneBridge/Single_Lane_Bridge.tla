-------------------------- MODULE Single_Lane_Bridge --------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions 

VARIABLES Location, Waiting
vars == <<Location, Waiting>>

Cars == CarsRight \union CarsLeft 

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

StartBridge == CHOOSE min \in Bridge : \A e \in Bridge : min <= e
EndBridge == CHOOSE max \in Bridge : \A e \in Bridge : max >= e

RMove(pos) == IF pos > 1 THEN pos - 1 ELSE 8
LMove(pos) == IF pos < 8 THEN pos + 1 ELSE 1

NextLocation(car) == IF car \in CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

ChangeLocation(car) ==
    /\ IF \/ car \in CarsRight /\ NextLocation(car) = EndBridge + 1
          \/ car \in CarsLeft /\ NextLocation(car) = StartBridge - 1
        THEN Waiting' = Append(Waiting, car)
        ELSE UNCHANGED Waiting
    /\ Location' = [ Location EXCEPT ![car] = NextLocation(car) ]

HaveSameDirection(car) ==
    \/ car \in CarsRight /\ \A c \in CarsInBridge : c \in CarsRight
    \/ car \in CarsLeft /\ \A c \in CarsInBridge : c \in CarsLeft

\*Actions
Move(car) ==
    /\ NextLocation(car) \notin Bridge
    /\ ChangeLocation(car)

MoveInsideBridge(car) ==
    /\ car \in CarsInBridge
    /\ \A c \in Cars : Location[c] # NextLocation(car)
    /\ ChangeLocation(car)

EnterBridge ==
        /\ CarsInBridge = {}
        /\ Len(Waiting) # 0
        /\ Location' = [ Location EXCEPT ![Head(Waiting)] = NextLocation(Head(Waiting)) ]
        /\ Waiting' = Tail(Waiting)
    \/  /\ Len(Waiting) # 0
        /\ Head(Waiting) \notin CarsInBridge
        /\ HaveSameDirection(Head(Waiting))
        /\ \A c \in Cars : Location[c] # NextLocation(Head(Waiting))
        /\ Location' = [ Location EXCEPT ![Head(Waiting)] = NextLocation(Head(Waiting)) ]
        /\ Waiting' = Tail(Waiting)


Init == 
    /\ Location = [ c \in Cars |-> IF c \in CarsRight THEN 8 ELSE 1  ]
    /\ Waiting = <<>>

Next == \E car \in Cars : EnterBridge \/ Move(car) \/ MoveInsideBridge(car)

Fairness ==
    /\ \A car \in Cars : WF_vars(Move(car))
    /\ \A car \in Cars : WF_vars(MoveInsideBridge(car))
    /\ \A car \in Cars : WF_vars(EnterBridge)

Spec == Init /\ [][Next]_vars /\ Fairness

TypeOK ==
    /\ Location \in [ Cars -> Positions ]
    /\ Len(Waiting) <= Cardinality(Cars)

Invariants ==
    /\ TypeOK
    \* Two cars or more cannot be in the same location in the Bridge at the same time
    /\ \A a,b \in Cars :
        /\ Location[a] \in Bridge
        /\ Location[a] = Location[b]
        => a = b
    \* The bridge capacity should be respected
    /\ Cardinality(CarsInBridge) < Cardinality(Bridge) + 1
    \* Two cars of different directions can never be in the bridge
    /\ \A <<r,l>> \in CarsRight \X CarsLeft :
        ~ (Location[r] \in Bridge /\ Location[l] \in Bridge) 

THEOREM Invariants => []Spec

CarsInBridgeExitBridge ==
    \* All cars eventually exit the Bridge 
    \A car \in Cars : Location[car] \in Bridge ~> <> (Location[car] \notin Bridge)
CarsEnterBridge ==
    \* All cars eventually enter the bridge
    \A car \in Cars : Location[car] \notin Bridge ~> <> (Location[car] \in Bridge)

=============================================================================
\* Modification History
\* Last modified Sun Mar 14 12:13:14 CET 2021 by oblic
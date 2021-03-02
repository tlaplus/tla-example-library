---- MODULE DiningPhilosophers ----

(*
TLA+ / PlusCal implementation of the Dining Philosophers problem.
Based on the exercise given in https://learntla.com/temporal-logic/operators/

I ran this with alygin's TLA+ extension for VSCode:
  https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus
"> TLA+: Parse module" updates the translated TLA+ to match the PlusCal
  'algorithm' above.
"> TLA+: Check model with TLC" checks the model's correctness.

You can also use TLA+ Toolbox. You may need to "create a model" and
add the properties to check via the UI, though. These properties are:
 Termination
 ForkOrderingHolds
 NobodyStarves
*)

EXTENDS Integers, TLC

CONSTANTS
    \* Number of philosophers
    NP,
    \* Special constant to indicates a value outside the domain
    NULL

(* --algorithm DiningPhilosophers

variables
    forks = [fork \in 1..NP |-> NULL]

define
    
    \* Instead of a "left fork" and a "right fork", each philosopher is aware
    \* of the lower-numbered and higher-numbered fork next to them.
    LowFork(p) == IF p = NP THEN 1 ELSE p
    HighFork(p) == IF p = NP THEN p ELSE p + 1

    ShouldPickUpLowFork(p) ==
        forks[LowFork(p)] = NULL
    ShouldPickUpHighFork(p) ==
        forks[LowFork(p)] = p
        /\ forks[HighFork(p)] = NULL
    
    \* We release the low fork if we can't pick up the high fork.
    ShouldReleaseLowFork(p) ==
        forks[LowFork(p)] = p
        /\ forks[HighFork(p)] /= p
        /\ forks[HighFork(p)] /= NULL

    IsHoldingBothForks(p) ==
        forks[LowFork(p)] = p /\ forks[HighFork(p)] = p
end define;

\* This spawns 'NP' parallel Philosopher processes.
\* 
\* A process looks kind of like an object oriented class, but '\in 1..NP' means
\* it's really just an integer between 1 and NP. Use 'self' to access that
\* integer.
\* 
\* If you remove the 'fair' in 'fair process', the model will not check. 
fair process Philosopher \in 1..NP
\* This acts like a member variable and you can access it like one. But it's
\* actually an array with one element per process, and the "member variable" is
\* just the corresponding bucket in that array.
variables hungry = TRUE;
begin
    
    Loop:
        while hungry do
            if ShouldPickUpLowFork(self) then
                forks[LowFork(self)] := self;
            elsif ShouldPickUpHighFork(self) then
                forks[HighFork(self)] := self;
            elsif ShouldReleaseLowFork(self) then
                forks[LowFork(self)] := NULL;
            elsif IsHoldingBothForks(self) then
                Eat:
                    hungry := FALSE;
                    forks[LowFork(self)] := NULL
                    || forks[HighFork(self)] := NULL;
            end if;
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3b5d638b" /\ chksum(tla) = "b5311876")
VARIABLES forks, pc

(* define statement *)
LowFork(p) == IF p = NP THEN 1 ELSE p
HighFork(p) == IF p = NP THEN p ELSE p + 1

ShouldPickUpLowFork(p) ==
    forks[LowFork(p)] = NULL
ShouldPickUpHighFork(p) ==
    forks[LowFork(p)] = p
    /\ forks[HighFork(p)] = NULL


ShouldReleaseLowFork(p) ==
    forks[LowFork(p)] = p
    /\ forks[HighFork(p)] /= p
    /\ forks[HighFork(p)] /= NULL

IsHoldingBothForks(p) ==
    forks[LowFork(p)] = p /\ forks[HighFork(p)] = p

VARIABLE hungry

vars == << forks, pc, hungry >>

ProcSet == (1..NP)

Init == (* Global variables *)
        /\ forks = [fork \in 1..NP |-> NULL]
        (* Process Philosopher *)
        /\ hungry = [self \in 1..NP |-> TRUE]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF hungry[self]
                    THEN /\ IF ShouldPickUpLowFork(self)
                               THEN /\ forks' = [forks EXCEPT ![LowFork(self)] = self]
                                    /\ pc' = [pc EXCEPT ![self] = "Loop"]
                               ELSE /\ IF ShouldPickUpHighFork(self)
                                          THEN /\ forks' = [forks EXCEPT ![HighFork(self)] = self]
                                               /\ pc' = [pc EXCEPT ![self] = "Loop"]
                                          ELSE /\ IF ShouldReleaseLowFork(self)
                                                     THEN /\ forks' = [forks EXCEPT ![LowFork(self)] = NULL]
                                                          /\ pc' = [pc EXCEPT ![self] = "Loop"]
                                                     ELSE /\ IF IsHoldingBothForks(self)
                                                                THEN /\ pc' = [pc EXCEPT ![self] = "Eat"]
                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "Loop"]
                                                          /\ forks' = forks
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ forks' = forks
              /\ UNCHANGED hungry

Eat(self) == /\ pc[self] = "Eat"
             /\ hungry' = [hungry EXCEPT ![self] = FALSE]
             /\ forks' = [forks EXCEPT ![LowFork(self)] = NULL,
                                       ![HighFork(self)] = NULL]
             /\ pc' = [pc EXCEPT ![self] = "Loop"]

Philosopher(self) == Loop(self) \/ Eat(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..NP: Philosopher(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NP : WF_vars(Philosopher(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* PROPERTIES

\* Nobody will ever hold their higher-numbered fork without first holding their
\* lower-numbered fork.
ForkOrderingHolds ==
    [](\A p \in 1..NP: (forks[HighFork(p)] = p) => (forks[LowFork(p)] = p))

\* Everyone will eventually get to eat.
\* Note that we defined "hungry" as a member variable of the Philosopher
\* process, but it's actually an array.
NobodyStarves == <>[](\A p \in 1..NP: ~hungry[p])

====

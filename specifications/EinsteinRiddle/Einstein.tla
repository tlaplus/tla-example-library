------------------- MODULE Einstein ------------------------

(*********************************************************************)
(* Literature/Source:                                                *)
(*   https://udel.edu/~os/riddle.html                                *)
(*                                                                   *)
(* Situation:                                                        *)
(* - There are 5 houses in five different colors.                    *)
(* - In each house lives a person with a different nationality.      *)
(* - These five owners drink a certain type of beverage, smoke a     *)
(*   certain brand of cigar and keep a certain pet.                  *)
(* - No owners have the same pet, smoke the same brand of cigar, or  *)
(*   drink the same beverage.                                        *)
(*                                                                   *)
(* Rules:                                                            *)
(*  1 the Brit lives in the red house                                *)
(*  2 the Swede keeps dogs as pets                                   *)
(*  3 the Dane drinks tea                                            *)
(*  4 the green house is on the left of the white house              *)
(*  5 the green house's owner drinks coffee                          *)
(*  6 the person who smokes Pall Mall rears birds                    *)
(*  7 the owner of the yellow house smokes Dunhill                   *)
(*  8 the man living in the center house drinks mylk                 *)
(*  9 the Norwegian lives in the first house                         *)
(* 10 the man who smokes blends lives next to the one who keeps cats *)
(* 11 the man who keeps horses lives next to man who smokes Dunhill  *)
(* 12 the owner who smokes BlueMaster drinks beer                    *)
(* 13 the German smokes Prince                                       *)
(* 14 the Norwegian lives next to the blue house                     *)
(* 15 the man who smokes blend has a neighbor who drinks water       *)
(*********************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    NATIONALITIES,  \* { "brit", "swede", "dane", "norwegian", "german" }
    COLORS,         \* { "red", "white", "blue", "green", "yellow" }
    PETS,           \* { "bird", "cat", "dog", "fish", "horse" }
    CIGARS,         \* { "blend", "bm", "dh", "pm", "prince" }
    DRINKS          \* { "beer", "coffee", "mylk", "tea", "water" }

VARIABLES
    nationality,    \* tuple of nationalities
    colors,         \* tuple of house colors
    pets,           \* tuple of pets
    cigars,         \* tuple of cigars
    drinks          \* tuple of drinks

------------------------------------------------------------

(*********)
(* Rules *)
(*********)

BritLivesInTheRedHouse == \E i \in 2..5 : nationality[i] = "brit" /\ colors[i] = "red"

SwedeKeepsDogs == \E i \in 2..5 : nationality[i] = "swede" /\ pets[i] = "dog"

DaneDrinksTea == \E i \in 2..5 : nationality[i] = "dane" /\ drinks[i] = "tea"

GreenLeftOfWhite == \E i \in 1..4 : colors[i] = "green" /\ colors[i + 1] = "white"

GreenOwnerDrinksCoffee == \E i \in 1..5 \ {3} : colors[i] = "green" /\ drinks[i] = "coffee"

SmokesPallmallRearsBirds == \E i \in 1..5 : cigars[i] = "pm" /\ pets[i] = "bird"

YellowOwnerSmokesDunhill == \E i \in 1..5 : colors[i] = "yellow" /\ cigars[i] = "dh"

CenterDrinksMylk == drinks[3] = "mylk"

NorwegianFirstHouse == nationality[1] = "norwegian"

BlendSmokerLivesNextToCatOwner ==
    \E i \in 1..4 :
        \/ cigars[i] = "blend" /\ pets[i + 1] = "cat"
        \/ pets[i] = "cat" /\ cigars[i + 1] = "blend"

HorseKeeperLivesNextToDunhillSmoker ==
    \E i \in 1..4 :
        \/ cigars[i] = "dh" /\ pets[i + 1] = "horse"
        \/ pets[i] = "horse" /\ cigars[i + 1] = "dh"

BluemasterSmokerDrinksBeer == \E i \in 1..5 : cigars[i] = "bm" /\ drinks[i] = "beer"

GermanSmokesPrince == \E i \in 2..5 : nationality[i] = "german" /\ cigars[i] = "prince"

NorwegianLivesNextToBlueHouse == colors[2] = "blue" \* since the norwegian lives in the first house

BlendSmokerHasWaterDrinkingNeighbor ==
    \E i \in 1..4 :
        \/ cigars[i] = "blend" /\ drinks[i + 1] = "water"
        \/ drinks[i] = "water" /\ cigars[i + 1] = "blend"

------------------------------------------------------------

(************)
(* Solution *)
(************)

Permutation(S) ==
    { p \in [ 1..5 -> S ] :
        /\ p[2] \in S \ {p[1]}
        /\ p[3] \in S \ {p[1], p[2]}
        /\ p[4] \in S \ {p[1], p[2], p[3]}
        /\ p[5] \in S \ {p[1], p[2], p[3], p[4]} }

Init ==
    /\ drinks \in { p \in Permutation(DRINKS) : p[3] = "mylk" }
    /\ nationality \in { p \in Permutation(NATIONALITIES) : p[1] = "norwegian" }
    /\ colors \in { p \in Permutation(COLORS) : p[2] = "blue" }
    /\ pets \in Permutation(PETS)
    /\ cigars \in Permutation(CIGARS)

Spec == Init /\ [][FALSE]_<<nationality, colors, cigars, pets, drinks>>

Solution ==
    /\ BritLivesInTheRedHouse
    /\ SwedeKeepsDogs
    /\ DaneDrinksTea
    /\ GreenLeftOfWhite
    /\ GreenOwnerDrinksCoffee
    /\ SmokesPallmallRearsBirds
    /\ YellowOwnerSmokesDunhill
    /\ CenterDrinksMylk
    /\ NorwegianFirstHouse
    /\ BlendSmokerLivesNextToCatOwner
    /\ HorseKeeperLivesNextToDunhillSmoker
    /\ BluemasterSmokerDrinksBeer
    /\ GermanSmokesPrince
    /\ NorwegianLivesNextToBlueHouse
    /\ BlendSmokerHasWaterDrinkingNeighbor

FindSolution == ~Solution

============================================================

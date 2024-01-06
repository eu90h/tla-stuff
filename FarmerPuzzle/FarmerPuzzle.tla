---------------------------- MODULE FarmerPuzzle ----------------------------
EXTENDS FiniteSets, Naturals
VARIABLES LeftSideContents, RightSideContents, BoatContents, EmbarkSide

W == "Wolf"
G == "Goat"
C == "Cabbage"
F == "Farmer"
L == "Left"
R == "Right"

AllObjects == {W,G,C,F}

WolfEatsGoat == \/ {W, G} \subseteq LeftSideContents /\ F \notin LeftSideContents
                \/ {W, G} \subseteq RightSideContents /\ F \notin RightSideContents

GoatEatsCabbage == \/ {G, C} \subseteq LeftSideContents /\ F \notin LeftSideContents
                   \/ {C, G} \subseteq RightSideContents /\ F \notin RightSideContents

Safe == ~WolfEatsGoat /\ ~GoatEatsCabbage

NotSolved == Cardinality(RightSideContents) < 4

TypeOK == /\ Cardinality(LeftSideContents) + Cardinality(BoatContents) + Cardinality(RightSideContents) = 4
          /\ Cardinality(BoatContents) <= 2
          /\ LeftSideContents \subseteq AllObjects
          /\ BoatContents \subseteq AllObjects
          /\ RightSideContents \subseteq AllObjects
          /\ EmbarkSide \in {L, R}

Init == /\ LeftSideContents = AllObjects
        /\ RightSideContents = {}
        /\ BoatContents = {}
        /\ EmbarkSide = L

PutOnBoat(obj) == /\ Safe
                  /\ Cardinality(BoatContents) = 0 \/ Cardinality(BoatContents) = 1
                  /\ BoatContents \subseteq AllObjects  
                  /\ IF EmbarkSide = R THEN 
                         /\ obj \in RightSideContents
                         /\ RightSideContents' = RightSideContents \ {obj}
                         /\ UNCHANGED LeftSideContents
                     ELSE
                        /\ obj \in LeftSideContents
                        /\ LeftSideContents' = LeftSideContents \ {obj}
                        /\ UNCHANGED RightSideContents
                  /\ BoatContents' = BoatContents \cup {obj}
                  /\ UNCHANGED <<EmbarkSide>>

Disembark == /\ Safe
             /\ F \in BoatContents
             /\ Cardinality(BoatContents) = 1 \/ Cardinality(BoatContents) = 2
             /\ BoatContents \subseteq AllObjects
             /\ BoatContents' = {}
             /\ IF EmbarkSide = L 
                THEN /\ EmbarkSide' = R
                     /\ RightSideContents' = RightSideContents \cup BoatContents
                     /\ UNCHANGED <<LeftSideContents>>
                ELSE /\ EmbarkSide' = L
                     /\ LeftSideContents' = LeftSideContents \cup BoatContents
                     /\ UNCHANGED <<RightSideContents>>

LoadFromLeft == EmbarkSide = L /\ \E obj \in LeftSideContents : PutOnBoat(obj)

LoadFromRight == EmbarkSide = R /\ \E obj \in RightSideContents : PutOnBoat(obj)

Next == \/ LoadFromLeft
        \/ LoadFromRight
        \/ Disembark

Spec == Init /\ [][Next]_<<LeftSideContents, RightSideContents, BoatContents, EmbarkSide>>
=============================================================================
\* Modification History
\* Last modified Sat Jan 06 07:56:43 EST 2024 by sca
\* Created Fri Jan 05 19:20:32 EST 2024 by sca

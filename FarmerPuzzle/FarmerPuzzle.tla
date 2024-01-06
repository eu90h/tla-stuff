---------------------------- MODULE FarmerPuzzle ----------------------------
EXTENDS FiniteSets, Naturals
VARIABLES LeftSideContents, RightSideContents, BoatContents, EmbarkSide

AllObjects == {"Wolf", "Goat", "Cabbage", "Farmer"}

WolfEatsGoat == \/ {"Wolf", "Goat"} \subseteq LeftSideContents /\ "Farmer" \notin LeftSideContents
                \/ {"Wolf", "Goat"} \subseteq RightSideContents /\ "Farmer" \notin RightSideContents

GoatEatsCabbage == \/ {"Goat", "Cabbage"} \subseteq LeftSideContents /\ "Farmer" \notin LeftSideContents
                   \/ {"Cabbage", "Goat"} \subseteq RightSideContents /\ "Farmer" \notin RightSideContents

Safe == ~WolfEatsGoat /\ ~GoatEatsCabbage

TypeOK == /\ Cardinality(LeftSideContents) + Cardinality(BoatContents) + Cardinality(RightSideContents) = 4
          /\ Cardinality(BoatContents) <= 2
          /\ LeftSideContents \subseteq AllObjects
          /\ BoatContents \subseteq AllObjects
          /\ RightSideContents \subseteq AllObjects
          /\ EmbarkSide \in {"Left", "Right"}

Init == /\ LeftSideContents = AllObjects
        /\ RightSideContents = {}
        /\ BoatContents = {}
        /\ EmbarkSide = "Left"

PutOnBoat(obj) == /\ Safe
                  /\ Cardinality(BoatContents) = 0 \/ Cardinality(BoatContents) = 1
                  /\ BoatContents \subseteq AllObjects  
                  /\ IF EmbarkSide = "Right" THEN 
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
             /\ "Farmer" \in BoatContents
             /\ Cardinality(BoatContents) = 1 \/ Cardinality(BoatContents) = 2
             /\ BoatContents \subseteq AllObjects
             /\ BoatContents' = {}
             /\ IF EmbarkSide = "Left" 
                THEN /\ EmbarkSide' = "Right"
                     /\ RightSideContents' = RightSideContents \cup BoatContents
                     /\ UNCHANGED <<LeftSideContents>>
                ELSE /\ EmbarkSide' = "Left"
                     /\ LeftSideContents' = LeftSideContents \cup BoatContents
                     /\ UNCHANGED <<RightSideContents>>

LoadFromLeft == EmbarkSide = "Left" /\ \E obj \in LeftSideContents : PutOnBoat(obj)

LoadFromRight == EmbarkSide = "Right" /\ \E obj \in RightSideContents : PutOnBoat(obj)

Next == \/ LoadFromLeft
        \/ LoadFromRight
        \/ Disembark

Spec == Init /\ [][Next]_<<LeftSideContents, RightSideContents, BoatContents, EmbarkSide>>
=============================================================================
\* Modification History
\* Last modified Fri Jan 05 21:35:08 EST 2024 by sca
\* Created Fri Jan 05 19:20:32 EST 2024 by sca

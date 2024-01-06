---- MODULE FarmerPuzzle2 ----
EXTENDS Naturals, FiniteSets, TLC
W == "Wolf"
G == "Goat"
C == "Cabbage"
F == "Farmer"
Locations == {"left", "right"}
AllObjects == {W,G,C,F}

(* --algorithm FarmerPuzzle2 {
    variables
        left_bank = AllObjects;
        right_bank = {};
        boat = {};
        location = "left";

    define {
        WolfEatsGoat(S) == {W,G} \subseteq S /\ F \notin S
        GoatEatsCabbage(S) == {G,C} \subseteq S /\ F \notin S
        Safe(S) == ~WolfEatsGoat(S) /\ ~GoatEatsCabbage(S)
        TypeOK ==
            /\ Cardinality(left_bank) + Cardinality(right_bank) + Cardinality(boat) = 4
            /\ Cardinality(boat) <= 2
            /\ boat \in SUBSET{F,C,G,W}
            /\ left_bank \in SUBSET {F,C,G,W}
            /\ right_bank \in SUBSET {F,C,G,W}
            /\ location \in Locations
        NotSolved == Cardinality(right_bank) < 4
    } 
    
    fair process (i \in {0,1}) {
        S: while (TRUE) {
            either { \* Load Boat
                await Cardinality(boat) < 2;
                if (location = "left") {
                    await left_bank # {};
                    with (x \in left_bank) {
                        if (Safe(left_bank \ {x}) /\ Safe(right_bank) /\ Safe(boat)) {
                            left_bank := left_bank \ {x};
                            boat := boat \union {x};
                        }
                    }
                } else {
                    await right_bank # {};
                    with (x \in right_bank) {
                        if (Safe(left_bank) /\ Safe(right_bank \ {x}) /\ Safe(boat)) {
                            right_bank := right_bank \ {x};
                            boat := boat \union {x};
                        }
                     };
                };
            }
            or {
                await (boat # {} /\ Cardinality(boat) <= 2 /\ F \in boat);
                if (location = "left" /\ Safe(left_bank) /\ Safe(right_bank\union boat)) {
                    location := "right";
                    right_bank := right_bank \union boat;
                    boat := {}
                } else if (location = "right" /\ Safe(right_bank) /\ Safe(left_bank\union boat)) {
                    location := "left";
                    left_bank := left_bank \union boat;
                    boat := {}
                };
            }
        }
    }
  
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "509165d8" /\ chksum(tla) = "74d5f33d")
VARIABLES left_bank, right_bank, boat, location

(* define statement *)
WolfEatsGoat(S) == {W,G} \subseteq S /\ F \notin S
GoatEatsCabbage(S) == {G,C} \subseteq S /\ F \notin S
Safe(S) == ~WolfEatsGoat(S) /\ ~GoatEatsCabbage(S)
TypeOK ==
    /\ Cardinality(left_bank) + Cardinality(right_bank) + Cardinality(boat) = 4
    /\ Cardinality(boat) <= 2
    /\ boat \in SUBSET{F,C,G,W}
    /\ left_bank \in SUBSET {F,C,G,W}
    /\ right_bank \in SUBSET {F,C,G,W}
    /\ location \in Locations
NotSolved == Cardinality(right_bank) < 4


vars == << left_bank, right_bank, boat, location >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ left_bank = AllObjects
        /\ right_bank = {}
        /\ boat = {}
        /\ location = "left"

i(self) == \/ /\ Cardinality(boat) < 2
              /\ IF location = "left"
                    THEN /\ left_bank # {}
                         /\ \E x \in left_bank:
                              IF Safe(left_bank \ {x}) /\ Safe(right_bank) /\ Safe(boat)
                                 THEN /\ left_bank' = left_bank \ {x}
                                      /\ boat' = (boat \union {x})
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << left_bank, boat >>
                         /\ UNCHANGED right_bank
                    ELSE /\ right_bank # {}
                         /\ \E x \in right_bank:
                              IF Safe(left_bank) /\ Safe(right_bank \ {x}) /\ Safe(boat)
                                 THEN /\ right_bank' = right_bank \ {x}
                                      /\ boat' = (boat \union {x})
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << right_bank, boat >>
                         /\ UNCHANGED left_bank
              /\ UNCHANGED location
           \/ /\ (boat # {} /\ Cardinality(boat) <= 2 /\ F \in boat)
              /\ IF location = "left" /\ Safe(left_bank) /\ Safe(right_bank\union boat)
                    THEN /\ location' = "right"
                         /\ right_bank' = (right_bank \union boat)
                         /\ boat' = {}
                         /\ UNCHANGED left_bank
                    ELSE /\ IF location = "right" /\ Safe(right_bank) /\ Safe(left_bank\union boat)
                               THEN /\ location' = "left"
                                    /\ left_bank' = (left_bank \union boat)
                                    /\ boat' = {}
                               ELSE /\ TRUE
                                    /\ UNCHANGED << left_bank, boat, 
                                                    location >>
                         /\ UNCHANGED right_bank

Next == (\E self \in {0,1}: i(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(i(self))

\* END TRANSLATION 
====

------------------------------- MODULE OnOff -------------------------------
EXTENDS TLC
VARIABLE switch
CONSTANT ON, OFF
Init == \/ switch = ON
        \/ switch = OFF
Next == IF switch = ON THEN switch' = OFF ELSE switch' = ON
SwitchOnOrOff == switch = ON \/ switch = OFF
Spec == Init /\ [][Next]_switch
=============================================================================
\* Modification History
\* Last modified Fri Dec 29 10:32:20 EST 2023 by sca
\* Created Fri Dec 29 10:19:28 EST 2023 by sca

--------------------------- MODULE GossipGlomers2 ---------------------------
(* Challenge #2: Unique ID Generation
Nodes receive a "generate" message and they must respond with a unique ID.
This system must totally available, meaning it can continue to operate even in the face of network partitions.

Let's first proceed naively and imagine there's only one node running the service.
The client and service node will communicate over an asynchronous channel, whose specification is based on
the one found in chapter 3 of Lamport's "Specifying Systems".
*)
EXTENDS Naturals
CONSTANT IDS_TO_GENERATE
CONSTANT MAX_VAL

VARIABLE rdy, val, seen, is_unique, num_ids_generated

vars == <<rdy, val, seen, is_unique, num_ids_generated>>

TypeInvariant == /\ val \in 1..MAX_VAL
                 /\ rdy \in {0,1}
                 /\ seen \subseteq 1..MAX_VAL
                 /\ is_unique \in {TRUE, FALSE}
                 /\ num_ids_generated \in 0..IDS_TO_GENERATE-1

IsUnique == is_unique = TRUE

Init == /\ val = 0
        /\ rdy = 0
        /\ is_unique = TRUE
        /\ seen = {}
        /\ num_ids_generated = 0

RequestNewID == /\ num_ids_generated < IDS_TO_GENERATE
                /\ rdy = 0
                /\ rdy' = 1
                /\ UNCHANGED val
                /\ UNCHANGED seen
                /\ UNCHANGED is_unique
                /\ UNCHANGED num_ids_generated
                

HandleNewIDRequest == /\ num_ids_generated < IDS_TO_GENERATE
                      /\ rdy = 1
                      /\ rdy' = 0
                      /\ val' \in (1..MAX_VAL \ seen)
                      /\ is_unique' = ~(val' \in seen)
                      /\ seen' = seen \union {val'}
                      /\ num_ids_generated' = num_ids_generated + 1
                    
Finished == /\ num_ids_generated >= IDS_TO_GENERATE
            /\ UNCHANGED rdy
            /\ UNCHANGED val
            /\ UNCHANGED seen
            /\ UNCHANGED is_unique
            /\ UNCHANGED num_ids_generated
                  
Next == RequestNewID \/ HandleNewIDRequest \/ Finished
Spec == Init /\ [][Next]_vars
----------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Mon Jan 01 22:03:50 EST 2024 by sca
\* Created Sat Dec 30 10:22:28 EST 2023 by sca

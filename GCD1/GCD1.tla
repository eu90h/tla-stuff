-------------------------------- MODULE GCD1 --------------------------------
(* Our goal here is to prove that an algorithm solves the problem that it claims to solve.
Namely to prove a particular form of Euclid's algorithm, but using TLA+ instead of mathematics.
See the paper "Euclid Writes an Algorithm: A Fairy Tale" by Leslie Lamport for more depth.
*)
EXTENDS Integers, TLC
CONSTANTS M, N
(* First, let's define the divisibility relation. We say a divides b, written a | b, if there's some natural number c in [1, q] s.t. b = ac.
*)
p | q == \exists d \in 1..q : q = p * d
(* Divisors(q) will denote the set of all divisors of q, including 1 and q *)
Divisors(q) == {d \in 1 .. q : d | q}
(* Maximum(S) equals the maximal element x in S such that x \geq for all y *)
Maximum(S) == CHOOSE x \in S : \forall y \in S : x \geq y
(* GCD(p, q) is defined then as the maximum of the intersection of the divisors of p and q; that is, the largest divisor common to both p and q. *)
GCD(p, q) == Maximum(Divisors(p) \cap Divisors(q))
(* Now Euclid's algorithm can be expressed. It takes natural numbers x and y as input, and stores the result in x and y as well.
We use the GCD expression above the verify the result with an assertion.
--algorithm Euclid {
    variables x \in 1 .. M, y \in 1 .. N, x0 = x, y0 = y;
    {
        while (x # y) {
            if (x < y) {
                y := y - x;
            } else { 
                x := x - y;
            }
        };
        assert x = GCD(x0, y0) /\ y = GCD(x0, y0) 
    }
}
The TLA+ toolbox will translate the above PlusCal program into a TLA+ one below:
*)
\* BEGIN TRANSLATION (chksum(pcal) = "6fcb1b8f" /\ chksum(tla) = "d8b1bdba")
VARIABLES x, y, x0, y0, pc

vars == << x, y, x0, y0, pc >>

Init == (* Global variables *)
        /\ x \in 1 .. M
        /\ y \in 1 .. N
        /\ x0 = x
        /\ y0 = y
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(x = GCD(x0, y0) /\ y = GCD(x0, y0), 
                              "Failure of assertion at line 29, column 9.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>
         /\ UNCHANGED << x0, y0 >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu Jan 04 09:03:01 EST 2024 by sca
\* Created Thu Jan 04 06:30:29 EST 2024 by sca

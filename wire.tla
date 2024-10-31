-------------------------------- MODULE wire --------------------------------
EXTENDS Integers
(*--algorithm wire
    variables
        people = {"alice", "bob"},
        acc = [p \in people |-> 5];
begin
skip;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a0c379cf" /\ chksum(tla) = "31975730")
VARIABLES people, acc, pc

vars == << people, acc, pc >>

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [p \in people |-> 5]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << people, acc >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu Oct 31 09:03:27 GMT 2024 by frankeg
\* Created Thu Oct 31 08:50:01 GMT 2024 by frankeg

-------------------------------- MODULE wire --------------------------------
EXTENDS Integers
(*--algorithm wire
begin
skip;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "40557b85" /\ chksum(tla) = "af3d9146")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu Oct 31 09:01:49 GMT 2024 by frankeg
\* Created Thu Oct 31 08:50:01 GMT 2024 by frankeg

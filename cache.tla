------------------------------- MODULE cache -------------------------------
\* Several clients consume some shared resource that periodically renews.
(*--algorithm cache
begin
skip;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "37d3045f" /\ chksum(tla) = "af3d9146")
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
\* Last modified Fri Nov 01 16:14:42 GMT 2024 by frankeg
\* Created Fri Nov 01 16:11:59 GMT 2024 by frankeg

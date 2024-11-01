--------------------------- MODULE message_queue ---------------------------
(*--algorithm message_queue
begin
skip;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "faddc595" /\ chksum(tla) = "af3d9146")
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
\* Last modified Fri Nov 01 15:21:10 GMT 2024 by frankeg
\* Created Fri Nov 01 15:18:56 GMT 2024 by frankeg

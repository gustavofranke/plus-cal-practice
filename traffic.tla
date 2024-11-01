------------------------------ MODULE traffic ------------------------------
(*
 Imagine we have a car at a traffic light.
 We have two processes in the system.
 The traffic light alternates between red and green. 
 The car waits until the light is green before moving.
*)
(*--algorithm traffic
begin
skip;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ef7a2c38" /\ chksum(tla) = "af3d9146")
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
\* Last modified Fri Nov 01 21:50:55 GMT 2024 by frankeg
\* Created Fri Nov 01 21:48:16 GMT 2024 by frankeg

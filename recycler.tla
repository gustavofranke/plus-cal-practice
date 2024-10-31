------------------------------ MODULE recycler ------------------------------
(***********************************************************************************)
(* Imagine we have a machine that sorts material into "recyclable" and "trash."    *)
(* It has finite space for both recycling and trash.                               *)
(* Items with a specified size and type come in, one at a time,                    *)
(* and it sorts them according to the following rules:                             *)
(* 1. If the item is labeled as "recycling"                                        *)
(*    and it is under the remaining capacity for the recycling bin,                *)
(*    the item goes into recycling.                                                *)
(* 2. If the item is labeled as "trash" OR the item is labeled as "recycling"      *)
(*    and there is not enough recycling capacity                                   *)
(*    AND there is sufficient capacity in the trash bin, the item goes into trash. *)
(* 3. Otherwise, it’s dropped on the floor and somebody else gets to sweep it up.  *)
(***********************************************************************************)
EXTENDS Integers
(*--algorithm recycler
variables
begin
skip;    
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "33dbf480" /\ chksum(tla) = "af3d9146")
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
\* Last modified Thu Oct 31 11:42:49 GMT 2024 by frankeg
\* Created Thu Oct 31 11:12:44 GMT 2024 by frankeg

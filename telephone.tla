----------------------------- MODULE telephone -----------------------------
(**********************************************************************************)
(* For this example, we'll have an idealized model of sending messages            *)
(* when the receiver doesn't automatically accept them.                           *)
(* Maybe the receiver is a friend who's going in and out of cell coverage.        *) 
(* We can approximate this with a two-turn cycle:                                 *)
(* 1. On the sender's turn, they put a message in transit.                        *)
(* 2. On the receiver's turn, they either receive a message in transit            *)
(*    or do nothing (they're outside cell coverage).                              *)
(* While we have a definite order on how the messages are sent                    *)
(* and an order in which they are received, they aren't ordered while in transit. *)
(* The receiver can get the messages in transit in any order.                     *)
(* This means we have two sequences for to_send and received,                     *)
(* but a set for in_transit.                                                      *)
(**********************************************************************************)
(*---algorithm telephone
variables
begin
skip;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7c763995" /\ chksum(tla) = "af3d9146")
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
\* Last modified Thu Oct 31 12:22:56 GMT 2024 by frankeg
\* Created Thu Oct 31 12:13:35 GMT 2024 by frankeg

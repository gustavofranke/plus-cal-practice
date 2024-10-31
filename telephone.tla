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
EXTENDS Sequences, TLC
(*---algorithm telephone
variables
    to_send = <<1, 2, 3>>,
    received = <<>>,
    in_transit = {};
    can_send = TRUE;
begin
    while Len(received) /= 3 do
        \* send
        if can_send /\ to_send /= <<>> then
            in_transit := in_transit \union {Head(to_send)};
            can_send := FALSE;
            to_send := Tail(to_send);
        end if;
        \* receive
        either
            with msg \in in_transit do
                received := Append(received, msg);
                in_transit := in_transit \ {msg};
                either
                    can_send := TRUE;
                or
                    skip;
                end either;
            end with;
        or
            skip;
        end either;
    end while;
    assert received = <<1, 2, 3>>;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f7ae0df" /\ chksum(tla) = "fdf67b65")
VARIABLES to_send, received, in_transit, can_send, pc

vars == << to_send, received, in_transit, can_send, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ can_send = TRUE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) /= 3
               THEN /\ IF can_send /\ to_send /= <<>>
                          THEN /\ in_transit' = (in_transit \union {Head(to_send)})
                               /\ can_send' = FALSE
                               /\ to_send' = Tail(to_send)
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit, can_send >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ Assert(received = <<1, 2, 3>>, 
                              "Failure of assertion at line 46, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit, can_send >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = in_transit \ {msg}
              /\ \/ /\ can_send' = TRUE
                 \/ /\ TRUE
                    /\ UNCHANGED can_send
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu Oct 31 13:57:43 GMT 2024 by frankeg
\* Created Thu Oct 31 12:13:35 GMT 2024 by frankeg

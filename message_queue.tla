--------------------------- MODULE message_queue ---------------------------
EXTENDS Sequences
(*--algorithm message_queue
variable queue = <<>>;
process writer = "writer"
begin Write:
    while TRUE do
        queue := Append(queue, "msg");
    end while;
end process;
process reader = "reader"
variables current_message = "none";
begin Read:
    while TRUE do
        current_message := Head(queue);
        queue := Tail(queue);
    end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "a798b384" /\ chksum(tla) = "197f644c")
VARIABLES queue, current_message

vars == << queue, current_message >>

ProcSet == {"writer"} \cup {"reader"}

Init == (* Global variables *)
        /\ queue = <<>>
        (* Process reader *)
        /\ current_message = "none"

writer == /\ queue' = Append(queue, "msg")
          /\ UNCHANGED current_message

reader == /\ current_message' = Head(queue)
          /\ queue' = Tail(queue)

Next == writer \/ reader

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Nov 01 15:31:08 GMT 2024 by frankeg
\* Created Fri Nov 01 15:18:56 GMT 2024 by frankeg

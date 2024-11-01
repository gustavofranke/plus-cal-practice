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
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "1ade2ba" /\ chksum(tla) = "e2665637")
VARIABLE queue

vars == << queue >>

ProcSet == {"writer"}

Init == (* Global variables *)
        /\ queue = <<>>

writer == queue' = Append(queue, "msg")

Next == writer

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Nov 01 15:30:05 GMT 2024 by frankeg
\* Created Fri Nov 01 15:18:56 GMT 2024 by frankeg

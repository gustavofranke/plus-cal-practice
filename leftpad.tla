------------------------------ MODULE leftpad ------------------------------
(*
 Given a character, a length, and a string,
 return a string padded on the left with that character to length n.
 If n is less than the length of the string, output the original string. 
 For example, Leftpad(" ", 5, "foo") = "  foo" ,
 while Leftpad(" ", 1, "foo") = "foo".
*)
EXTENDS Sequences, Integers, TLC
PT == INSTANCE PT

Leftpad(c, n, str) ==
    IF n < 0 THEN str ELSE
    LET
        outlength == PT!Max(Len(str), n)
        padlength ==
            CHOOSE padlength \in 0..n:
                padlength + Len(str) = outlength
    IN
        [x \in 1..padlength |-> c] \o str
E1 == Leftpad(" ", 1, <<"f", "o", "o">>) \* <<"f", "o", "o">>
E2 == Leftpad(" ", 5, <<"f", "o", "o">>) \* <<" ", " ", "f", "o", "o">>

Characters == {"a", "b", "c"}
(*--algorithm leftpad
variables
    in_c \in Characters \union {" "},
    in_n \in 0..6,
    in_str \in PT!SeqOf(Characters, 6),
    output;
begin
    assert in_n >= 0;
    output := in_str;
    while Len(output) < in_n do
        output := <<in_c>> \o output;
    end while;
    assert output = Leftpad(in_c, in_n, in_str);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "eb236b37" /\ chksum(tla) = "f0d53092")
CONSTANT defaultInitValue
VARIABLES in_c, in_n, in_str, output, pc

vars == << in_c, in_n, in_str, output, pc >>

Init == (* Global variables *)
        /\ in_c \in (Characters \union {" "})
        /\ in_n \in 0..6
        /\ in_str \in PT!SeqOf(Characters, 6)
        /\ output = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(in_n >= 0, "Failure of assertion at line 32, column 5.")
         /\ output' = in_str
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << in_c, in_n, in_str >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF Len(output) < in_n
               THEN /\ output' = <<in_c>> \o output
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(output = Leftpad(in_c, in_n, in_str), 
                              "Failure of assertion at line 37, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED output
         /\ UNCHANGED << in_c, in_n, in_str >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Nov 03 21:19:53 GMT 2024 by frankeg
\* Created Sun Nov 03 12:21:52 GMT 2024 by frankeg

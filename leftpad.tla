------------------------------ MODULE leftpad ------------------------------
(*
 Given a character, a length, and a string,
 return a string padded on the left with that character to length n.
 If n is less than the length of the string, output the original string. 
 For example, Leftpad(" ", 5, "foo") = "  foo" ,
 while Leftpad(" ", 1, "foo") = "foo".
*)
EXTENDS Sequences, Integers
PT == INSTANCE PT

Leftpad(c, n, str) ==
    LET
        outlength == PT!Max(Len(str), n)
        padlength ==
            CHOOSE padlength \in 0..n:
                padlength + Len(str) = outlength
    IN
        [x \in 1..padlength |-> c] \o str
E1 == Leftpad(" ", 1, <<"f", "o", "o">>) \* <<"f", "o", "o">>
E2 == Leftpad(" ", 5, <<"f", "o", "o">>)
=============================================================================
\* Modification History
\* Last modified Sun Nov 03 20:58:29 GMT 2024 by frankeg
\* Created Sun Nov 03 12:21:52 GMT 2024 by frankeg

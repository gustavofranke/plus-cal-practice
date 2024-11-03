-------------------------------- MODULE max --------------------------------
(*
 Given a sequence of numbers, return the largest element of that sequence.
 For example, max(<<1, 1, 2, -1>>) = 2.
*)
EXTENDS Integers, Sequences
Max(seq) ==
    LET set == {seq[i]: i \in 1..Len(seq)}
    IN CHOOSE x \in set: \A y \in set: y <= x
=============================================================================
\* Modification History
\* Last modified Sun Nov 03 11:45:44 GMT 2024 by frankeg
\* Created Sun Nov 03 11:31:50 GMT 2024 by frankeg

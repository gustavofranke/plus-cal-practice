--------------------------- MODULE binary_search ---------------------------
(*
 A correct implementation of binary search will take approximately log2(n) comparisons.
 Can we verify an algorithm does that?
*)
EXTENDS Sequences, Integers
PT == INSTANCE PT
OrderedSeqOf(set, n) ==
    { seq \in PT!SeqOf(set, n):
        \A x \in 2..Len(seq):
            seq[x] >= seq[x-1]
    }
=============================================================================
\* Modification History
\* Last modified Sun Nov 03 21:31:32 GMT 2024 by frankeg
\* Created Sun Nov 03 21:26:45 GMT 2024 by frankeg

--------------------------- MODULE binary_search ---------------------------
(*
 A correct implementation of binary search will take approximately log2(n) comparisons.
 Can we verify an algorithm does that?
*)
EXTENDS Sequences, Integers, TLC
PT == INSTANCE PT
OrderedSeqOf(set, n) ==
    { seq \in PT!SeqOf(set, n):
        \A x \in 2..Len(seq):
            seq[x] >= seq[x-1]
    }
MaxInt == 7
Range(f) == {f[x]: x \in DOMAIN f}
\* take the number of loop iterations and exponent it, it should be under the length of the sequence
Pow2(n) ==
    LET f[x \in 0..n] ==
        IF x = 0
        THEN 1
        ELSE 2*f[x-1]
    IN f[n]
E1 == {Pow2(x): x \in 0..5} \* {1, 2, 4, 8, 16, 32}
(*--algorithm binary_search
variables
    low = 1,
    seq \in OrderedSeqOf(1..MaxInt, MaxInt),
    high = Len(seq),
    target \in 1..MaxInt,
    found_index = 0;
    counter = 0;
begin
    Search:
        while low <= high do
            counter := counter + 1;
            with
                lh = low + high,
                m = lh \div 2
            do 
                    assert lh <= MaxInt;
                    if seq[m] = target then
                        found_index := m;
                        goto Result;
                    elsif seq[m] < target then
                        low := m + 1;
                    else
                        high := m - 1;
                    end if;
            end with;
        end while;
    Result:
        if Len(seq) > 0 then
            assert Pow2(counter - 1) <= Len(seq);
        end if;
        if target \in Range(seq) then
            assert seq[found_index] = target;
        else
            \* 0 is out of DOMAIN seq, so can represent "not found"
            assert found_index = 0;
        end if;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "bd03ea2e" /\ chksum(tla) = "d0960456")
VARIABLES low, seq, high, target, found_index, counter, pc

vars == << low, seq, high, target, found_index, counter, pc >>

Init == (* Global variables *)
        /\ low = 1
        /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
        /\ high = Len(seq)
        /\ target \in 1..MaxInt
        /\ found_index = 0
        /\ counter = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF low <= high
                THEN /\ counter' = counter + 1
                     /\ LET lh == low + high IN
                          LET m == lh \div 2 IN
                            /\ Assert(lh <= MaxInt, 
                                      "Failure of assertion at line 39, column 21.")
                            /\ IF seq[m] = target
                                  THEN /\ found_index' = m
                                       /\ pc' = "Result"
                                       /\ UNCHANGED << low, high >>
                                  ELSE /\ IF seq[m] < target
                                             THEN /\ low' = m + 1
                                                  /\ high' = high
                                             ELSE /\ high' = m - 1
                                                  /\ low' = low
                                       /\ pc' = "Search"
                                       /\ UNCHANGED found_index
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << low, high, found_index, counter >>
          /\ UNCHANGED << seq, target >>

Result == /\ pc = "Result"
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter - 1) <= Len(seq), 
                               "Failure of assertion at line 52, column 13.")
                ELSE /\ TRUE
          /\ IF target \in Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 55, column 13.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 58, column 13.")
          /\ pc' = "Done"
          /\ UNCHANGED << low, seq, high, target, found_index, counter >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Nov 03 22:04:13 GMT 2024 by frankeg
\* Created Sun Nov 03 21:26:45 GMT 2024 by frankeg

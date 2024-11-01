------------------------------ MODULE knapsack ------------------------------
(*
The Knapsack Problem is an optimization problem that’s known to be NP-complete.
We can define it as: 
We have a knapsack of volume N and a set of items.
Each item has a value and a size.
You can fit any number of each item in the knapsack as long as
the sum of them all is less than the capacity of the sack.
What’s the most valuable knapsack you can make?
*)
EXTENDS TLC, Integers, Sequences
PT == INSTANCE PT
Capacity == 7
Items == {"a", "b", "c"}

HardcodedItemSet == [
    a |-> [size |-> 1, value |-> 1],
    b |-> [size |-> 2, value |-> 3],
    c |-> [size |-> 3, value |-> 1]
]

ValueOf(item) == HardcodedItemSet[item].value
E1 == ValueOf("b")
ItemParams == [size: 2..4, value: 0..5]

\* the possible inputs we care about
ItemSets == [Items -> ItemParams]

\* a measure of what counts as a valid knapsack.
KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)
ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

\* the best valid knapsack is the one with the highest possible value
\* A minor amount of duplicate code
KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

BestKnapsack(itemset) ==
    LET all == ValidKnapsacks(itemset)
    IN CHOOSE best \in all:
        \A worse \in all \ {best}:
        KnapsackValue(best, itemset) > KnapsackValue(worse, itemset)
E2 == BestKnapsack(HardcodedItemSet)
E3 == KnapsackValue([a |-> 1, b |-> 3, c |-> 0], HardcodedItemSet)
\*E4 == {BestKnapsack(itemset) : itemset \in ItemSets}
\* Attempted to compute the value of an expression of form
\* CHOOSE x \in S: P, but no element of S satisfied P.
\* Why does nothing satisfy it?
\* In this case, we don’t have any information on which ItemSet caused the problem.
\* For debugging purposes, let’s make this a PlusCal algorithm, so we get a trace.


\* Choose the subset of valid knapsacks that are higher than everything outside of that set.
\* This most closely matches the defintion of "best knapsacks".
BestKnapsacksOne(itemset) ==
    LET all == ValidKnapsacks(itemset)
    IN CHOOSE all_the_best \in SUBSET all:
        /\ \E good \in all_the_best:
            /\ \A other \in all_the_best:
                KnapsackValue(good, itemset) = KnapsackValue(other, itemset)
            /\ \A worse \in all \ all_the_best:
                KnapsackValue(good, itemset) > KnapsackValue(worse, itemset)

\* Pick a best knapsack arbitrarily, calculate its value, and filter for all the other knapsacks that match it.
BestKnapsacksTwo(itemset) ==
    LET
        value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                value(best) >= value(worse)
        value_of_best == KnapsackValue(best, itemset)
    IN
        {k \in all: value_of_best = KnapsackValue(k, itemset)}

E4 == \A is \in ItemSets: BestKnapsacksTwo(is) = BestKnapsacksOne(is)
E5 == LET is == CHOOSE is \in ItemSets:
    BestKnapsacksTwo(is) /= BestKnapsacksOne(is)
    IN <<is, BestKnapsacksOne(is), BestKnapsacksTwo(is)>>

(*--algorithm debug
variables itemset \in ItemSets
begin
    assert BestKnapsack(itemset) \in ValidKnapsacks(itemset);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e9e49621" /\ chksum(tla) = "e319b293")
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(BestKnapsack(itemset) \in ValidKnapsacks(itemset), 
                   "Failure of assertion at line 88, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED itemset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Nov 01 14:03:06 GMT 2024 by frankeg
\* Created Fri Nov 01 12:03:42 GMT 2024 by frankeg

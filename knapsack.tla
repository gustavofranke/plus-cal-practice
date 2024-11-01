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
E4 == {BestKnapsack(itemset) : itemset \in ItemSets}
\* Attempted to compute the value of an expression of form
\* CHOOSE x \in S: P, but no element of S satisfied P.
\* Why does nothing satisfy it?
\* In this case, we don’t have any information on which ItemSet caused the problem.
\* For debugging purposes, let’s make this a PlusCal algorithm, so we get a trace.

=============================================================================
\* Modification History
\* Last modified Fri Nov 01 12:50:58 GMT 2024 by frankeg
\* Created Fri Nov 01 12:03:42 GMT 2024 by frankeg

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
ItemSets == [a: ItemParams, b: ItemParams, c: ItemParams]
=============================================================================
\* Modification History
\* Last modified Fri Nov 01 12:22:27 GMT 2024 by frankeg
\* Created Fri Nov 01 12:03:42 GMT 2024 by frankeg

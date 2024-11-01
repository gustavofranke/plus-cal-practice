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

HardcodedItemSet == {
    [item |-> "a", size |-> 1, value |-> 1],
    [item |-> "b", size |-> 2, value |-> 3],
    [item |-> "c", size |-> 3, value |-> 1]
}

ValueOf(item) == (CHOOSE struct \in HardcodedItemSet: struct.item = item).value
E1 == ValueOf("b")
=============================================================================
\* Modification History
\* Last modified Fri Nov 01 12:11:33 GMT 2024 by frankeg
\* Created Fri Nov 01 12:03:42 GMT 2024 by frankeg

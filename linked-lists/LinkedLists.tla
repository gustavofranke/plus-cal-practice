---------------------------- MODULE LinkedLists ----------------------------
CONSTANT NULL
LOCAL INSTANCE FiniteSets \* For Cardinality
LOCAL INSTANCE Sequences \* For len
LOCAL INSTANCE TLC \* For Assert
LOCAL INSTANCE Integers \* For a..b
PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]

\* While Range is defined in PT, we don't want a generic module reliant on PT!
Range(f) == {f[x]: x \in DOMAIN f}
\* PointerMap is an element of PointerMaps
isLinkedList(PointerMap) ==
    LET
        nodes == DOMAIN PointerMap
        all_seqs == [1..Cardinality(nodes) -> nodes]
    IN \E ordering \in all_seqs:
        \* each node points to the next node in the ordering
        /\ \A i \in 1..Len(ordering) - 1:
            PointerMap[ordering[i]] = ordering[i+1]
        /\ nodes \subseteq Range(ordering)

LinkedLists(Nodes) ==
    IF NULL \in Nodes THEN Assert(FALSE, "NULL cannot be in Nodes") ELSE
    LET
        node_subsets == (SUBSET Nodes \ {{}})
        pointer_maps_sets == {PointerMaps(subn): subn \in node_subsets}
        all_pointer_maps == UNION pointer_maps_sets
    IN {pm \in all_pointer_maps : isLinkedList(pm)}

Ring(LL) == (DOMAIN LL = Range(LL))
First(LL) ==
    IF Ring(LL)
    THEN CHOOSE node \in DOMAIN LL:
        TRUE
    ELSE CHOOSE node \in DOMAIN LL:
        node \notin Range(LL)
=============================================================================
\* Modification History
\* Last modified Thu Nov 07 21:35:18 GMT 2024 by frankeg
\* Created Mon Nov 04 09:09:26 GMT 2024 by frankeg

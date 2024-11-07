---------------------------- MODULE LinkedLists ----------------------------
CONSTANT NULL
LOCAL INSTANCE TLC \* For Assert
PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]
LinkedLists(Nodes) ==
    IF NULL \in Nodes THEN Assert(FALSE, "NULL cannot be in Nodes") ELSE
    LET
        node_subsets == (SUBSET NODES \ {{}})
        pointer_maps_sets == {PointerMaps(subn): subn \in node_subsets}
        all_pointer_maps == UNION pointer_maps_sets
    IN {pm \in all_pointer_maps : isLinkedList(pm)}

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
\* While Range is defined in PT, we don't want a generic module reliant on PT!
Range(f) == {f[x]: x \in DOMAIN f}
=============================================================================
\* Modification History
\* Last modified Thu Nov 07 21:18:00 GMT 2024 by frankeg
\* Created Mon Nov 04 09:09:26 GMT 2024 by frankeg

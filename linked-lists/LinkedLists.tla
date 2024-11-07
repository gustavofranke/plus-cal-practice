---------------------------- MODULE LinkedLists ----------------------------
CONSTANT NULL
LOCAL INSTANCE TLC \* For Assert
PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]
\*LinkedLists(Nodes) ==
\*    IF NULL \in Nodes THEN Assert(FALSE, "NULL cannot be in Nodes") ELSE

\* PointerMap is an element of PointerMaps
isLinkedList(PointerMap) ==
    LET
        nodes == DOMAIN PointerMap
        all_seqs == [1..Cardinality(nodes) -> nodes]
    IN \E ordering \in all_seqs:
        \* each node points to the next node in the ordering
        /\ \A i \in 1..Len(ordering) - 1:
            PointerMap[ordering[i]] = ordering[i+1]
        \* all nodes in the mapping appear in the ordering
        /\ \A n \in nodes:
            \E i \in 1..Len(ordering):
                ordering[i] = n    
=============================================================================
\* Modification History
\* Last modified Thu Nov 07 21:03:27 GMT 2024 by frankeg
\* Created Mon Nov 04 09:09:26 GMT 2024 by frankeg

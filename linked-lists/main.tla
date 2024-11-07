-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, FiniteSets, Sequences
CONSTANTS Nodes, NULL
INSTANCE LinkedLists WITH NULL <- NULL
AllLinkedLists == LinkedLists(Nodes)
CycleImpliesTwoParents(ll) ==
    Cyclic(ll) <=>
        \/ Ring(ll)
        \/ \E n \in DOMAIN ll:
            Cardinality({p \in DOMAIN ll: ll[p] = n}) = 2
Valid ==
 /\ \A ll \in AllLinkedLists:
    /\ Assert(CycleImpliesTwoParents(ll), <<"Counterexample:", ll>>)
=============================================================================
\* Modification History
\* Last modified Thu Nov 07 21:48:12 GMT 2024 by frankeg
\* Created Mon Nov 04 09:09:02 GMT 2024 by frankeg

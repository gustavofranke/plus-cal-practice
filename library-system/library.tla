------------------------------ MODULE library ------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANTS Books, People, NumCopies
ASSUME NumCopies \subseteq Nat
set ++ x == set \union {x}
set -- x == set \ {x}
(*--algorithm library
variables
    library \in [Books -> NumCopies];
define 
    AvailableBooks == {b \in Books: library[b] > 0}
end define;
fair process person \in People
variables
    books = {};
begin
    Person:
        either
            \* Checkout
            with b \in AvailableBooks \ books do
                library[b] := library[b] - 1;
                books := books ++ b;
            end with;
        or
            \* Return
            with b \in books do
                library[b] := library[b] + 1;
                books := books -- b;
            end with;
        end either;
    goto Person;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "dcc9b141" /\ chksum(tla) = "705db726")
VARIABLES library, pc

(* define statement *)
AvailableBooks == {b \in Books: library[b] > 0}

VARIABLE books

vars == << library, pc, books >>

ProcSet == (People)

Init == (* Global variables *)
        /\ library \in [Books -> NumCopies]
        (* Process person *)
        /\ books = [self \in People |-> {}]
        /\ pc = [self \in ProcSet |-> "Person"]

Person(self) == /\ pc[self] = "Person"
                /\ \/ /\ \E b \in AvailableBooks \ books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] - 1]
                           /\ books' = [books EXCEPT ![self] = books[self] ++ b]
                   \/ /\ \E b \in books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] + 1]
                           /\ books' = [books EXCEPT ![self] = books[self] -- b]
                /\ pc' = [pc EXCEPT ![self] = "Person"]

person(self) == Person(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in People: person(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in People : WF_vars(person(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
TypeInvariant ==
    /\ library \in [Books -> NumCopies ++ 0]
    /\ books \in [People -> SUBSET books]
=============================================================================
\* Modification History
\* Last modified Sat Nov 09 21:35:30 GMT 2024 by frankeg
\* Created Fri Nov 08 21:24:01 GMT 2024 by frankeg

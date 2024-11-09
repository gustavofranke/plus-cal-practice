------------------------------ MODULE library ------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANTS Books, People, NumCopies
ASSUME NumCopies \subseteq Nat
set ++ x == set \union {x}
set -- x == set \ {x}
(*--algorithm library
variables
    library \in [Books -> NumCopies],
    reserves = [b \in Books |-> {}];
    wants \in SUBSET Books;
define 
    AvailableBooks == {b \in Books: library[b] > 0}
    BorrowableBooks(p) == {b \in AvailableBooks: reserves[b] = {} \/ p \in reserves[b]}
end define;
fair process person \in People
variables
    books = {};
begin
    Person:
        either
            \* Checkout
            with b \in BorrowableBooks(self) \ books do
                library[b] := library[b] - 1;
                books := books ++ b;
                wants := wants -- b;
            end with;
        or
            \* Return
            with b \in books do
                library[b] := library[b] + 1;
                books := books -- b;
            end with;
        or
            \* Reserve:
            with b \in Books do
                reserves[b] := reserves[b] ++ self;
            end with;
        end either;
    goto Person;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "91398d0e" /\ chksum(tla) = "1d777cde")
VARIABLES library, reserves, wants, pc

(* define statement *)
AvailableBooks == {b \in Books: library[b] > 0}
BorrowableBooks(p) == {b \in AvailableBooks: reserves[b] = {} \/ p \in reserves[b]}

VARIABLE books

vars == << library, reserves, wants, pc, books >>

ProcSet == (People)

Init == (* Global variables *)
        /\ library \in [Books -> NumCopies]
        /\ reserves = [b \in Books |-> {}]
        /\ wants \in SUBSET Books
        (* Process person *)
        /\ books = [self \in People |-> {}]
        /\ pc = [self \in ProcSet |-> "Person"]

Person(self) == /\ pc[self] = "Person"
                /\ \/ /\ \E b \in BorrowableBooks(self) \ books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] - 1]
                           /\ books' = [books EXCEPT ![self] = books[self] ++ b]
                           /\ wants' = wants -- b
                      /\ UNCHANGED reserves
                   \/ /\ \E b \in books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] + 1]
                           /\ books' = [books EXCEPT ![self] = books[self] -- b]
                      /\ UNCHANGED <<reserves, wants>>
                   \/ /\ \E b \in Books:
                           reserves' = [reserves EXCEPT ![b] = reserves[b] ++ self]
                      /\ UNCHANGED <<library, wants, books>>
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
    /\ wants \in [People -> SUBSET Books]
Liveness == /\ <>(\A p \in People: wants[p] = {})
=============================================================================
\* Modification History
\* Last modified Sat Nov 09 21:43:25 GMT 2024 by frankeg
\* Created Fri Nov 08 21:24:01 GMT 2024 by frankeg

------------------------------- MODULE debug -------------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC
E0 == 1 + 2

E1 == 1 = 2
E2 == 1 /= 2
E3 == TRUE /\ FALSE
E4 == TRUE \/ FALSE
E5 == ~TRUE

E6 == 1..3
E7 == 1 \in 1..2
E8 == 1 \notin 1..2
E9 == {1, 2} \subseteq {1, 2, 3}
E10 == (1..2) \union (2..3)
E11 == (1..2) \intersect (2..3)
E12 == (1..2) \ (2..3)
E13 == Cardinality({"a", "b"})

E14 == {x \in 1..2: x < 2}
E15 == {x * 2: x \in 1..2}

E16 == <<"a", {1, 2}>>
E17 == E16[1]
E18 == E16[2]
E19 == Head(<<1, 2>>)
E20 == Tail(<<1, 2, 3>>)
E21 == Append(<<1, 2>>, 3)
E22 == <<1>> \o <<2, 3>>
E23 == Len(<<1, 1, 1, 1>>)
E24 == [a |-> 1, b |-> <<1, {}>>].b

E25 == SUBSET {"a", "b"}
E26 == {"a", "b", "c"} \X (1..2)
E27 == <<1, 2, 3>> \in (1..3) \X (1..3) \X (1..3)
E28 == <<1, 2, 3>> \in (1..3) \X ((1..3) \X (1..3))

E29 == [a: {"a", "b"}]
E30 == [a: {"a", "b"}, b: (1..2)]

Add(a, b) == a + b
Apply(op(_, _), x, y) == op(x, y)
E31 == Apply(Add, 1, 2)

set ++ elem == set \union {elem}
set -- elem == set \ {elem}
E32 == {1, 2} ++ 3
E33 == {1, 2} -- 2

AllLessThan(set, max) == \A num \in set: num < max
E34 == AllLessThan({1, 3}, 4)
E35 == AllLessThan({1, 3}, 2)
E36 == AllLessThan({1, 3}, "FOO")

SeqOverlapsSet(seq, set) == \E x \in 1..Len(seq): seq[x] \in set
E37 == SeqOverlapsSet(<<1, 3>>, {2, 3, 4})

Xor(A, B) == (~A /\ B) \/ (A /\ ~B)
OtherXor(A, B) == ~A <=> B
E38 == \A A \in BOOLEAN, B \in BOOLEAN: Xor(A, B) = OtherXor(A, B)

RotateRight(seq) ==
    LET
        last == seq[Len(seq)]
        first == SubSeq(seq, 1, Len(seq) - 1)
    IN <<last>> \o first
E39 == RotateRight(<<1, 2, 3>>)

Max(x, y) == IF x > y THEN x ELSE y
E40 == <<Max(2, 3), Max(3, 2)>>

Case(x) ==
    CASE x = 1 -> TRUE
      [] x = 2 -> TRUE
      [] x = 3 -> 7
      [] OTHER -> FALSE
E41 == <<Case(1), Case(2), Case(3), Case(4), Case(5)>>

IndexOf(seq, elem) == CHOOSE i \in 1..Len(seq): seq[i] = elem
E42 == IndexOf(<<8, 3, 1>>, 3)
E43 == IndexOf(<<8, 3, 1>>, 4)

Max2(set) == CHOOSE x \in set: \A y \in set: x >= y
E44 == Max2(1..10)

\* what values for x and y satisfy the two equations 2x + y =  − 2 and 3x − 2y = 11?
E45 == CHOOSE <<x, y>> \in (-10..10) \X (-10..10):
        /\ 2*x + y = -2
        /\ 3*x - 2*y = 11
        
\* All functions have the form [x \in set |-> P(x)]
E46 == [x \in 1..2 |-> x * 2]
E47 == Head([x \in 1..2 |-> x * 2])

\* You can make a function as an operator
MapToSomeNumber(set, num) == [x \in set |-> num]

SumUpTo(n) ==
    LET F[m \in 0..n] ==
        IF m = 0 THEN 0
        ELSE m + F[m-1]
    IN F[n]
E48 == SumUpTo(10)

PT == INSTANCE PT
SumUpTo2(n) ==
    PT!ReduceSet(LAMBDA x, y: x + y, 0..n, 0)
E49 == SumUpTo2(10)

\* domain
F[x \in BOOLEAN] == x
G == <<6, 0, 9>>
H == [F |-> DOMAIN F, G |-> DOMAIN G]
E50 == H
E51 == DOMAIN H

\* f @@ g merges two function
Merge(f, g) == [
    x \in (DOMAIN f) \union (DOMAIN g) |-> IF x \in DOMAIN f THEN f[x] ELSE g[x]
    ]
f[x \in 1..2] == "a"
g[x \in 2..3] == "b"
E52 == f @@ g
E53 == g @@ f

\* a :> b is the function [x \in {a} |-> b]
E54 == (2  :> 3)[2]
E55 == ("a" :> "b").a

\* Sets of Functions
\*[set1 -> set2] is the set of all functions that map elements of set1 to elements of set2.
E56 == [s \in {"a", "b"} |-> {1, 2}]
E57 == [{"a", "b"} -> {1, 2}]

SeqOf(set, count) == [1..count -> set]
E58 == SeqOf({"a", "b", "c"}, 2)
=============================================================================
\* Modification History
\* Last modified Thu Oct 31 22:30:11 GMT 2024 by frankeg
\* Created Thu Oct 31 16:54:07 GMT 2024 by frankeg

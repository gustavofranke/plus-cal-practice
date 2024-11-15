----------------------------- MODULE backmatter -----------------------------
EXTENDS Integers, FiniteSets
CONSTANT counter, change \* <- 0
\* return the numbers in that set that are the sum of two other numbers in it
FilterSums(set) ==
    { x \in set: \E y, z \in set \ {x}: y /= z /\ x = y + z }

\*E0 ==
\*    either
\*        with change \in 1..10 do
\*            counter := counter + change;
\*        end with;
\*    or
\*        counter := 0;
\*    end either;

E1 == {1, 1} \* a set
\* {1}

E2 == <<1, 2>> \* not a set
\* <<1, 2>>

E3 == {}
\* {}

E4 == {{}}
\* {{}}

E5 == Cardinality({{}})
\* 1

E6 == TRUE \in BOOLEAN
\* TRUE

E7 == BOOLEAN
\* {FALSE, TRUE}

(******************* Propositional Logic *******************)
\* Propositional Logic is how we determine statements are true or false.

\*| A | B | A ∧ B | A ∨ B |
\*|---|---|-------|-------|
\*| T | T |   T   |   T   |
\*| T | F |   F   |   T   |
\*| F | T |   F   |   T   |
\*| F | F |   F   |   F   |
E8 == {<<A, B,  A  /\  B, A \/ B>>  : A,  B  \in BOOLEAN}
\* { <<FALSE, FALSE, FALSE, FALSE>>,
\*     <<FALSE, TRUE, FALSE, TRUE>>,
\*     <<TRUE, FALSE, FALSE, TRUE>>,
\*     <<TRUE, TRUE, TRUE, TRUE>> }

\*| A | ¬A | ¬(¬A)|
\*|---|----|------|
\*| T |  F |  T   |
\*| F |  T |  F   |
E9 == {<<A, ~A,  ~(~A)>> : A \in BOOLEAN}
\* {<<FALSE, TRUE, FALSE>>,
\*  <<TRUE, FALSE, TRUE>>}

\*| P | Q | P ⇒ Q | ¬P ∨ Q |
\*| T | T |   T   |   T    |
\*| T | F |   F   |   F    |
\*| F | T |   T   |   T    |
\*| F | F |   T   |   T    |
E10 == {<<P, Q,  P  => Q, ~P \/ Q>>  : P, Q  \in BOOLEAN}
\*{ <<FALSE, FALSE, TRUE, TRUE>>,
\*     <<FALSE, TRUE, TRUE, TRUE>>,
\*     <<TRUE, FALSE, FALSE, FALSE>>,
\*     <<TRUE, TRUE, TRUE, TRUE>> }

E11 == TRUE /\ FALSE
\* FALSE

\*  with set comprehensions, we can create a complete truth table for an expression
E12 == {<<A, B,  A  =>  B>>  : A,  B  \in BOOLEAN}
\* { <<FALSE, FALSE, TRUE>>,
\*     <<FALSE, TRUE, TRUE>>,
\*     <<TRUE, FALSE, FALSE>>,
\*     <<TRUE, TRUE, TRUE>> }
(******************* Sets *******************)
E13 == {1} /= {2}
\* TRUE

E14 == {1, 2} = {1, 2}
\* TRUE

\* S1 is a subset of S2 if every element of S1 is also an element of S2
E15 == {1} \subseteq {1, 2}
\* TRUE

E16 == {1, 3} \subseteq {1, 2}
\* FALSE

E17 == {1, 2} \union {1, 3}
\* {1, 2, 3}

E18 == {1, 2} \intersect {1, 3}
\* {1}

\* set difference of two sets, is all of the elements of S1 that are not in S2
E19 == {1, 2} \ {1, 3}
\* {2}

(******************* Predicate Logic *******************)
\* By combining propositional logic and set theory, we get predicate logic
\* Predicates extend propositons with two logical statements, called quantifiers

\* ∃ b ∈ Bool : b ∨ b is true, since T ∨ T is true.
E20 == \E b \in BOOLEAN : b \/ b
\* TRUE

\* ∀ b ∈ Bool : b ∨ b is false, since F ∨ F is false.
E21 == \A b \in BOOLEAN : b \/ b
\* FALSE

\* ∃ b ∈ Bool : b ∨ ¬ b is true, since T ∨ ¬ T is true.
E22 == \E b \in BOOLEAN : b \/ ~b
\* TRUE

\* ∀ b ∈ Bool : b ∨ ¬ b is true, since it’s true for all (two) elements of Bool.
E23 == \A b \in BOOLEAN : b \/ ~b
\* TRUE

\* ∃ b ∈ Bool : b ∧ ¬ b is false, since it’s false for both T and F.
E24 == \E b \in BOOLEAN : b /\ ~b
\* FALSE

\* ∀ b ∈ Bool : b ∧ ¬ b is false, because it’s not true for at least one element.
E25 == \A b \in BOOLEAN : b /\ ~b
\* FALSE

(******************* Evaluating Predicates in TLA+ *******************)
\*\* We can quantify over finite sets, though, such as BOOLEAN
E26 == \A A, B \in BOOLEAN: (A => B) <=> (~A \/ B)
\* TRUE

E27 == \A A, B \in BOOLEAN: A <=> ~B
\* FALSE

E28 == \A A \in BOOLEAN: \E B \in BOOLEAN: A <=> ~B
\* TRUE

E29 == \E B \in BOOLEAN: ~(\A A \in BOOLEAN: A <=> ~B)
\* TRUE

\* We can use this to compare equations and check if two equations are substitutable.
E30 == \A A, B \in BOOLEAN: ~(A /\ B) = ~A \/ ~B
\* TRUE
=============================================================================
\* Modification History
\* Last modified Fri Nov 15 11:58:49 GMT 2024 by frankeg
\* Created Tue Nov 12 21:43:58 GMT 2024 by frankeg

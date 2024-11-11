----------------------------- MODULE mapreduce -----------------------------
EXTENDS TLC, Sequences, Integers
PT == INSTANCE PT
CONSTANTS Workers, Reducer, NULL
PossibleInputs == PT!TupleOf(0..2, 4)
SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)
(*--algorithm mapreduce
variables
    input \in PossibleInputs,
    result = [w \in Workers |-> NULL];
process reducer = Reducer
variables
    final = 0
    consumed = [w \in Workers |-> FALSE];
begin
    Schedule:
        skip;
    ReduceResult:
        while \E w \in Workers: ~consumed[w] do
            with w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL} do
                final := final + result[w];
                consumed[w] := TRUE;
            end with;
        end while;
    Finish:
        assert final = SumSeq(input);
end process;
process worker \in Workers
begin
    Worker:
        result[self] :=  5;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9ed4ea25" /\ chksum(tla) = "b8e4043c")
VARIABLES input, result, pc, final

vars == << input, result, pc, final >>

ProcSet == {Reducer} \cup (Workers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ result = [w \in Workers |-> NULL]
        (* Process reducer *)
        /\ final = 0
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in Workers -> "Worker"]

Schedule == /\ pc[Reducer] = "Schedule"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
            /\ UNCHANGED << input, result, final >>

ReduceResult == /\ pc[Reducer] = "ReduceResult"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                /\ UNCHANGED << input, result, final >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(final = SumSeq(input), 
                    "Failure of assertion at line 19, column 9.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, result, final >>

reducer == Schedule \/ ReduceResult \/ Finish

Worker(self) == /\ pc[self] = "Worker"
                /\ result' = [result EXCEPT ![self] = 5]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << input, final >>

worker(self) == Worker(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reducer
           \/ (\E self \in Workers: worker(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
=============================================================================
\* Modification History
\* Last modified Mon Nov 11 14:25:51 GMT 2024 by frankeg
\* Created Mon Nov 11 10:41:54 GMT 2024 by frankeg

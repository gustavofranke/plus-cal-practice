----------------------------- MODULE mapreduce -----------------------------
EXTENDS TLC, Sequences, Integers
PT == INSTANCE PT
CONSTANTS Workers, Reducer, NULL
PossibleInputs == PT!TupleOf(0..2, 4)
SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)
(*--algorithm mapreduce
variables
    input \in PossibleInputs,
    result = [w \in Workers |-> NULL],
    queue = [w \in Workers |-> <<1, 2>>]; \* for testing
process reducer = Reducer
variables
    final = 0,
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
variables
    total = 0;
begin
    WaitForQueue:
        await queue[self] /= <<>>;
    Process:
        while queue[self] /= <<>> do
            total := total + Head(queue[self]);
            queue[self] := Tail(queue[self]);
        end while;
    Result:
        result[self] :=  total;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9f52ad73" /\ chksum(tla) = "1fb52e27")
VARIABLES input, result, queue, pc, final, consumed, total

vars == << input, result, queue, pc, final, consumed, total >>

ProcSet == {Reducer} \cup (Workers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ result = [w \in Workers |-> NULL]
        /\ queue = [w \in Workers |-> <<1, 2>>]
        (* Process reducer *)
        /\ final = 0
        /\ consumed = [w \in Workers |-> FALSE]
        (* Process worker *)
        /\ total = [self \in Workers |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in Workers -> "WaitForQueue"]

Schedule == /\ pc[Reducer] = "Schedule"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
            /\ UNCHANGED << input, result, queue, final, consumed, total >>

ReduceResult == /\ pc[Reducer] = "ReduceResult"
                /\ IF \E w \in Workers: ~consumed[w]
                      THEN /\ \E w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL}:
                                /\ final' = final + result[w]
                                /\ consumed' = [consumed EXCEPT ![w] = TRUE]
                           /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
                      ELSE /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                           /\ UNCHANGED << final, consumed >>
                /\ UNCHANGED << input, result, queue, total >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(final = SumSeq(input), 
                    "Failure of assertion at line 27, column 9.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, result, queue, final, consumed, total >>

reducer == Schedule \/ ReduceResult \/ Finish

WaitForQueue(self) == /\ pc[self] = "WaitForQueue"
                      /\ queue[self] /= <<>>
                      /\ pc' = [pc EXCEPT ![self] = "Process"]
                      /\ UNCHANGED << input, result, queue, final, consumed, 
                                      total >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF queue[self] /= <<>>
                       THEN /\ total' = [total EXCEPT ![self] = total[self] + Head(queue[self])]
                            /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                            /\ pc' = [pc EXCEPT ![self] = "Process"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Result"]
                            /\ UNCHANGED << queue, total >>
                 /\ UNCHANGED << input, result, final, consumed >>

Result(self) == /\ pc[self] = "Result"
                /\ result' = [result EXCEPT ![self] = total[self]]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << input, queue, final, consumed, total >>

worker(self) == WaitForQueue(self) \/ Process(self) \/ Result(self)

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
\* Last modified Mon Nov 11 14:49:46 GMT 2024 by frankeg
\* Created Mon Nov 11 10:41:54 GMT 2024 by frankeg

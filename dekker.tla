------------------------------- MODULE dekker -------------------------------
(*
 Dekker’s Algorithm was, historically, the first successful algorithm to allow
 two threads to share a single resource without having a race condition.
 It guarantees that both threads will eventually perform their update,
 but not at the same time, and without using any CPU-specific features.
 The only thing you need is some shared memory.
 The grain of atomicity here is a single CPU instruction.
 We represent the set of instructions where the thread is updating
 the resource as the critical section.
*)
EXTENDS TLC, Integers, Sequences
\*CONSTANT Threads
Threads == 1..2
(*--algorithm dekker
variables
    flag = [t \in Threads |-> FALSE];
    next_thread \in Threads;
procedure thread()
begin
    P1: flag[self] := TRUE;
    \* all threads except self are false
    P2:
        while \E t \in Threads \ {self}: flag[t] do
            P2_1:
                if next_thread /= self then
                    P2_1_1: flag[self] := FALSE;
                    P2_1_2: await next_thread = self;
                    P2_1_3: flag[self] := TRUE;
                end if;
        end while;
    CS: skip;
    P3: with t \in Threads \ {self} do
        next_thread := t;
    end with;
    P4: flag[self] := FALSE;
    P5: goto P1;
end procedure;
fair process fair_thread \in {1}
begin
    Fair:
        call thread();
end process;
process crashable_thread \in {2}
begin
    Crashable:
        call thread();
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "dd0f4112" /\ chksum(tla) = "457367b4")
VARIABLES flag, next_thread, pc, stack

vars == << flag, next_thread, pc, stack >>

ProcSet == ({1}) \cup ({2})

Init == (* Global variables *)
        /\ flag = [t \in Threads |-> FALSE]
        /\ next_thread \in Threads
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {1} -> "Fair"
                                        [] self \in {2} -> "Crashable"]

P1(self) == /\ pc[self] = "P1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << next_thread, stack >>

P2(self) == /\ pc[self] = "P2"
            /\ IF \E t \in Threads \ {self}: flag[t]
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << flag, next_thread, stack >>

P2_1(self) == /\ pc[self] = "P2_1"
              /\ IF next_thread /= self
                    THEN /\ pc' = [pc EXCEPT ![self] = "P2_1_1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "P2"]
              /\ UNCHANGED << flag, next_thread, stack >>

P2_1_1(self) == /\ pc[self] = "P2_1_1"
                /\ flag' = [flag EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "P2_1_2"]
                /\ UNCHANGED << next_thread, stack >>

P2_1_2(self) == /\ pc[self] = "P2_1_2"
                /\ next_thread = self
                /\ pc' = [pc EXCEPT ![self] = "P2_1_3"]
                /\ UNCHANGED << flag, next_thread, stack >>

P2_1_3(self) == /\ pc[self] = "P2_1_3"
                /\ flag' = [flag EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "P2"]
                /\ UNCHANGED << next_thread, stack >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ UNCHANGED << flag, next_thread, stack >>

P3(self) == /\ pc[self] = "P3"
            /\ \E t \in Threads \ {self}:
                 next_thread' = t
            /\ pc' = [pc EXCEPT ![self] = "P4"]
            /\ UNCHANGED << flag, stack >>

P4(self) == /\ pc[self] = "P4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ UNCHANGED << next_thread, stack >>

P5(self) == /\ pc[self] = "P5"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ UNCHANGED << flag, next_thread, stack >>

thread(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_1_1(self)
                   \/ P2_1_2(self) \/ P2_1_3(self) \/ CS(self) \/ P3(self)
                   \/ P4(self) \/ P5(self)

Fair(self) == /\ pc[self] = "Fair"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "thread",
                                                       pc        |->  "Done" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "P1"]
              /\ UNCHANGED << flag, next_thread >>

fair_thread(self) == Fair(self)

Crashable(self) == /\ pc[self] = "Crashable"
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "thread",
                                                            pc        |->  "Done" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "P1"]
                   /\ UNCHANGED << flag, next_thread >>

crashable_thread(self) == Crashable(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: thread(self))
           \/ (\E self \in {1}: fair_thread(self))
           \/ (\E self \in {2}: crashable_thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1} : WF_vars(fair_thread(self)) /\ WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
AtMostOneCritical ==
    \A t1, t2 \in Threads:
        t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")
Liveness ==
    \A t \in {1}:
        <>(pc[t] = "CS")
=============================================================================
\* Modification History
\* Last modified Sun Nov 03 11:29:34 GMT 2024 by frankeg
\* Created Fri Nov 01 22:12:48 GMT 2024 by frankeg

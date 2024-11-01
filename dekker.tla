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
EXTENDS TLC, Integers
CONSTANT Threads
(*--algorithm dekker
variables flag = [t \in Threads |-> FALSE];
fair process thread \in Threads
begin
    P1: flag[self] := TRUE;
    \* all threads except self are false
    P2: await \A t \in Threads \ {self}: ~flag[t];
    CS: skip;
    P3: flag[self] := FALSE;
    P4: goto P1;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d8900cdc" /\ chksum(tla) = "f884ff52")
VARIABLES flag, pc

vars == << flag, pc >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ flag = [t \in Threads |-> FALSE]
        /\ pc = [self \in ProcSet |-> "P1"]

P1(self) == /\ pc[self] = "P1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]

P2(self) == /\ pc[self] = "P2"
            /\ \A t \in Threads \ {self}: ~flag[t]
            /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ flag' = flag

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ flag' = flag

P3(self) == /\ pc[self] = "P3"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P4"]

P4(self) == /\ pc[self] = "P4"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ flag' = flag

thread(self) == P1(self) \/ P2(self) \/ CS(self) \/ P3(self) \/ P4(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
AtMostOneCritical ==
    \/ \A t \in Threads: pc[t] /= "CS"
    \/ \E t \in Threads:
        /\ pc[t] = "CS"
        /\ \A t2 \in Threads \ {t}: pc[t2] /= "CS"
=============================================================================
\* Modification History
\* Last modified Fri Nov 01 22:39:00 GMT 2024 by frankeg
\* Created Fri Nov 01 22:12:48 GMT 2024 by frankeg

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

=============================================================================
\* Modification History
\* Last modified Fri Nov 01 22:16:06 GMT 2024 by frankeg
\* Created Fri Nov 01 22:12:48 GMT 2024 by frankeg

------------------------ MODULE counter_incrementer ------------------------
(*
 Multiprocess algorithms are similar to single-process algorithms,
 except that we want to check our assertion when all of the processes terminate.
 Instead of hard-coding an assertion in, we should encode it as a liveness requirement.
*)

=============================================================================
\* Modification History
\* Last modified Sun Nov 03 22:17:40 GMT 2024 by frankeg
\* Created Sun Nov 03 22:16:03 GMT 2024 by frankeg

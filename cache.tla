------------------------------- MODULE cache -------------------------------
\* Several clients consume some shared resource that periodically renews.
EXTENDS Integers
CONSTANT ResourceCap, MaxConsumerReq
ASSUME ResourceCap > 0
ASSUME MaxConsumerReq \in 1..ResourceCap
(*--algorithm cache
variables resources_left = ResourceCap;
process actor = "actor"
variables
    resources_needed \in 1..MaxConsumerReq
begin
    UseResources:
        while TRUE do
            resources_left := resources_left - resources_needed;
        end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "24ddfd76" /\ chksum(tla) = "65b0065d")
VARIABLES resources_left, resources_needed

vars == << resources_left, resources_needed >>

ProcSet == {"actor"}

Init == (* Global variables *)
        /\ resources_left = ResourceCap
        (* Process actor *)
        /\ resources_needed \in 1..MaxConsumerReq

actor == /\ resources_left' = resources_left - resources_needed
         /\ UNCHANGED resources_needed

Next == actor

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Nov 01 16:21:33 GMT 2024 by frankeg
\* Created Fri Nov 01 16:11:59 GMT 2024 by frankeg

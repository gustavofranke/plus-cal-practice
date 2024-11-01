------------------------------ MODULE traffic ------------------------------
(*
 Imagine we have a car at a traffic light.
 We have two processes in the system.
 The traffic light alternates between red and green. 
 The car waits until the light is green before moving.
*)
NextColor(c) == CASE c = "red" -> "green"
                  [] c = "green" -> "red"
(*--algorithm traffic
variables
    at_light = TRUE,
    light = "red";
fair process light = "light"
begin
    Cycle:
        while at_light do
            light := NextColor(light);
        end while;
end process;
fair+ process car = "car"
begin
    Drive:
        when light = "green";
        at_light := FALSE;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "10e15a9a" /\ chksum(tla) = "f8d75175")
\* Process light at line 14 col 6 changed to light_
VARIABLES at_light, light, pc

vars == << at_light, light, pc >>

ProcSet == {"light"} \cup {"car"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ light = "red"
        /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
                                        [] self = "car" -> "Drive"]

Cycle == /\ pc["light"] = "Cycle"
         /\ IF at_light
               THEN /\ light' = NextColor(light)
                    /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
               ELSE /\ pc' = [pc EXCEPT !["light"] = "Done"]
                    /\ light' = light
         /\ UNCHANGED at_light

light_ == Cycle

Drive == /\ pc["car"] = "Drive"
         /\ light = "green"
         /\ at_light' = FALSE
         /\ pc' = [pc EXCEPT !["car"] = "Done"]
         /\ light' = light

car == Drive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == light_ \/ car
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(light_)
        /\ SF_vars(car)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Nov 01 22:01:40 GMT 2024 by frankeg
\* Created Fri Nov 01 21:48:16 GMT 2024 by frankeg

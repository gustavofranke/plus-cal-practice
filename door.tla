-------------------------------- MODULE door --------------------------------
(*--algorithm door
variables
    open = FALSE;
    locked = FALSE;
    key \in BOOLEAN;
begin
    Event:
        either \* unlock
            await locked /\ (open \/ key);
            locked := FALSE;
        or \* lock
            await ~locked /\ (open \/ key);
            locked := TRUE;
        or \* open
            await ~locked;
            await ~open;
            open := TRUE;
        or \* close
            await open;
            open := FALSE;
        end either;
    goto Event;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "580244f3" /\ chksum(tla) = "48ed8048")
VARIABLES open, locked, key, pc

vars == << open, locked, key, pc >>

Init == (* Global variables *)
        /\ open = FALSE
        /\ locked = FALSE
        /\ key \in BOOLEAN
        /\ pc = "Event"

Event == /\ pc = "Event"
         /\ \/ /\ locked /\ (open \/ key)
               /\ locked' = FALSE
               /\ open' = open
            \/ /\ ~locked /\ (open \/ key)
               /\ locked' = TRUE
               /\ open' = open
            \/ /\ ~locked
               /\ ~open
               /\ open' = TRUE
               /\ UNCHANGED locked
            \/ /\ open
               /\ open' = FALSE
               /\ UNCHANGED locked
         /\ pc' = "Event"
         /\ key' = key

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Event
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Nov 08 16:59:33 GMT 2024 by frankeg
\* Created Fri Nov 08 15:06:24 GMT 2024 by frankeg

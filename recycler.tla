------------------------------ MODULE recycler ------------------------------
(***********************************************************************************)
(* Imagine we have a machine that sorts material into "recyclable" and "trash."    *)
(* It has finite space for both recycling and trash.                               *)
(* Items with a specified size and type come in, one at a time,                    *)
(* and it sorts them according to the following rules:                             *)
(* 1. If the item is labeled as "recycling"                                        *)
(*    and it is under the remaining capacity for the recycling bin,                *)
(*    the item goes into recycling.                                                *)
(* 2. If the item is labeled as "trash" OR the item is labeled as "recycling"      *)
(*    and there is not enough recycling capacity                                   *)
(*    AND there is sufficient capacity in the trash bin, the item goes into trash. *)
(* 3. Otherwise, it’s dropped on the floor and somebody else gets to sweep it up.  *)
(***********************************************************************************)
EXTENDS Sequences, Integers, TLC, FiniteSets
(*--algorithm recycler
variables
    capacity = [trash |-> 10, recycle |-> 10],
    bins = [trash |-> {}, recycle |-> {}],
    count = [trash |-> 0, recycle |-> 0],
    items = <<
        [type |-> "recycle", size |-> 5],
        [type |-> "trash", size |-> 5],
        [type |-> "recycle", size |-> 4],
        [type |-> "recycle", size |-> 3]
    >>,
    curr = ""; \* helper: current item
begin
    while items /= <<>> do
        curr := Head(items);
        items := Tail(items);
        if curr.type = "recycle" /\ curr.size < capacity.recycle then
            bins.recycle := bins.recycle \union {curr};
            capacity.recycle := capacity.recycle - curr.size;
            count.recycle := count.recycle + 1;
        elsif curr.size < capacity.trash then
            bins.trash := bins.trash \union {curr};
            capacity.trash := capacity.trash - curr.size;
            count.trash := count.trash + 1;
        end if;    
    end while;       
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d54701ce" /\ chksum(tla) = "4ee2ed74")
VARIABLES capacity, bins, count, items, curr, pc

vars == << capacity, bins, count, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity = [trash |-> 10, recycle |-> 10]
        /\ bins = [trash |-> {}, recycle |-> {}]
        /\ count = [trash |-> 0, recycle |-> 0]
        /\ items =         <<
                       [type |-> "recycle", size |-> 5],
                       [type |-> "trash", size |-> 5],
                       [type |-> "recycle", size |-> 4],
                       [type |-> "recycle", size |-> 3]
                   >>
        /\ curr = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycle" /\ curr'.size < capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !.recycle = bins.recycle \union {curr'}]
                               /\ capacity' = [capacity EXCEPT !.recycle = capacity.recycle - curr'.size]
                               /\ count' = [count EXCEPT !.recycle = count.recycle + 1]
                          ELSE /\ IF curr'.size < capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !.trash = bins.trash \union {curr'}]
                                          /\ capacity' = [capacity EXCEPT !.trash = capacity.trash - curr'.size]
                                          /\ count' = [count EXCEPT !.trash = count.trash + 1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu Oct 31 11:43:50 GMT 2024 by frankeg
\* Created Thu Oct 31 11:12:44 GMT 2024 by frankeg

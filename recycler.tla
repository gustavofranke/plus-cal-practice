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
    capacity \in [trash: 1..10, recycle: 1..10],
    bins = [trash |-> <<>>, recycle |-> <<>>],
    count = [trash |-> 0, recycle |-> 0],
    item = [type: {"trash", "recycle"}, size: 1..6],
    items \in item \X item \X item \X item,
    curr = ""; \* helper: current item
macro add_item(type) begin
    bins[type] := Append(bins[type], curr);
    capacity[type] := capacity[type] - curr.size;
    count[type] := count[type] + 1;
end macro;
begin
    while items /= <<>> do
        curr := Head(items);
        items := Tail(items);
        if curr.type = "recycle" /\ curr.size < capacity.recycle then
            add_item("recycle");
        elsif curr.size < capacity.trash then
            add_item("trash");
        end if;    
    end while;  
    assert capacity.trash >= 0 /\ capacity.recycle >= 0;
    assert Len(bins.trash) = count.trash;
    assert Len(bins.recycle) = count.recycle;      
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1efeb7af" /\ chksum(tla) = "f635fb90")
VARIABLES capacity, bins, count, item, items, curr, pc

vars == << capacity, bins, count, item, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity \in [trash: 1..10, recycle: 1..10]
        /\ bins = [trash |-> <<>>, recycle |-> <<>>]
        /\ count = [trash |-> 0, recycle |-> 0]
        /\ item = [type: {"trash", "recycle"}, size: 1..6]
        /\ items \in item \X item \X item \X item
        /\ curr = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycle" /\ curr'.size < capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = Append(bins["recycle"], curr')]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - curr'.size]
                               /\ count' = [count EXCEPT !["recycle"] = count["recycle"] + 1]
                          ELSE /\ IF curr'.size < capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = Append(bins["trash"], curr')]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(capacity.trash >= 0 /\ capacity.recycle >= 0, 
                              "Failure of assertion at line 39, column 5.")
                    /\ Assert(Len(bins.trash) = count.trash, 
                              "Failure of assertion at line 40, column 5.")
                    /\ Assert(Len(bins.recycle) = count.recycle, 
                              "Failure of assertion at line 41, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>
         /\ item' = item

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu Oct 31 12:07:53 GMT 2024 by frankeg
\* Created Thu Oct 31 11:12:44 GMT 2024 by frankeg

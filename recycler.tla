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
EXTENDS Integers
(*--algorithm recycler
variables
begin
skip;    
end algorithm; *)
=============================================================================
\* Modification History
\* Last modified Thu Oct 31 11:42:28 GMT 2024 by frankeg
\* Created Thu Oct 31 11:12:44 GMT 2024 by frankeg

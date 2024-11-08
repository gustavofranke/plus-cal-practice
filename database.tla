------------------------------ MODULE database ------------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS Data, NULL, Clients
(*--algorithm database
variables
    query = [c \in Clients |-> NULL];
    db_value \in Data;
define Exists(val) == val /= NULL
    RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}
end define;
macro request(data) begin
    query[self] := [type |-> "request", data |-> data]
end macro;
macro wait_for_response() begin
    await query[self].type = "response";
end macro;
process database = "Database"
begin
    DB:
        with client \in RequestingClients, q = query[client] do
            db_value := q.data;
            query[client] := [type |-> "response"];
        end with;
    goto DB;
end process;
process clients \in Clients
variables result = NULL;
begin
    Request:
        while TRUE do
            either \* read
                result := db_value;
                assert result = db_value;
            or \* write
                with d \in Data do
                    request(d);
                end with;
                Wait:
                    wait_for_response();
            end either;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e25d3a79" /\ chksum(tla) = "22adce56")
VARIABLES query, db_value, pc

(* define statement *)
   Exists(val) == val /= NULL
RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}

VARIABLE result

vars == << query, db_value, pc, result >>

ProcSet == {"Database"} \cup (Clients)

Init == (* Global variables *)
        /\ query = [c \in Clients |-> NULL]
        /\ db_value \in Data
        (* Process clients *)
        /\ result = [self \in Clients |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self = "Database" -> "DB"
                                        [] self \in Clients -> "Request"]

DB == /\ pc["Database"] = "DB"
      /\ \E client \in RequestingClients:
           LET q == query[client] IN
             /\ db_value' = q.data
             /\ query' = [query EXCEPT ![client] = [type |-> "response"]]
      /\ pc' = [pc EXCEPT !["Database"] = "DB"]
      /\ UNCHANGED result

database == DB

Request(self) == /\ pc[self] = "Request"
                 /\ \/ /\ result' = [result EXCEPT ![self] = db_value]
                       /\ Assert(result'[self] = db_value, 
                                 "Failure of assertion at line 33, column 17.")
                       /\ pc' = [pc EXCEPT ![self] = "Request"]
                       /\ query' = query
                    \/ /\ \E d \in Data:
                            query' = [query EXCEPT ![self] = [type |-> "request", data |-> d]]
                       /\ pc' = [pc EXCEPT ![self] = "Wait"]
                       /\ UNCHANGED result
                 /\ UNCHANGED db_value

Wait(self) == /\ pc[self] = "Wait"
              /\ query[self].type = "response"
              /\ pc' = [pc EXCEPT ![self] = "Request"]
              /\ UNCHANGED << query, db_value, result >>

clients(self) == Request(self) \/ Wait(self)

Next == database
           \/ (\E self \in Clients: clients(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Nov 08 21:03:24 GMT 2024 by frankeg
\* Created Fri Nov 08 20:35:30 GMT 2024 by frankeg

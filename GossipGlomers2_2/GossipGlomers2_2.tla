---- MODULE GossipGlomers2_2 ----
EXTENDS TLC, Naturals, Sequences

Servers == {1, 2, 3}
Clients == {4}
IDSpace == 0..10

(* --algorithm GossipGlomers2_2

variables
    server_msg_queue = [ server \in Servers |-> <<>> ];
    client_msg_queue = [ client \in Clients |-> <<>> ];
    server_saw = [ server \in Servers |-> {} ];
    ids_seen_by_clients = {};
    ids_unique = TRUE;

define
    Safe == ids_unique = TRUE
    GenerateIDMessage(sender) == [sender_id |-> sender, type |-> "GenerateIDRequest"]
    GenerateIDMessageResponse(sender, id) == [sender_id |-> sender, type |-> "GenerateIDResponse", new_id |-> id]
end define;
process client \in Clients
begin
    ClientAct:
        either
            with server \in Servers do
                server_msg_queue[server] := Append(server_msg_queue[server], GenerateIDMessage(self));
            end with;
        or
            await Len(client_msg_queue[self]) > 0;
            with msg = Head(client_msg_queue[self]) do
                client_msg_queue[self] := Tail(client_msg_queue[self]);
                if msg.new_id \in ids_seen_by_clients then
                    ids_unique := FALSE;
                end if;
                ids_seen_by_clients := ids_seen_by_clients \union {msg.new_id};
            end with;
        end either;
        goto ClientAct;
end process;

process server \in Servers
begin
    ServerAct:
        await Len(server_msg_queue[self]) > 0;
        with msg = Head(server_msg_queue[self]) do
            server_msg_queue[self] := Tail(server_msg_queue[self]);
            with id \in IDSpace \ server_saw[self] do
                server_saw[self] := server_saw[self] \union {id};
                client_msg_queue[msg.sender_id] := Append(client_msg_queue[msg.sender_id], GenerateIDMessageResponse(self, id));
            end with;
        end with;
        goto ServerAct;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "bd466dec" /\ chksum(tla) = "4eb7950d")
VARIABLES server_msg_queue, client_msg_queue, server_saw, ids_seen_by_clients, 
          ids_unique, pc

(* define statement *)
Safe == ids_unique = TRUE
GenerateIDMessage(sender) == [sender_id |-> sender, type |-> "GenerateIDRequest"]
GenerateIDMessageResponse(sender, id) == [sender_id |-> sender, type |-> "GenerateIDResponse", new_id |-> id]


vars == << server_msg_queue, client_msg_queue, server_saw, 
           ids_seen_by_clients, ids_unique, pc >>

ProcSet == (Clients) \cup (Servers)

Init == (* Global variables *)
        /\ server_msg_queue = [ server \in Servers |-> <<>> ]
        /\ client_msg_queue = [ client \in Clients |-> <<>> ]
        /\ server_saw = [ server \in Servers |-> {} ]
        /\ ids_seen_by_clients = {}
        /\ ids_unique = TRUE
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "ClientAct"
                                        [] self \in Servers -> "ServerAct"]

ClientAct(self) == /\ pc[self] = "ClientAct"
                   /\ \/ /\ \E server \in Servers:
                              server_msg_queue' = [server_msg_queue EXCEPT ![server] = Append(server_msg_queue[server], GenerateIDMessage(self))]
                         /\ UNCHANGED <<client_msg_queue, ids_seen_by_clients, ids_unique>>
                      \/ /\ Len(client_msg_queue[self]) > 0
                         /\ LET msg == Head(client_msg_queue[self]) IN
                              /\ client_msg_queue' = [client_msg_queue EXCEPT ![self] = Tail(client_msg_queue[self])]
                              /\ IF msg.new_id \in ids_seen_by_clients
                                    THEN /\ ids_unique' = FALSE
                                    ELSE /\ TRUE
                                         /\ UNCHANGED ids_unique
                              /\ ids_seen_by_clients' = (ids_seen_by_clients \union {msg.new_id})
                         /\ UNCHANGED server_msg_queue
                   /\ pc' = [pc EXCEPT ![self] = "ClientAct"]
                   /\ UNCHANGED server_saw

client(self) == ClientAct(self)

ServerAct(self) == /\ pc[self] = "ServerAct"
                   /\ Len(server_msg_queue[self]) > 0
                   /\ LET msg == Head(server_msg_queue[self]) IN
                        /\ server_msg_queue' = [server_msg_queue EXCEPT ![self] = Tail(server_msg_queue[self])]
                        /\ \E id \in IDSpace \ server_saw[self]:
                             /\ server_saw' = [server_saw EXCEPT ![self] = server_saw[self] \union {id}]
                             /\ client_msg_queue' = [client_msg_queue EXCEPT ![msg.sender_id] = Append(client_msg_queue[msg.sender_id], GenerateIDMessageResponse(self, id))]
                   /\ pc' = [pc EXCEPT ![self] = "ServerAct"]
                   /\ UNCHANGED << ids_seen_by_clients, ids_unique >>

server(self) == ServerAct(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Clients: client(self))
           \/ (\E self \in Servers: server(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====

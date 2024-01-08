---- MODULE GossipGlomers3a ----
EXTENDS TLC, Naturals, Sequences
CONSTANT MAX_MSGS, Servers, Clients
DataSpace == 1..100

(* --algorithm GossipGlomers3a
 
variables
    server_msg_queue = [ server \in Servers |-> <<>> ];
    client_msg_queue = [ client \in Clients |-> <<>> ];
    server_saw = [ server \in Servers |-> <<>> ];
    server_topologies = [ server \in Servers |-> Servers \ {server}];
    all_sent_values = <<>>;
    broadcasts_processed = 0;
define
    AllServersSawSameValues == []<>(\A s \in Servers : server_saw[s] = all_sent_values)
    BroadcastMessage(s,k) == [type |-> "broadcast", message |-> k, sender |-> s]
    BroadcastMessageResponse == [type |-> "broadcast_ok"]
    ReadMessage(s) == [type |-> "read", sender |-> s]
    ReadMessageResponse(msgs) == [type |-> "read_ok", messages |-> msgs]
end define;
process client \in Clients
begin
    ClientAct: while (broadcasts_processed < MAX_MSGS) do
            with server \in Servers ; k \in DataSpace do
                server_msg_queue[server] := Append(server_msg_queue[server], BroadcastMessage(self, k));
                all_sent_values := Append(all_sent_values, k);
            end with;
            ClientProcessBroadcastResponse:
            await Len(client_msg_queue[self]) > 0;
            with msg = Head(client_msg_queue[self]) do
                client_msg_queue[self] := Tail(client_msg_queue[self]);
            end with;
    end while;
    ClientRead:
        with server \in Servers do
            server_msg_queue[server] := Append(server_msg_queue[server], ReadMessage(self));
        end with;
end process;

process server \in Servers
begin
    ServerAct: while (broadcasts_processed < MAX_MSGS) do
        await Len(server_msg_queue[self]) > 0;
        if Head(server_msg_queue[self]).type = "broadcast" then
            broadcasts_processed := broadcasts_processed + 1;
            server_saw[self] := Append(server_saw[self], Head(server_msg_queue[self]).message);
            client_msg_queue[ Head(server_msg_queue[self]).sender] := Append(client_msg_queue[Head(server_msg_queue[self]).sender], BroadcastMessageResponse);
        else
            with msg = Head(server_msg_queue[self]) do
                if msg.type = "read" then
                    client_msg_queue[msg.sender] := Append(client_msg_queue[msg.sender], ReadMessageResponse(server_saw[self]));
                end if;
            end with;
        end if;
        server_msg_queue[self] := Tail(server_msg_queue[self]);
    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "4dee7e2e" /\ chksum(tla) = "2fcbd9d0")
VARIABLES server_msg_queue, client_msg_queue, server_saw, server_topologies, 
          all_sent_values, broadcasts_processed, pc

(* define statement *)
AllServersSawSameValues == []<>(\A s \in Servers : server_saw[s] = all_sent_values)
BroadcastMessage(s,k) == [type |-> "broadcast", message |-> k, sender |-> s]
BroadcastMessageResponse == [type |-> "broadcast_ok"]
ReadMessage(s) == [type |-> "read", sender |-> s]
ReadMessageResponse(msgs) == [type |-> "read_ok", messages |-> msgs]


vars == << server_msg_queue, client_msg_queue, server_saw, server_topologies, 
           all_sent_values, broadcasts_processed, pc >>

ProcSet == (Clients) \cup (Servers)

Init == (* Global variables *)
        /\ server_msg_queue = [ server \in Servers |-> <<>> ]
        /\ client_msg_queue = [ client \in Clients |-> <<>> ]
        /\ server_saw = [ server \in Servers |-> <<>> ]
        /\ server_topologies = [ server \in Servers |-> Servers \ {server}]
        /\ all_sent_values = <<>>
        /\ broadcasts_processed = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "ClientAct"
                                        [] self \in Servers -> "ServerAct"]

ClientAct(self) == /\ pc[self] = "ClientAct"
                   /\ IF (broadcasts_processed < MAX_MSGS)
                         THEN /\ \E server \in Servers:
                                   \E k \in DataSpace:
                                     /\ server_msg_queue' = [server_msg_queue EXCEPT ![server] = Append(server_msg_queue[server], BroadcastMessage(self, k))]
                                     /\ all_sent_values' = Append(all_sent_values, k)
                              /\ pc' = [pc EXCEPT ![self] = "ClientProcessBroadcastResponse"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "ClientRead"]
                              /\ UNCHANGED << server_msg_queue, 
                                              all_sent_values >>
                   /\ UNCHANGED << client_msg_queue, server_saw, 
                                   server_topologies, broadcasts_processed >>

ClientProcessBroadcastResponse(self) == /\ pc[self] = "ClientProcessBroadcastResponse"
                                        /\ Len(client_msg_queue[self]) > 0
                                        /\ LET msg == Head(client_msg_queue[self]) IN
                                             client_msg_queue' = [client_msg_queue EXCEPT ![self] = Tail(client_msg_queue[self])]
                                        /\ pc' = [pc EXCEPT ![self] = "ClientAct"]
                                        /\ UNCHANGED << server_msg_queue, 
                                                        server_saw, 
                                                        server_topologies, 
                                                        all_sent_values, 
                                                        broadcasts_processed >>

ClientRead(self) == /\ pc[self] = "ClientRead"
                    /\ \E server \in Servers:
                         server_msg_queue' = [server_msg_queue EXCEPT ![server] = Append(server_msg_queue[server], ReadMessage(self))]
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << client_msg_queue, server_saw, 
                                    server_topologies, all_sent_values, 
                                    broadcasts_processed >>

client(self) == ClientAct(self) \/ ClientProcessBroadcastResponse(self)
                   \/ ClientRead(self)

ServerAct(self) == /\ pc[self] = "ServerAct"
                   /\ IF (broadcasts_processed < MAX_MSGS)
                         THEN /\ Len(server_msg_queue[self]) > 0
                              /\ IF Head(server_msg_queue[self]).type = "broadcast"
                                    THEN /\ broadcasts_processed' = broadcasts_processed + 1
                                         /\ server_saw' = [server_saw EXCEPT ![self] = Append(server_saw[self], Head(server_msg_queue[self]).message)]
                                         /\ client_msg_queue' = [client_msg_queue EXCEPT ![ Head(server_msg_queue[self]).sender] = Append(client_msg_queue[Head(server_msg_queue[self]).sender], BroadcastMessageResponse)]
                                    ELSE /\ LET msg == Head(server_msg_queue[self]) IN
                                              IF msg.type = "read"
                                                 THEN /\ client_msg_queue' = [client_msg_queue EXCEPT ![msg.sender] = Append(client_msg_queue[msg.sender], ReadMessageResponse(server_saw[self]))]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED client_msg_queue
                                         /\ UNCHANGED << server_saw, 
                                                         broadcasts_processed >>
                              /\ server_msg_queue' = [server_msg_queue EXCEPT ![self] = Tail(server_msg_queue[self])]
                              /\ pc' = [pc EXCEPT ![self] = "ServerAct"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                              /\ UNCHANGED << server_msg_queue, 
                                              client_msg_queue, server_saw, 
                                              broadcasts_processed >>
                   /\ UNCHANGED << server_topologies, all_sent_values >>

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

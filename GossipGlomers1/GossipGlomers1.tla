---- MODULE GossipGlomers1 ----
EXTENDS TLC, Naturals, Sequences
CONSTANT MAX_MSGS, MAX_VAL, Servers, Clients
DataSpace == 0..MAX_VAL
IdSpace == 0..MAX_MSGS
(* --algorithm GossipGlomers1
variables
    server_msg_queue = [ server \in Servers |-> <<>> ];
    client_msg_queue = [ client \in Clients |-> <<>> ];
    v = [n \in IdSpace |-> 0];
    client_sent = [client \in Clients |-> v];
    next_echo_message_id = 0;
    echos_processed = 0;

define
    EchoMessage(s, e, id) == [type |-> "echo", echo |-> e, sender |-> s, msg_id |-> id]
    EchoMessageResponse(e, id) == [type |-> "echo_ok", echo |-> e, in_reply_to |-> id]
end define;

process client \in Clients
begin
    ClientAct: while (echos_processed < MAX_MSGS) do
            with server \in Servers; k \in DataSpace do
                client_sent[self] := [client_sent[self] EXCEPT ![next_echo_message_id] = k];
                server_msg_queue[server] := Append(server_msg_queue[server], EchoMessage(self, k, next_echo_message_id));
                next_echo_message_id := next_echo_message_id + 1
            end with;
            A:
            await Len(client_msg_queue[self]) > 0;
            assert Head(client_msg_queue[self]).echo = client_sent[self][Head(client_msg_queue[self]).in_reply_to];
            client_msg_queue[self] := Tail(client_msg_queue[self]);
    end while;
end process;

process server \in Servers
begin
    ServerAct: while (echos_processed < MAX_MSGS) do
        await Len(server_msg_queue[self]) > 0;
        if Head(server_msg_queue[self]).type = "echo" then
            echos_processed := echos_processed + 1;
            client_msg_queue[Head(server_msg_queue[self]).sender] := Append(client_msg_queue[Head(server_msg_queue[self]).sender], EchoMessageResponse(Head(server_msg_queue[self]).echo, Head(server_msg_queue[self]).msg_id));
            server_msg_queue[self] := Tail(server_msg_queue[self]);
        end if;
    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "4dc7a168" /\ chksum(tla) = "aaa58da9")
VARIABLES server_msg_queue, client_msg_queue, v, client_sent, 
          next_echo_message_id, echos_processed, pc

(* define statement *)
EchoMessage(s, e, id) == [type |-> "echo", echo |-> e, sender |-> s, msg_id |-> id]
EchoMessageResponse(e, id) == [type |-> "echo_ok", echo |-> e, in_reply_to |-> id]


vars == << server_msg_queue, client_msg_queue, v, client_sent, 
           next_echo_message_id, echos_processed, pc >>

ProcSet == (Clients) \cup (Servers)

Init == (* Global variables *)
        /\ server_msg_queue = [ server \in Servers |-> <<>> ]
        /\ client_msg_queue = [ client \in Clients |-> <<>> ]
        /\ v = [n \in IdSpace |-> 0]
        /\ client_sent = [client \in Clients |-> v]
        /\ next_echo_message_id = 0
        /\ echos_processed = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "ClientAct"
                                        [] self \in Servers -> "ServerAct"]

ClientAct(self) == /\ pc[self] = "ClientAct"
                   /\ IF (echos_processed < MAX_MSGS)
                         THEN /\ \E server \in Servers:
                                   \E k \in DataSpace:
                                     /\ client_sent' = [client_sent EXCEPT ![self] = [client_sent[self] EXCEPT ![next_echo_message_id] = k]]
                                     /\ server_msg_queue' = [server_msg_queue EXCEPT ![server] = Append(server_msg_queue[server], EchoMessage(self, k, next_echo_message_id))]
                                     /\ next_echo_message_id' = next_echo_message_id + 1
                              /\ pc' = [pc EXCEPT ![self] = "A"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                              /\ UNCHANGED << server_msg_queue, client_sent, 
                                              next_echo_message_id >>
                   /\ UNCHANGED << client_msg_queue, v, echos_processed >>

A(self) == /\ pc[self] = "A"
           /\ Len(client_msg_queue[self]) > 0
           /\ Assert(Head(client_msg_queue[self]).echo = client_sent[self][Head(client_msg_queue[self]).in_reply_to], 
                     "Failure of assertion at line 32, column 13.")
           /\ client_msg_queue' = [client_msg_queue EXCEPT ![self] = Tail(client_msg_queue[self])]
           /\ pc' = [pc EXCEPT ![self] = "ClientAct"]
           /\ UNCHANGED << server_msg_queue, v, client_sent, 
                           next_echo_message_id, echos_processed >>

client(self) == ClientAct(self) \/ A(self)

ServerAct(self) == /\ pc[self] = "ServerAct"
                   /\ IF (echos_processed < MAX_MSGS)
                         THEN /\ Len(server_msg_queue[self]) > 0
                              /\ IF Head(server_msg_queue[self]).type = "echo"
                                    THEN /\ echos_processed' = echos_processed + 1
                                         /\ client_msg_queue' = [client_msg_queue EXCEPT ![Head(server_msg_queue[self]).sender] = Append(client_msg_queue[Head(server_msg_queue[self]).sender], EchoMessageResponse(Head(server_msg_queue[self]).echo, Head(server_msg_queue[self]).msg_id))]
                                         /\ server_msg_queue' = [server_msg_queue EXCEPT ![self] = Tail(server_msg_queue[self])]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << server_msg_queue, 
                                                         client_msg_queue, 
                                                         echos_processed >>
                              /\ pc' = [pc EXCEPT ![self] = "ServerAct"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                              /\ UNCHANGED << server_msg_queue, 
                                              client_msg_queue, 
                                              echos_processed >>
                   /\ UNCHANGED << v, client_sent, next_echo_message_id >>

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

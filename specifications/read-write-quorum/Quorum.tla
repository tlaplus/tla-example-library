------------------------------- MODULE Quorum -------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS numClients, numReplicas, ReadQuorum, WriteQuorum, MaxClock

\* TODO: Verify all uses of Pid
Pid == 1 .. numClients+numReplicas
ClientPids == 1 .. numClients
ReplicaPids == numClients+1 .. numClients+numReplicas

ReadQuorums == { x \in SUBSET ReplicaPids : Cardinality(x) = ReadQuorum }
WriteQuorums == { x \in SUBSET ReplicaPids : Cardinality(x) = WriteQuorum }

ClockVal == 0 .. MaxClock+1
Message == [time: ClockVal, type: {"Read", "Write", "Ack"}, stamp: ClockVal, value: 1..20]

(*--algorithm Quorum

variables channel = [source \in Pid |-> [destination \in Pid |-> <<>>]]

define
  GetMsgSrcs(dst, type) ==
    { src \in Pid: /\ Len(channel[src][dst]) > 0
                   /\ Head(channel[src][dst]).type = type
    }
   
  Max(a, b) == IF a <= b THEN b ELSE a
end define

macro Receive(type, clock, src, time, stamp, value) begin
  with s \in GetMsgSrcs(self, type) do
    src := s;
    time := Head(channel[src][self]).time;
    stamp := Head(channel[src][self]).stamp;
    value := Head(channel[src][self]).value;
    channel := [channel EXCEPT ![src][self] = Tail(channel[src][self])]
  end with
end macro

macro BroadcastTo(dsts, clock, msg) begin
  channel :=
    [channel EXCEPT ![self] =
      [dst \in Pid |->
        IF dst = self THEN channel[self][self]
                      ELSE Append(channel[self][dst], msg)]]
end macro

macro SendTo(clock, dst, msg) begin
  channel :=
    [channel EXCEPT ![self][dst] = Append(channel[self][dst], msg)]
end macro

process Proc \in Pid
variables
  clock = 1,
  acks = <<>>,
  requests = [pid \in Pid |-> 0],
  src,
  time,
  stamper,
  value,

  TS = 1,
  state = 0,

  type = 0

begin
    loop: while TRUE do
        if self \in ClientPids then
\*            Client actions
            either
\*            Send "Read" or "Write"
                when requests[self] = 0;
                    either
\*                    Send "Read"
                        with quorum \in ReadQuorums do
\*                            print <<quorum>>;
                            BroadcastTo(quorum, clock, [time |-> clock, type |-> "Read", stamp |-> clock, value |-> 0]);
                            requests := [requests EXCEPT ![self] = clock];
                            type := 1;
                        end with
                    or
\*                    Send "Write
                        with quorum \in WriteQuorums do
                            with val \in 1..20 do
                                BroadcastTo(quorum, clock, [time |-> clock, type |-> "Write", stamp |-> clock, value |-> val]);
                                requests := [requests EXCEPT ![self] = clock];
                                type := 2;
                            end with
                        end with
                    end either;
            or
\*            Receive "Ack"
                Receive("Ack", clock, src, time, stamper, value);
                acks := Append(acks, [source |-> src, stamp |-> stamper, val |-> value]);
                clock := Max(clock, time);
            or
\*            Do work: "Read"
                when (type = 1 /\ Len(acks) = ReadQuorum);
                    acks := <<>>;
                    requests := [requests EXCEPT ![self] = 0];
                    type := 0;
            or
\*            Do work: "Write"
                when (type = 2 /\ Len(acks) = WriteQuorum);
                    acks := <<>>;
                    requests := [requests EXCEPT ![self] = 0];
                    type := 0; 
            end either;
        else
\*            Replica actions
            either
\*            Receive "Read"
                Receive("Read", clock, src, time, stamper, value);
                clock := Max(clock, time);
                L2: SendTo(clock, src, [time |-> clock+1, type |-> "Ack", stamp |-> TS, value |-> state])
            or
\*            Receive "Write
                Receive("Write", clock, src, time, stamper, value);
                if (stamper > TS) \/ (stamper = TS /\ src > self) then
                    TS := stamper;
                    state := value;
                    clock := Max(clock, time);
                    L3: SendTo(clock, src, [time |-> clock+1, type |-> "Ack", stamp |-> TS, value |-> state])
                else
                    clock := Max(clock, time);
                    L4: SendTo(clock, src, [time |-> clock+1, type |-> "Ack", stamp |-> TS, value |-> 0])
                end if;
            end either;
        end if;
        tic: clock := clock + 1
    end while;
end process

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "85c970db" /\ chksum(tla) = "b3dc63aa")
CONSTANT defaultInitValue
VARIABLES channel, pc

(* define statement *)
GetMsgSrcs(dst, type) ==
  { src \in Pid: /\ Len(channel[src][dst]) > 0
                 /\ Head(channel[src][dst]).type = type
  }

Max(a, b) == IF a <= b THEN b ELSE a

VARIABLES clock, acks, requests, src, time, stamper, value, TS, state, type

vars == << channel, pc, clock, acks, requests, src, time, stamper, value, TS, 
           state, type >>

ProcSet == (Pid)

Init == (* Global variables *)
        /\ channel = [source \in Pid |-> [destination \in Pid |-> <<>>]]
        (* Process Proc *)
        /\ clock = [self \in Pid |-> 1]
        /\ acks = [self \in Pid |-> <<>>]
        /\ requests = [self \in Pid |-> [pid \in Pid |-> 0]]
        /\ src = [self \in Pid |-> defaultInitValue]
        /\ time = [self \in Pid |-> defaultInitValue]
        /\ stamper = [self \in Pid |-> defaultInitValue]
        /\ value = [self \in Pid |-> defaultInitValue]
        /\ TS = [self \in Pid |-> 1]
        /\ state = [self \in Pid |-> 0]
        /\ type = [self \in Pid |-> 0]
        /\ pc = [self \in ProcSet |-> "loop"]

loop(self) == /\ pc[self] = "loop"
              /\ IF self \in ClientPids
                    THEN /\ \/ /\ requests[self][self] = 0
                               /\ \/ /\ \E quorum \in ReadQuorums:
                                          /\ channel' = [channel EXCEPT ![self] =
                                                          [dst \in Pid |->
                                                            IF dst = self THEN channel[self][self]
                                                                          ELSE Append(channel[self][dst], ([time |-> clock[self], type |-> "Read", stamp |-> clock[self], value |-> 0]))]]
                                          /\ requests' = [requests EXCEPT ![self] = [requests[self] EXCEPT ![self] = clock[self]]]
                                          /\ type' = [type EXCEPT ![self] = 1]
                                  \/ /\ \E quorum \in WriteQuorums:
                                          \E val \in 1..20:
                                            /\ channel' = [channel EXCEPT ![self] =
                                                            [dst \in Pid |->
                                                              IF dst = self THEN channel[self][self]
                                                                            ELSE Append(channel[self][dst], ([time |-> clock[self], type |-> "Write", stamp |-> clock[self], value |-> val]))]]
                                            /\ requests' = [requests EXCEPT ![self] = [requests[self] EXCEPT ![self] = clock[self]]]
                                            /\ type' = [type EXCEPT ![self] = 2]
                               /\ UNCHANGED <<clock, acks, src, time, stamper, value>>
                            \/ /\ \E s \in GetMsgSrcs(self, "Ack"):
                                    /\ src' = [src EXCEPT ![self] = s]
                                    /\ time' = [time EXCEPT ![self] = Head(channel[src'[self]][self]).time]
                                    /\ stamper' = [stamper EXCEPT ![self] = Head(channel[src'[self]][self]).stamp]
                                    /\ value' = [value EXCEPT ![self] = Head(channel[src'[self]][self]).value]
                                    /\ channel' = [channel EXCEPT ![src'[self]][self] = Tail(channel[src'[self]][self])]
                               /\ acks' = [acks EXCEPT ![self] = Append(acks[self], [source |-> src'[self], stamp |-> stamper'[self], val |-> value'[self]])]
                               /\ clock' = [clock EXCEPT ![self] = Max(clock[self], time'[self])]
                               /\ UNCHANGED <<requests, type>>
                            \/ /\ (type[self] = 1 /\ Len(acks[self]) = ReadQuorum)
                               /\ acks' = [acks EXCEPT ![self] = <<>>]
                               /\ requests' = [requests EXCEPT ![self] = [requests[self] EXCEPT ![self] = 0]]
                               /\ type' = [type EXCEPT ![self] = 0]
                               /\ UNCHANGED <<channel, clock, src, time, stamper, value>>
                            \/ /\ (type[self] = 2 /\ Len(acks[self]) = WriteQuorum)
                               /\ acks' = [acks EXCEPT ![self] = <<>>]
                               /\ requests' = [requests EXCEPT ![self] = [requests[self] EXCEPT ![self] = 0]]
                               /\ type' = [type EXCEPT ![self] = 0]
                               /\ UNCHANGED <<channel, clock, src, time, stamper, value>>
                         /\ pc' = [pc EXCEPT ![self] = "tic"]
                         /\ UNCHANGED << TS, state >>
                    ELSE /\ \/ /\ \E s \in GetMsgSrcs(self, "Read"):
                                    /\ src' = [src EXCEPT ![self] = s]
                                    /\ time' = [time EXCEPT ![self] = Head(channel[src'[self]][self]).time]
                                    /\ stamper' = [stamper EXCEPT ![self] = Head(channel[src'[self]][self]).stamp]
                                    /\ value' = [value EXCEPT ![self] = Head(channel[src'[self]][self]).value]
                                    /\ channel' = [channel EXCEPT ![src'[self]][self] = Tail(channel[src'[self]][self])]
                               /\ clock' = [clock EXCEPT ![self] = Max(clock[self], time'[self])]
                               /\ pc' = [pc EXCEPT ![self] = "L2"]
                               /\ UNCHANGED <<TS, state>>
                            \/ /\ \E s \in GetMsgSrcs(self, "Write"):
                                    /\ src' = [src EXCEPT ![self] = s]
                                    /\ time' = [time EXCEPT ![self] = Head(channel[src'[self]][self]).time]
                                    /\ stamper' = [stamper EXCEPT ![self] = Head(channel[src'[self]][self]).stamp]
                                    /\ value' = [value EXCEPT ![self] = Head(channel[src'[self]][self]).value]
                                    /\ channel' = [channel EXCEPT ![src'[self]][self] = Tail(channel[src'[self]][self])]
                               /\ IF (stamper'[self] > TS[self]) \/ (stamper'[self] = TS[self] /\ src'[self] > self)
                                     THEN /\ TS' = [TS EXCEPT ![self] = stamper'[self]]
                                          /\ state' = [state EXCEPT ![self] = value'[self]]
                                          /\ clock' = [clock EXCEPT ![self] = Max(clock[self], time'[self])]
                                          /\ pc' = [pc EXCEPT ![self] = "L3"]
                                     ELSE /\ clock' = [clock EXCEPT ![self] = Max(clock[self], time'[self])]
                                          /\ pc' = [pc EXCEPT ![self] = "L4"]
                                          /\ UNCHANGED << TS, state >>
                         /\ UNCHANGED << acks, requests, type >>

tic(self) == /\ pc[self] = "tic"
             /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "loop"]
             /\ UNCHANGED << channel, acks, requests, src, time, stamper, 
                             value, TS, state, type >>

L2(self) == /\ pc[self] = "L2"
            /\ channel' = [channel EXCEPT ![self][src[self]] = Append(channel[self][src[self]], ([time |-> clock[self]+1, type |-> "Ack", stamp |-> TS[self], value |-> state[self]]))]
            /\ pc' = [pc EXCEPT ![self] = "tic"]
            /\ UNCHANGED << clock, acks, requests, src, time, stamper, value, 
                            TS, state, type >>

L3(self) == /\ pc[self] = "L3"
            /\ channel' = [channel EXCEPT ![self][src[self]] = Append(channel[self][src[self]], ([time |-> clock[self]+1, type |-> "Ack", stamp |-> TS[self], value |-> state[self]]))]
            /\ pc' = [pc EXCEPT ![self] = "tic"]
            /\ UNCHANGED << clock, acks, requests, src, time, stamper, value, 
                            TS, state, type >>

L4(self) == /\ pc[self] = "L4"
            /\ channel' = [channel EXCEPT ![self][src[self]] = Append(channel[self][src[self]], ([time |-> clock[self]+1, type |-> "Ack", stamp |-> TS[self], value |-> 0]))]
            /\ pc' = [pc EXCEPT ![self] = "tic"]
            /\ UNCHANGED << clock, acks, requests, src, time, stamper, value, 
                            TS, state, type >>

Proc(self) == loop(self) \/ tic(self) \/ L2(self) \/ L3(self) \/ L4(self)

Next == (\E self \in Pid: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

ReplicaConsistency == \A p1, p2 \in ReplicaPids : (TS[p1] = TS[p2] => state[p1] = state[p2])

\* Essential variables to be monitored by TLC
View == <<channel, TS, state, clock, acks, requests, pc>>

====

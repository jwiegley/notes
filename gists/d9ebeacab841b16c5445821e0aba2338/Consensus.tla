--------------------- MODULE Consensus ---------------------------

(* The DFINITY Consensus Algorithm.

   See https://dfinity.org/tech/
 *)

\* TODO: Add a request queue for proposals and notarizations
\* TODO: Add notaries
\* TODO: Add finalization

EXTENDS TLC, Naturals, Integers, Sequences, FiniteSets

CONSTANTS NodeCount, BlockCount, LastRound

Nodes  == 1..NodeCount
Blocks == 1..BlockCount
Rounds == 1..LastRound

PT == INSTANCE PT

(* --termination --fair algorithm Consensus {

variables
  NextBlock = 1,
  Rank      = [ b \in Blocks |-> 0 ],
  Round     = [ n \in Nodes  |-> 1 ],
  Messages  = {};

define {
  NodeRank(n) == n
  Majority(n) == (n \div 3) * 2 + 1
  Honest(n)   == n < Majority(NodeCount)
  Even(n)     == n % 2 = 0
  Notary(n)   == Even(n)
  LiveNodes   == { \A n \in Nodes: Round[n] <= LastRound }
  Notaries    == Cardinality(LiveNodes) \div 2

  Pending(proposals,signed) == 
    { p \in proposals: 
      /\ (~ \E q \in proposals: Rank[q] < Rank[p])
      /\ (~ (p \in DOMAIN signed)) }

  x ++ y == x \union {y}
  x -- y == x \ {y}
}

macro Incr(i) {
  i := i + 1;
}

macro HandleMessage(msg) {
  if (msg.body.type = "proposal") {
    Proposals := Proposals ++ msg.body.block;
  }
  else if (msg.body.type = "signature") {
    if (msg.body.block \in DOMAIN Signed) {
      Signed := msg.body.block
        :> Signed[msg.body.block] ++ msg.fromNode @@ Signed;
    } else {
      Signed := msg.body.block :> {msg.fromNode} @@ Signed;
    }
  }
}

macro Finalize() {
  \* Finalization is much like garbage collection, as its function is to
  \* prune away any dead chains.

  Incr(Round[self]);
}

\* Messages are broadcast back to the node itself, so it can record
\* its own notarized blocks, and sign its own created blocks.
macro Broadcast(body) {
  Messages := PT!ReduceSet(LAMBDA j, acc: acc ++
      [ fromNode |-> self
      , toNode   |-> j
      , body     |-> body ], 
    LiveNodes, 
    Messages);
}

macro MakeBlock() {
  Incr(NextBlock);
  Rank[NextBlock - 1] := NodeRank(self);
  Broadcast(
    [ type  |-> "proposal"
    , block |-> NextBlock - 1 ]);
}

\* ℬ ← set of all valid round-r block proposals so far
\* for All B ∈ ℬ with minimal rk B do
procedure Notarize(SoFar) {
Prepare:
  Proposals := Proposals \ SoFar;
Rebroadcast:
  while (SoFar /= {}) {
    with (p \in SoFar) {
      Broadcast(
        [ type  |-> "signature"
        , block |-> p ]);
      SoFar := SoFar -- p;
    };
  };
}

procedure handleNode()
  variables 
    Signed    = 0 :> {},
    Proposals = {}, 
    Queue     = {};
{
BlockMaker:
  if (NextBlock + 1 <= BlockCount) {
    MakeBlock();
  };

ReceiveAndSign:
  \* jww (2018-11-26): We cannot proceed to finalization until we know that
  \* we've seen a majority of signatures (2/3) up to the current round for
  \* the highest ranked block, or we see a new random beacon.

  \* while no notarization for round r received do
  while (/\ Majority(Notaries) < Cardinality(LiveNodes) 
         /\ \A b \in DOMAIN Signed: 
             Cardinality(Signed[b]) < Majority(Notaries)) {

    Queue := { m \in Messages : m.toNode = self };
    Messages := Messages \ Queue;
    await (Queue /= {});

  ReceiveMessages:
    while (Queue /= {}) {
      with (msg \in Queue) {
        HandleMessage(msg);
        Queue := Queue -- msg;
      }
    };

    if (Notary(self)) {
      call Notarize(Pending(Proposals, Signed));
    }
  };

  Finalize();

  return;
}

process (dishonestNode \in { n \in Nodes: ~ Honest(n) })
{
DishonestNode:
  while (Round[self] <= LastRound) {
    call handleNode();
  }
}

fair+ process (honestNode \in { n \in Nodes: Honest(n) })
{
HonestNode:
  while (Round[self] <= LastRound) {
    call handleNode();
  }
}

} *)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES NextBlock, Rank, Round, Messages, pc, stack

(* define statement *)
NodeRank(n) == n
Majority(n) == n \div 2 + 1
Honest(n)   == n < Majority(NodeCount)
Even(n)     == n % 2 = 0
Notary(n)   == Even(n)
LiveNodes   == { \A n \in Nodes: Round[n] <= LastRound }
Notaries    == Cardinality(LiveNodes) \div 2

Pending(proposals,signed) ==
  { p \in proposals:
    /\ (~ \E q \in proposals: Rank[q] < Rank[p])
    /\ (~ (p \in DOMAIN signed)) }

x ++ y == x \union {y}
x -- y == x \ {y}

VARIABLES SoFar, Signed, Proposals, Queue

vars == << NextBlock, Rank, Round, Messages, pc, stack, SoFar, Signed, 
           Proposals, Queue >>

ProcSet == ({ n \in Nodes: ~ Honest(n) }) \cup ({ n \in Nodes: Honest(n) })

Init == (* Global variables *)
        /\ NextBlock = 1
        /\ Rank = [ b \in Blocks |-> 0 ]
        /\ Round = [ n \in Nodes  |-> 1 ]
        /\ Messages = {}
        (* Procedure Notarize *)
        /\ SoFar = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure handleNode *)
        /\ Signed = [ self \in ProcSet |-> 0 :> {}]
        /\ Proposals = [ self \in ProcSet |-> {}]
        /\ Queue = [ self \in ProcSet |-> {}]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in { n \in Nodes: ~ Honest(n) } -> "DishonestNode"
                                        [] self \in { n \in Nodes: Honest(n) } -> "HonestNode"]

Prepare(self) == /\ pc[self] = "Prepare"
                 /\ Proposals' = [Proposals EXCEPT ![self] = Proposals[self] \ SoFar[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Rebroadcast"]
                 /\ UNCHANGED << NextBlock, Rank, Round, Messages, stack, 
                                 SoFar, Signed, Queue >>

Rebroadcast(self) == /\ pc[self] = "Rebroadcast"
                     /\ IF SoFar[self] /= {}
                           THEN /\ \E p \in SoFar[self]:
                                     /\ Messages' =           PT!ReduceSet(LAMBDA j, acc: acc ++
                                                      [ fromNode |-> self
                                                      , toNode   |-> j
                                                      , body     |-> ([ type  |-> "signature"
                                                                      , block |-> p ]) ],
                                                    LiveNodes,
                                                    Messages)
                                     /\ SoFar' = [SoFar EXCEPT ![self] = SoFar[self] -- p]
                                /\ pc' = [pc EXCEPT ![self] = "Rebroadcast"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                                /\ UNCHANGED << Messages, SoFar >>
                     /\ UNCHANGED << NextBlock, Rank, Round, stack, Signed, 
                                     Proposals, Queue >>

Notarize(self) == Prepare(self) \/ Rebroadcast(self)

BlockMaker(self) == /\ pc[self] = "BlockMaker"
                    /\ IF NextBlock + 1 <= BlockCount
                          THEN /\ NextBlock' = NextBlock + 1
                               /\ Rank' = [Rank EXCEPT ![NextBlock' - 1] = NodeRank(self)]
                               /\ Messages' =           PT!ReduceSet(LAMBDA j, acc: acc ++
                                                [ fromNode |-> self
                                                , toNode   |-> j
                                                , body     |-> ([ type  |-> "proposal"
                                                                , block |-> NextBlock' - 1 ]) ],
                                              LiveNodes,
                                              Messages)
                          ELSE /\ TRUE
                               /\ UNCHANGED << NextBlock, Rank, Messages >>
                    /\ pc' = [pc EXCEPT ![self] = "ReceiveAndSign"]
                    /\ UNCHANGED << Round, stack, SoFar, Signed, Proposals, 
                                    Queue >>

ReceiveAndSign(self) == /\ pc[self] = "ReceiveAndSign"
                        /\ IF /\ Majority(Notaries) < Cardinality(LiveNodes)
                              /\ \A b \in DOMAIN Signed[self]:
                                  Cardinality(Signed[self][b]) < Majority(Notaries)
                              THEN /\ Queue' = [Queue EXCEPT ![self] = { m \in Messages : m.toNode = self }]
                                   /\ Messages' = Messages \ Queue'[self]
                                   /\ (Queue'[self] /= {})
                                   /\ pc' = [pc EXCEPT ![self] = "ReceiveMessages"]
                                   /\ UNCHANGED << Round, stack, Signed, 
                                                   Proposals >>
                              ELSE /\ Round' = [Round EXCEPT ![self] = (Round[self]) + 1]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ Signed' = [Signed EXCEPT ![self] = Head(stack[self]).Signed]
                                   /\ Proposals' = [Proposals EXCEPT ![self] = Head(stack[self]).Proposals]
                                   /\ Queue' = [Queue EXCEPT ![self] = Head(stack[self]).Queue]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED Messages
                        /\ UNCHANGED << NextBlock, Rank, SoFar >>

ReceiveMessages(self) == /\ pc[self] = "ReceiveMessages"
                         /\ IF Queue[self] /= {}
                               THEN /\ \E msg \in Queue[self]:
                                         /\ IF msg.body.type = "proposal"
                                               THEN /\ Proposals' = [Proposals EXCEPT ![self] = Proposals[self] ++ msg.body.block]
                                                    /\ UNCHANGED Signed
                                               ELSE /\ IF msg.body.type = "signature"
                                                          THEN /\ IF msg.body.block \in DOMAIN Signed[self]
                                                                     THEN /\ Signed' = [Signed EXCEPT ![self] =         msg.body.block
                                                                                                                :> Signed[self][msg.body.block] ++ msg.fromNode @@ Signed[self]]
                                                                     ELSE /\ Signed' = [Signed EXCEPT ![self] = msg.body.block :> {msg.fromNode} @@ Signed[self]]
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED Signed
                                                    /\ UNCHANGED Proposals
                                         /\ Queue' = [Queue EXCEPT ![self] = Queue[self] -- msg]
                                    /\ pc' = [pc EXCEPT ![self] = "ReceiveMessages"]
                                    /\ UNCHANGED << stack, SoFar >>
                               ELSE /\ IF Notary(self)
                                          THEN /\ /\ SoFar' = [SoFar EXCEPT ![self] = Pending(Proposals[self], Signed[self])]
                                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Notarize",
                                                                                           pc        |->  "ReceiveAndSign",
                                                                                           SoFar     |->  SoFar[self] ] >>
                                                                                       \o stack[self]]
                                               /\ pc' = [pc EXCEPT ![self] = "Prepare"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "ReceiveAndSign"]
                                               /\ UNCHANGED << stack, SoFar >>
                                    /\ UNCHANGED << Signed, Proposals, Queue >>
                         /\ UNCHANGED << NextBlock, Rank, Round, Messages >>

handleNode(self) == BlockMaker(self) \/ ReceiveAndSign(self)
                       \/ ReceiveMessages(self)

DishonestNode(self) == /\ pc[self] = "DishonestNode"
                       /\ IF Round[self] <= LastRound
                             THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "handleNode",
                                                                           pc        |->  "DishonestNode",
                                                                           Signed    |->  Signed[self],
                                                                           Proposals |->  Proposals[self],
                                                                           Queue     |->  Queue[self] ] >>
                                                                       \o stack[self]]
                                  /\ Signed' = [Signed EXCEPT ![self] = 0 :> {}]
                                  /\ Proposals' = [Proposals EXCEPT ![self] = {}]
                                  /\ Queue' = [Queue EXCEPT ![self] = {}]
                                  /\ pc' = [pc EXCEPT ![self] = "BlockMaker"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << stack, Signed, Proposals, 
                                                  Queue >>
                       /\ UNCHANGED << NextBlock, Rank, Round, Messages, SoFar >>

dishonestNode(self) == DishonestNode(self)

HonestNode(self) == /\ pc[self] = "HonestNode"
                    /\ IF Round[self] <= LastRound
                          THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "handleNode",
                                                                        pc        |->  "HonestNode",
                                                                        Signed    |->  Signed[self],
                                                                        Proposals |->  Proposals[self],
                                                                        Queue     |->  Queue[self] ] >>
                                                                    \o stack[self]]
                               /\ Signed' = [Signed EXCEPT ![self] = 0 :> {}]
                               /\ Proposals' = [Proposals EXCEPT ![self] = {}]
                               /\ Queue' = [Queue EXCEPT ![self] = {}]
                               /\ pc' = [pc EXCEPT ![self] = "BlockMaker"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << stack, Signed, Proposals, Queue >>
                    /\ UNCHANGED << NextBlock, Rank, Round, Messages, SoFar >>

honestNode(self) == HonestNode(self)

Next == (\E self \in ProcSet: Notarize(self) \/ handleNode(self))
           \/ (\E self \in { n \in Nodes: ~ Honest(n) }: dishonestNode(self))
           \/ (\E self \in { n \in Nodes: Honest(n) }: honestNode(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in { n \in Nodes: Honest(n) } : /\ SF_vars(honestNode(self))
                                                    /\ SF_vars(handleNode(self))                                                    /\ SF_vars(Notarize(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

==============================================
Specification.


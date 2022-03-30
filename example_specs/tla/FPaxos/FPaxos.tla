-------------------------------- MODULE FPaxos -------------------------------

EXTENDS Integers
CONSTANT Value, Acceptor, Quorum1, Quorum2

Ballot == Nat

ASSUME QuorumAssumption == /\ \A Q \in Quorum1 : Q \subseteq Acceptor   \* Set of Phase 1 quorums
                           /\ \A Q \in Quorum2 : Q \subseteq Acceptor   \* Set of Phase 2 quorums
                           /\ \A Q1 \in Quorum1 : \A Q2 \in Quorum2 : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Value  

Message ==      [type : {"1a"}, bal : Ballot]  \* Set of all records with type in set {"1a"} and bal in set Ballot
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value \cup {None}]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value \cup {None}]

VARIABLE maxBal,
         maxVBal,
         maxVal,
         msgs

vars == <<maxBal, maxVBal, maxVal, msgs>>  \* System state
Send(m) == msgs' = msgs \cup {m}

TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]  \* maxBal maps acceptors to Ballots+{-1}
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}] \* maxVBal maps acceptors to Ballots+{-1} 
          /\ maxVal \in [Acceptor -> Value \cup {None}] \* maxVal maps acceptors to Value+{None}
          /\ msgs \subseteq Message                     \* msgs collection is a subset of Message type

Init == /\ maxBal = [a \in Acceptor |-> -1]         \* Every acceptor has maxBal = -1
        /\ maxVBal = [a \in Acceptor |-> -1]        \* Every acceptor has maxVBal = -1
        /\ maxVal = [a \in Acceptor |-> None]       \* Every acceptor has maxVal = None
        /\ msgs = {}                                \* No sent messages in the initial state

\* Broadcast Phase1a(b) in the network
Phase1a(b) == /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

\* Acceptor a responds to a Phase1a message in the network
Phase1b(a) == /\ \E m \in msgs :
                  /\ m.type = "1a"
                  /\ m.bal > maxBal[a]
                  /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                  /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                            mbal |-> maxVBal[a], mval |-> maxVal[a]])
              /\ UNCHANGED <<maxVBal, maxVal>>

\* Broadcast Phase2a(b, v) under the following conditions:
\* 1. Have yet to propose for this ballot b
\* 2. There is a phase 1 quorum of messages that either support v, or carry no prior accepted values
Phase2a(b, v) ==
  /\ v \in Value
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorum1 :
        LET Q1b == {m \in msgs : /\ m.type = "1b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
            Q1bv == {m \in Q1b : m.mbal \geq 0}     \* Set of messages that carry prior accepted values
        IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal \geq mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>


\* Acceptor a responds to a Phase2a proposal in the network
Phase2b(a) == \E m \in msgs : /\ m.type = "2a"
                              /\ m.bal \geq maxBal[a]
                              /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                              /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
                              /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
                              /\ Send([type |-> "2b", acc |-> a,
                                       bal |-> m.bal, val |-> m.val])

Next == \/ \E b \in Ballot : \/ Phase1a(b)
                             \/ \E v \in Value \cup {None} : Phase2a(b, v)
        \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

Sent2b(a,v,b) == \E m \in msgs: /\ m.type = "2b"
                                /\ m.acc = a
                                /\ m.val = v
                                /\ m.bal = b

Sent2a(v,b) == \E m \in msgs: /\ m.type = "2a"
                              /\ m.val = v
                              /\ m.bal = b

\* A value v is agreed at ballot b is there is a quorum of 2b(v, b) packets
Agreed(v,b) == \E Q \in Quorum2: \A a \in Q: Sent2b(a,v,b)

\* All proposals with ballot >b must be of value v
NoFutureProposal(v,b) == \A v2 \in Value: \A b2 \in Ballot: (b2 > b /\ Sent2a(v2,b2)) => v=v2

NotNone2a == \A m \in msgs : m.type = "2a" => m.val \in Value
NotNone2b == \A m \in msgs : m.type = "2b" => m.val \in Value

\* Safety: If (v, b) is agreed, then all proposals with ballot >b must be of value v
SafeValue == \A v \in Value \cup {None}: \A b \in Ballot: Agreed(v,b) => (NoFutureProposal(v,b) /\ v \in Value)

=============================================================================


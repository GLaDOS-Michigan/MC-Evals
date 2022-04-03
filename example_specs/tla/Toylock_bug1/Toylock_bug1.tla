-------------------------------- MODULE Toylock_bug1 -------------------------------

\* BUG: Node granting the lock does not grant with a strictly larger epoch.

EXTENDS Integers
CONSTANT Node

Epoch == Nat

Message ==      [type : {"Transfer"}, ep : Epoch, dst : Node]   \* Set of all records with type in set {"Transfer"} and ep in set Epoch and etc...
           \cup [type : {"Locked"}, ep : Epoch, src : Node]

VARIABLE epoch,
         held,
         msgs

vars == <<epoch, held, msgs>>  \* System state
Send(m) == msgs' = msgs \cup {m}

TypeOK == /\ epoch \in [Node -> Epoch]          \* epoch maps nodes to Epoch
          /\ held \in [Node -> BOOLEAN ]        \* held maps nodes to TRUE/FALSE
          /\ msgs \subseteq Message             \* msgs collection is a subset of Message type


Init == /\ epoch \in [Node -> Epoch]
        /\ held \in [Node -> BOOLEAN ]
        /\ msgs = {}
        /\ \E n0 \in Node :    
            /\ epoch[n0] # 0        \* n0 has non-zero epoch
            /\ held[n0]             \* n0 holds lock
            /\ \A n \in Node :      \* all other nodes has epoch 0 and don't hold lock
                    n # n0 => epoch[n] = 0 /\ ~held[n]

Grant(n1, n2, e) == /\ held[n1]         \* enabling condition: n1 holds lock
                    \* This is the BUG
                    \* /\ e > epoch[n1]    \* pick some epoch > epoch(n1)
                    /\ Send([type |-> "Transfer", ep |-> e, dst |-> n2])
                    /\ held' = [held EXCEPT ![n1] = FALSE]
                    /\ UNCHANGED <<epoch>>

Accept(n, e) == \E m \in msgs: /\ m.type = "Transfer"
                               /\ m.ep = e
                               /\ m.dst = n
                               /\ epoch[n] < e         \* above conjuncts are enabling condition
                               /\ held' = [held EXCEPT ![n] = TRUE]
                               /\ epoch' = [epoch EXCEPT ![n] = e]
                               /\ Send([type |-> "Locked", ep |-> e, src |-> n])

Stutter == UNCHANGED <<epoch, held, msgs>>

Next == \/ \E n1, n2 \in Node : 
            \E e \in Epoch : Grant(n1, n2, e)
        \/ \E n \in Node : 
            \E e \in Epoch : Accept(n, e)
        \/ Stutter
        
Spec == Init /\ [][Next]_vars

SafetyI4 == \A m1, m2 \in msgs :
            m1.type = "Locked" /\ m2.type = "Locked" /\ m1.ep = m2.ep => m1.src = m2.src


=============================================================================


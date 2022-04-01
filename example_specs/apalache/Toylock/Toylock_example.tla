-------------------------------- MODULE Toylock_example -------------------------------

EXTENDS Naturals

Epoch == 0..2
Node == {"n0", "n1"}

\* Set of all records with type in set {"Transfer", "Locked"} and ep in set Epoch and etc...
Message == [type : {"Transfer", "Locked"}, ep : Epoch, n : Node]   

VARIABLE 
    \* @type: Str;
    n0,
    \* @type: Str;
    n1,
    \* @type:Str->Int;
    epoch,
    \* @type:Str->Bool;
    held,
    \* @type:Set([type : Str, ep : Int, n : Str]);
    msgs

vars == <<n0, n1, epoch, held, msgs>>  \* System state

\* @type:([type : Str, ep : Int, n : Str]) => Bool;
Send(m) == msgs' = msgs \cup {m}

TypeOK == /\ n0 = "n0"
          /\ n1 = "n1"
          /\ epoch \in [Node -> Epoch]          \* epoch maps nodes to Epoch
          /\ held \in [Node -> BOOLEAN]        \* held maps nodes to TRUE/FALSE
          /\ msgs \subseteq Message             \* msgs collection is a subset of Message type


Init == /\ n0 = "n0"
        /\ n1 = "n1"
        /\ epoch \in [Node -> Epoch]
        /\ held \in [Node -> BOOLEAN]
        /\ msgs = {}
        /\ \E a \in Node :    
            /\ epoch[a] # 0        \* a has non-zero epoch
            /\ held[a]             \* a holds lock
            /\ \A n \in Node :      \* all other nodes has epoch 0 and don't hold lock
                    a # n => epoch[n] = 0 /\ ~held[n]

Grant(a1, a2, e) == /\ held[a1]         \* enabling condition: a1 holds lock
                    /\ e > epoch[a1]    \* pick some epoch > epoch(a1)
                    /\ Send([type |-> "Transfer", ep |-> e, n |-> a2])
                    /\ held' = [held EXCEPT ![a1] = FALSE]
                    /\ UNCHANGED <<epoch>>

Accept(a1, e) == \E m \in msgs: /\ m.type = "Transfer"
                               /\ m.ep = e
                               /\ m.n = a1
                               /\ epoch[a1] < e         \* above conjuncts are enabling condition
                               /\ held' = [held EXCEPT ![a1] = TRUE]
                               /\ epoch' = [epoch EXCEPT ![a1] = e]
                               /\ Send([type |-> "Locked", ep |-> e, n |-> a1])

Stutter == UNCHANGED <<epoch, held, msgs>>

Next == /\ UNCHANGED << n0, n1 >>
        /\  \/ \E a1, a2 \in Node : 
                \E e \in Epoch : Grant(a1, a2, e)
            \/ \E a1 \in Node : 
                \E e \in Epoch : Accept(a1, e)
            \/ Stutter
        
Spec == Init /\ [][Next]_vars

Safety == \A a1, a2 \in Node :
            held[a1] /\ held[a2] => a1 = a2 

SafetyI4 == \A m1, m2 \in msgs :
            m1.type = "Locked" /\ m2.type = "Locked" /\ m1.ep = m2.ep => m1.n = m2.n

=============================================================================
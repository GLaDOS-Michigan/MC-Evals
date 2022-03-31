-------------------------------- MODULE Toylock_Insane_example -------------------------------

\* This is a hand-written example spec of size (2, 2)

EXTENDS Naturals
VARIABLE
    \* @type:[id : Int, held : Bool, epoch : Int];
    n0
VARIABLE
    \* @type:[id : Int, held : Bool, epoch : Int];
    n1
VARIABLE
    \* @type:Int->Int->Bool;
    transfer
VARIABLE
    \* @type:Int->Int->Bool;
    locked
VARIABLE
    \* @type:Int;
    first_node
VARIABLE
    \* @type:Int;
    first_epoch
VARIABLE
    \* @type:Str;
    action
VARIABLE
    \* @type:Int;
    actor
VARIABLE
    \* @type:Int;
    grant_dst
VARIABLE
    \* @type:Int;
    accept_ep
\* System state
vars == <<n0, n1, transfer, locked, first_node, first_epoch, action, actor, grant_dst, accept_ep>>

nodeIDs == {0, 1}
epochs == {0, 1}

TypeOK == /\ n0 \in [id : {0}, held : BOOLEAN, epoch : epochs]
          /\ n1 \in [id : {1}, held : BOOLEAN, epoch : epochs]
          /\ transfer \in [nodeIDs -> [epochs -> BOOLEAN]]
          /\ locked \in [nodeIDs -> [epochs -> BOOLEAN]]
          /\ first_node \in nodeIDs
          /\ first_epoch \in epochs\{ 0 }
          /\ action \in {"grant", "accept", "stutter"}
          /\ actor \in nodeIDs
          /\ grant_dst \in nodeIDs
          /\ accept_ep \in epochs

constants_next == /\ n0' \in [id : {0}, held : BOOLEAN, epoch : epochs]
                  /\ n1' \in [id : {1}, held : BOOLEAN, epoch : epochs]
                  /\ n0'.id = n0.id
                  /\ n1'.id = n1.id
                  /\ first_node' = first_node
                  /\ first_epoch' = first_epoch

non_deterministics_next == /\ action' \in {"grant", "accept", "stutter"}
                           /\ actor' \in nodeIDs
                           /\ grant_dst' \in nodeIDs
                           /\ accept_ep' \in epochs

n0_stutter == n0' = n0
n1_stutter == n1' = n1
stutter_step == n0'=n0 /\ n1'=n1 /\ transfer'=transfer /\ locked'=locked

grant_step ==
    /\ action = "grant"
    /\ transfer' \in [nodeIDs -> [epochs -> BOOLEAN]]
    /\ CASE actor = 0 /\ n0.held ->
            /\ n1_stutter
            /\ n0'.held = (n0.epoch = 1)
            /\ n0'.epoch = n0.epoch
            /\ transfer'[0][0] = (IF grant_dst = 0 /\ n0.epoch + 1 = 0 THEN TRUE ELSE transfer[0][0])
            /\ transfer'[0][1] = (IF grant_dst = 0 /\ n0.epoch + 1 = 1 THEN TRUE ELSE transfer[0][1])
            /\ transfer'[1][0] = (IF grant_dst = 1 /\ n0.epoch + 1 = 0 THEN TRUE ELSE transfer[1][0])
            /\ transfer'[1][1] = (IF grant_dst = 1 /\ n0.epoch + 1 = 1 THEN TRUE ELSE transfer[1][1])
            /\ UNCHANGED <<locked>>
         [] actor = 1 /\ n1.held ->
            /\ n0_stutter
            /\ n1'.held = (n1.epoch = 1)
            /\ n1'.epoch = n1.epoch
            /\ transfer'[0][0] = (IF grant_dst = 0 /\ n1.epoch + 1 = 0 THEN TRUE ELSE transfer[0][0])
            /\ transfer'[0][1] = (IF grant_dst = 0 /\ n1.epoch + 1 = 1 THEN TRUE ELSE transfer[0][1])
            /\ transfer'[1][0] = (IF grant_dst = 1 /\ n1.epoch + 1 = 0 THEN TRUE ELSE transfer[1][0])
            /\ transfer'[1][1] = (IF grant_dst = 1 /\ n1.epoch + 1 = 1 THEN TRUE ELSE transfer[1][1])
            /\ UNCHANGED <<locked>>
         [] OTHER -> stutter_step

accept_step ==
    /\ action = "accept"
    /\ locked' \in [nodeIDs -> [epochs -> BOOLEAN]]
    /\ CASE actor = 0 /\ ~n0.held /\ accept_ep > n0.epoch /\ transfer[0][accept_ep] ->
            /\ n1_stutter
            /\ n0'.held
            /\ n0'.epoch = accept_ep
            /\ UNCHANGED << transfer >>
            /\ locked'[0][0] = (IF accept_ep = 0 THEN TRUE ELSE locked[0][0])
            /\ locked'[0][1] = (IF accept_ep = 1 THEN TRUE ELSE locked[0][1])
            /\ locked'[1][0] = locked[1][0]
            /\ locked'[1][1] = locked[1][1]
         [] actor = 1 /\ ~n1.held /\ accept_ep > n1.epoch /\ transfer[1][accept_ep]->
            /\ n0_stutter
            /\ n1'.held
            /\ n1'.epoch = accept_ep
            /\ UNCHANGED << transfer >>
            /\ locked'[0][0] = locked[0][0]
            /\ locked'[0][1] = locked[0][1]
            /\ locked'[1][0] = (IF accept_ep = 0 THEN TRUE ELSE locked[1][0])
            /\ locked'[1][1] = (IF accept_ep = 1 THEN TRUE ELSE locked[1][1])
         [] OTHER -> stutter_step

Init == /\ transfer \in [nodeIDs -> [epochs -> BOOLEAN]]
        /\ locked \in [nodeIDs -> [epochs -> BOOLEAN]]
        /\ first_node \in nodeIDs
        /\ first_epoch \in epochs\{ 0 }
        /\ action \in {"grant", "accept", "stutter"}
        /\ actor \in nodeIDs
        /\ grant_dst \in nodeIDs
        /\ accept_ep \in epochs
        /\ n0 = [id |-> 0, held |-> (first_node = 0), epoch |-> (IF first_node = 0 THEN first_epoch ELSE 0)]
        /\ n1 = [id |-> 1, held |-> (first_node = 1), epoch |-> (IF first_node = 1 THEN first_epoch ELSE 0)]
        /\ \A id \in nodeIDs: 
            \A e \in epochs : /\ transfer[id][e] = FALSE
                              /\ locked[id][e] = FALSE

Next == /\ constants_next
        /\ non_deterministics_next
        /\ CASE action = "grant" -> grant_step
             [] action = "accept" -> accept_step
             [] OTHER -> stutter_step


Spec == Init /\ [][Next]_vars
Safety == ~ (n0.held /\ n1.held)
SafetyI4 == \A e \in epochs : \A a, b \in {n0, n1} : locked[a.id][e] /\ locked[b.id][e] => a.id = b.id

=============================================================================
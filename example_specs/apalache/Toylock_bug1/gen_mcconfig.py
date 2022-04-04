import sys
from itertools import chain, combinations

def main(num_nodes, num_epochs):
    tla_str = gen_tla_file(num_nodes, num_epochs)
    cfg_str = gen_cfg_file(num_nodes, num_epochs)
    with open('Toylock_bug1.tla', 'w') as f:
        f.write(tla_str)
    with open('Toylock_bug1.cfg', 'w') as f:
        f.write(cfg_str)

def gen_tla_file(num_nodes, num_epochs):
    """ Returns the Toylock_bug1.tla file contents as string """    
    res = []
    res.append("---------------------------- MODULE Toylock_bug1 ----------------------------")
    res.append("\* BUG: Node granting the lock does not grant with a strictly larger epoch.")
    res.append("EXTENDS Naturals")
    res.append("")
    res.append("Epoch == 0..%d" %(num_epochs-1))
    res.append("Node == { %s }" %(", ".join(["\"n%d\"" %i for i in range(num_nodes)])))
    res.append("Message == [type : {\"Transfer\", \"Locked\"}, ep : Epoch, n : Node]   ")
    res.append("")
    res.append(gen_tla_file_variables(num_nodes))
    res.append("")
    res.append("vars == <<%s, epoch, held, msgs>> " %(", ".join(["n%d" %i for i in range(num_nodes)])))
    res.append("")
    res.append("\* @type:([type : Str, ep : Int, n : Str]) => Bool;")
    res.append("Send(m) == msgs' = msgs \cup {m}")
    res.append("")
    res.append(gen_tla_file_typeok(num_nodes))
    res.append("")
    res.append(gen_tla_file_init(num_nodes))
    res.append("")
    res.append("Stutter == UNCHANGED <<epoch, held, msgs>>")
    res.append("")
    res.append(gen_tla_file_grant())
    res.append("")
    res.append(gen_tla_file_accept())
    res.append("")
    res.append(gen_tla_file_next())
    res.append("")
    res.append(gen_tla_file_specs())
    res.append("")


    res.append("=============================================================================")
    return "\n".join(res)

def gen_tla_file_variables(num_nodes):
    decls = []
    for i in range(num_nodes):
        decls.append("\* @type: Str;\n    n%d" %i)
    decls.append("\* @type: Str->Int;\n    epoch")
    decls.append("\* @type: Str->Bool;\n    held")
    decls.append("\* @type: Set([type : Str, ep : Int, n : Str]);\n    msgs")
    return "VARIABLE\n    " + ",\n    ".join(decls)


def gen_tla_file_typeok(num_nodes):
    clauses = []
    for i in range(num_nodes):
        clauses.append("n%d = \"n%d\"" %(i,i))
    clauses += ["epoch \in [Node -> Epoch]", 
                "held \in [Node -> BOOLEAN]", 
                "msgs \subseteq Message"]
    return "TypeOK == /\ " + "\n          /\ ".join(clauses)

def gen_tla_file_init(num_nodes):
    clauses = []
    for i in range(num_nodes):
        clauses.append("n%d = \"n%d\"" %(i,i))
    clauses += ["epoch \in [Node -> Epoch]", 
                "held \in [Node -> BOOLEAN]", 
                "msgs = { }",
                "\E a \in Node :\n              /\ epoch[a] # 0\n              /\ held[a]\n              /\ \A n \in Node :\n                  a # n => epoch[n] = 0 /\ ~held[n]"]
    return "Init == /\ " + "\n          /\ ".join(clauses)

def gen_tla_file_grant():
    return """Grant(a1, a2, e) == /\ held[a1]         \* enabling condition: a1 holds lock
                    \* This is the BUG
                    \* /\ e > epoch[a1]    \* pick some epoch > epoch(a1)
                    /\ Send([type |-> "Transfer", ep |-> e, n |-> a2])
                    /\ held' = [held EXCEPT ![a1] = FALSE]
                    /\ UNCHANGED <<epoch>>"""

def gen_tla_file_accept():
    return """Accept(a1, e) == \E m \in msgs: /\ m.type = "Transfer"
                                /\ m.ep = e
                                /\ m.n = a1
                                /\ IF epoch[n] < e         \* above conjuncts are enabling condition
                                   THEN /\ held' = [held EXCEPT ![n] = TRUE]
                                        /\ epoch' = [epoch EXCEPT ![n] = e]
                                        /\ Send([type |-> "Locked", ep |-> e, src |-> n])
                                   ELSE 
                                     Stutter"""

def gen_tla_file_next():
    res = []
    res.append("")
    res.append("Next == /\ UNCHANGED << %s >> " %(", ".join(["n%d" %i for i in range(num_nodes)])))
    res.append("""        /\  \/ \E a1, a2 \in Node : 
                \E e \in Epoch : Grant(a1, a2, e)
            \/ \E a1 \in Node : 
                \E e \in Epoch : Accept(a1, e)
            \/ Stutter""")
    return "\n".join(res)

def gen_tla_file_specs():
    res = []
    res.append("Spec == Init /\ [][Next]_vars")
    res.append("""SafetyI4 == \A m1, m2 \in msgs :
            m1.type = "Locked" /\ m2.type = "Locked" /\ m1.ep = m2.ep => m1.n = m2.n""")
    return "\n\n".join(res)


def gen_cfg_file(num_nodes, num_epochs):
    """ Returns the Toylock_bug1.tla file contents as string """ 
    nodes = ["n%d" %i for i in range(num_nodes)]
    
    res = []
    res.append("SPECIFICATION Spec")
    res.append("")
    res.append("INVARIANTS TypeOK SafetyI4")
    return "\n".join(res)

if __name__ == "__main__":
    # positional arguments <#nodes> <#epochs>
    if len(sys.argv) != 3:
        print("Error: Expect <#nodes> <#epochs> as input")
        sys.exit(1)
    num_nodes, num_epochs = int(sys.argv[1]), int(sys.argv[2])
    main(num_nodes, num_epochs)
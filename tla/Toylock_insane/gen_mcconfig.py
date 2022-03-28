import sys
from itertools import chain, combinations

def main(num_nodes, num_epochs):
    tla_str = gen_tla_file(num_nodes, num_epochs)
    cfg_str = gen_cfg_file()
    with open('Toylock_Insane.tla', 'w') as f:
        f.write(tla_str)
    with open('Toylock_Insane.cfg', 'w') as f:
        f.write(cfg_str)

def gen_tla_file(num_nodes, num_epochs):
    """ Returns the Toylock_Insane.tla file contents as string """ 
    res = ["------------------------------- MODULE Toylock_Insane -------------------------------", "EXTENDS Integers"]
    res.append(gen_tla_file_variables(num_nodes, num_epochs))
    res.append(gen_tla_file_definitions(num_nodes, num_epochs))
    res.append(gen_tla_file_spec(num_nodes, num_epochs))
    res.append("")
    res.append("=============================================================================")
    return "\n".join(res)

def gen_tla_file_variables(num_nodes, num_epochs):
    res = ["VARIABLE"]
    for i in range(num_nodes):
        res.append("n%d," %i)
    res += ["transfer,", "locked,", "first_node,", "first_epoch,"]
    res.append("")
    res += ["action,", "actor,", "grant_dst,", "accept_ep"]
    res.append("")
    return "\n    ".join(res)


def gen_tla_file_definitions(num_nodes, num_epochs):
    res = ["\* System state", "vars == <<n0, n1, transfer, locked, first_node, first_epoch, action, actor, grant_dst, accept_ep>> "]
    res.append("")
    res.append("nodeIDs == {%s}" %(", ".join([str(i) for i in range(num_nodes)])))
    res.append("epochs == {%s}" %(", ".join([str(e) for e in range(num_epochs)])))
    res.append("")
    res.append(gen_tla_file_definitions_TypeOK(num_nodes))
    res.append("")
    res.append(gen_tla_file_definitions_constants_next(num_nodes))
    res.append("")
    res.append(gen_tla_file_definitions_nondeter_next())
    res.append("")
    res.append(gen_tla_file_definitions_stutter(num_nodes))
    res.append("")
    res.append(gen_tla_file_definitions_grant(num_nodes, num_epochs))
    res.append("")
    res.append(gen_tla_file_definitions_accept(num_nodes, num_epochs))
    res.append("")
    res.append(gen_tla_file_definitions_init(num_nodes))
    res.append("")
    res.append(gen_tla_file_definitions_next())
    res.append("")

    res.append("")
    return "\n".join(res)

def gen_tla_file_definitions_TypeOK(num_nodes):
    clauses = []
    for i in range(num_nodes):
        clauses.append("n%d \in [id : {%i}, held : BOOLEAN, epoch : epochs]" %(i,i))
    clauses += ["transfer \in [nodeIDs -> [epochs -> BOOLEAN]]", 
                "locked \in [nodeIDs -> [epochs -> BOOLEAN]]", 
                "first_node \in nodeIDs", "first_epoch \in epochs\{ 0 }", 
                "action \in {\"grant\", \"accept\", \"stutter\"}", "actor \in nodeIDs", 
                "grant_dst \in nodeIDs", "accept_ep \in nodeIDs"]
    return "TypeOK == /\ " + "\n          /\ ".join(clauses)

def gen_tla_file_definitions_constants_next(num_nodes):
    clauses = []
    for i in range(num_nodes):
        clauses.append("n%d' \in [id : {%i}, held : BOOLEAN, epoch : epochs]" %(i,i))
    for i in range(num_nodes):
        clauses.append("n%d'.id = n%d.id" %(i,i))
    clauses += ["first_node' = first_node", "first_epoch' = first_epoch"]
    return "constants_next == /\ " + "\n                  /\ ".join(clauses)

def gen_tla_file_definitions_nondeter_next():
    clauses = ["action' \in {\"grant\", \"accept\", \"stutter\"}",
               "actor' \in nodeIDs",
               "grant_dst' \in nodeIDs",
               "accept_ep' \in nodeIDs"]
    return "non_deterministics_next == /\ " + "\n                           /\ ".join(clauses)

def gen_tla_file_definitions_stutter(num_nodes):
    res = []
    for i in range(num_nodes):
        res.append("n%d_stutter == n%d' = n%d" %(i,i,i))
    res.append("stutter_step == UNCHANGED << %s, transfer, locked, first_node, first_epoch >>" %(", ".join(["n%d" %i for i in range(num_nodes)])))
    return "\n".join(res)

def gen_tla_file_definitions_grant(num_nodes, num_epochs):
    res = ["grant_step ==", "action = \"grant\""]
    case_bodies = []
    # Enumerate over each actor case
    for act in range(num_nodes):
        act_clauses = []
        act_clauses.append("n%d.held" %act)
        for i in range(num_nodes):
            if i != act:
                act_clauses.append("n%d_stutter" %i)
        act_clauses.append("n%d'.held = (n%d.epoch = %d)" %(act,act,num_epochs-1))
        act_clauses.append("n%d'.epoch = n%d.epoch" %(act,act))
        for i in range(num_nodes):
            for e in range(num_epochs):
                act_clauses.append("transfer'[%d][%d] = (IF grant_dst = %d /\ n%d.epoch + 1 = %d THEN TRUE ELSE transfer[%d][%d])" %(i,e,i,act,e,i,e))
        act_clauses.append("UNCHANGED <<locked>>")
        if act == 0:
            case_bodies.append("CASE actor = 0 ->")
        else:
            case_bodies.append("     [] actor = %d ->" %act)
        case_bodies.append("        /\ " +"\n            /\ ".join(act_clauses))
    case_bodies.append("     [] OTHER -> FALSE")
    res.append("\n    ".join(case_bodies))
    return "\n    /\ ".join(res)

def gen_tla_file_definitions_accept(num_nodes, num_epochs):
    res = ["accept_step ==", "action = \"accept\""]
    case_bodies = []
    # Enumerate over each actor case
    for act in range(num_nodes):
        act_clauses = []
        act_clauses.append("~ n%d.held" %act)
        act_clauses.append("accept_ep > n%d.epoch" %act)
        act_clauses.append("transfer[%d][accept_ep]" %act)
        for i in range(num_nodes):
            if i != act:
                act_clauses.append("n%d_stutter" %i)
        act_clauses.append("n%d'.held" %act)
        act_clauses.append("n%d'.epoch = accept_ep" %act)
        act_clauses.append("UNCHANGED << transfer >>")
        for i in range(num_nodes):
            for e in range(num_epochs):
                if i == act:
                    act_clauses.append("locked'[%d][%d] = (IF accept_ep = %d THEN TRUE ELSE locked[%d][%d])" %(i,e,e,i,e))
                else:
                    act_clauses.append("locked'[%d][%d] = locked'[%d][%d]" %(i,e,i,e))
        if act == 0:
            case_bodies.append("CASE actor = 0 ->")
        else:
            case_bodies.append("     [] actor = %d ->" %act)
        case_bodies.append("        /\ " +"\n            /\ ".join(act_clauses))
    case_bodies.append("     [] OTHER -> FALSE")
    res.append("\n    ".join(case_bodies))
    return "\n    /\ ".join(res)

def gen_tla_file_definitions_init(num_nodes):
    clauses = ["TypeOK"]
    for i in range(num_nodes):
        clauses.append("n%d.id = %d" %(i,i))
        clauses.append("n%d.held = (first_node = %d)" %(i,i))
        clauses.append("n%d.epoch = (IF first_node = %d THEN 1 ELSE 0)" %(i,i))
    clauses.append("\A id \in nodeIDs: \n            \A e \in epochs : /\ transfer[id][e] = FALSE\n                              /\ locked[id][e] = FALSE")
    return "Init == /\ " + "\n        /\ ".join(clauses)

def gen_tla_file_definitions_next():
    clauses = [ "constants_next", "non_deterministics_next",
                "transfer' \in [nodeIDs -> [epochs -> BOOLEAN]]",
                "locked' \in [nodeIDs -> [epochs -> BOOLEAN]]",
                "CASE action = \"grant\" -> grant_step\n             [] action = \"accept\" -> accept_step\n             [] OTHER -> stutter_step"]
    return "Next == /\ " + "\n        /\ ".join(clauses)


def gen_tla_file_spec(num_nodes, num_epochs):
    res = []
    res.append("Spec == Init /\ [][Next]_vars")
    res.append("Safety == ~ (n0.held /\ n1.held)")
    res.append("SafetyI4 == \A e \in epochs : \A a, b \in {n0, n1} : locked[a.id][e] /\ locked[b.id][e] => a.id = b.id")
    return "\n".join(res)


def gen_cfg_file():
    """ Returns the Toylock_Insane.cfg file contents as string """ 
    res = []
    res.append("SPECIFICATION Spec")
    res.append("")
    res.append("INVARIANTS TypeOK Safety SafetyI4")
    res.append("")
    return "\n".join(res)

if __name__ == "__main__":
    # positional arguments <#nodes> <#epochs>
    if len(sys.argv) != 3:
        print("Error: Expect <#nodes> <#epochs> as input")
        sys.exit(1)
    num_nodes, num_epochs = int(sys.argv[1]), int(sys.argv[2])
    main(num_nodes, num_epochs)
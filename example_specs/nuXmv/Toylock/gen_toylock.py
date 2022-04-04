import sys


def main(num_nodes:int, num_epochs:int):
    gen_module_node(num_nodes, num_epochs)
    gen_module_main(num_nodes, num_epochs)
    
    
def gen_module_node(num_nodes:int, num_epochs:int):
    print("MODULE node")
    print("VAR")
    print("    id : {%s};" %(", ".join([str(i) for i in range(num_nodes)])))
    print("    held : boolean;")
    print("    epoch : {%s};" %(", ".join([str(i) for i in range(num_epochs)])))
    print()
    print()
    
    
def gen_module_main(num_nodes:int, num_epochs:int):
    print("MODULE main")
    gen_module_main_VAR(num_nodes, num_epochs)
    gen_module_main_DEF(num_nodes, num_epochs)
    gen_module_main_ASSIGN(num_nodes, num_epochs)
    gen_module_main_TRANS(num_nodes, num_epochs)
    gen_module_main_SPEC(num_nodes, num_epochs)
    

def gen_module_main_VAR(num_nodes:int, num_epochs:int):
    print("VAR")
    for i in range(num_nodes):
        print("    n%d : node;" %i)
    print("    transfer : array 0..%d of array 0..%d of boolean;" %(num_nodes-1, num_epochs-1))     # transfer: dst->epoch->bool
    print("    locked   : array 0..%d of array 0..%d of boolean;" %(num_nodes-1, num_epochs-1))     # locked: src->epoch->bool
    print()
    print("    -- non-deterministics")
    print("    action      : {grant, accept, stutter};")
    print("    actor       : {%s};" %(", ".join([str(i) for i in range(num_nodes)])))
    print("    grant_dst   : {%s};" %(", ".join([str(i) for i in range(num_nodes)])))
    print("    grant_ep    : {%s};" %(", ".join([str(i) for i in range(num_epochs)])))
    print("    accept_ep   : {%s};" %(", ".join([str(i) for i in range(num_epochs)])))
    print("FROZENVAR")
    print("    first_node  : {%s};" %(", ".join([str(i) for i in range(num_nodes)])))
    print("    first_epoch : {%s};" %(", ".join([str(i) for i in range(1, num_epochs)])))
    print()


def gen_module_main_DEF(num_nodes:int, num_epochs:int):
    print("DEFINE")
    # TypeOK invariant
    print("    TypeOK := %s;" %(" & ".join(["n%d.id = %d" %(i, i) for i in range(num_nodes)])))
    # Maintain constants across transition
    print("    constants_next := \n        %s;" %("\n        & ".join(["next(n%d.id) = n%d.id" %(i, i) for i in range(num_nodes)])))
    print()
    # Node stutter definitions
    for i in range(num_nodes):
        print("    n%d_stutter := \n        next(n%d.held) = n%d.held & next(n%d.epoch) = n%d.epoch;" %(i,i,i,i,i))
    print()
    # Distributed system stutter definition
    print(gen_stutter_step_str(num_nodes, num_epochs))
    print()
    # Grant step definition
    print(gen_grant_step_str(num_nodes, num_epochs))
    print()
    # Accept step definition
    print(gen_accept_step_str(num_nodes, num_epochs))
    print()
    
def gen_stutter_step_str(num_nodes:int, num_epochs:int):
    clauses = ["constants_next"]
    for i in range(num_nodes):
        clauses.append("n%d_stutter" %i)
    for i in range(num_nodes):
        for e in range(num_epochs):
            clauses.append("next(transfer[%d][%d]) = transfer[%d][%d]" %(i,e,i,e))
    for i in range(num_nodes):
        for e in range(num_epochs):
            clauses.append("next(locked[%d][%d]) = locked[%d][%d]" %(i,e,i,e))
    return "    stutter_step :=\n        %s;" %("\n        & ".join(clauses))

def gen_grant_step_str(num_nodes:int, num_epochs:int):
    clauses = ["constants_next", "action = grant"]
    # actor holds lock
    held_cases = []
    for i in range(num_nodes):
        held_cases.append("actor=%d:n%d.held;" %(i,i))
    clauses.append("case %s\n        esac" %("  ".join(held_cases)))
    # actor actions
    actor_cases = []
    for i in range(num_nodes):
        actor_cases.append("actor=%d :\n                %s;" %(i, gen_grant_step_actor_action_str(num_nodes, num_epochs, i)))
    actor_cases.append("TRUE:\n                stutter_step;")
    clauses.append("case \n            %s\n        esac" %("\n            ".join(actor_cases)))
    return "    grant_step :=\n        %s;" %("\n        & ".join(clauses))

def gen_grant_step_actor_action_str(num_nodes:int, num_epochs:int, curr:int):
    clauses = []
    # All other nodes stutter
    for i in range(num_nodes):
        if i != curr:
            clauses.append("n%d_stutter" %i)
    # curr node takes the transition
    clauses.append("grant_ep > n%d.epoch" %curr)
    clauses.append("next(n%d.held) = (n%d.epoch=%d ? TRUE : FALSE)" %(curr,curr,num_epochs-1))
    clauses.append("next(n%d.epoch) = n%d.epoch" %(curr,curr))
    # send appropriate transfer message
    for dst in range(num_nodes):
        for e in range(num_epochs):
            clauses.append("next(transfer[%d][%d]) = (grant_dst=%d & grant_ep=%d ? TRUE : transfer[%d][%d])" %(dst,e,dst,e,dst,e))
    # locked unchanged
    for i in range(num_nodes):
        for e in range(num_epochs):
            clauses.append("next(locked[%d][%d]) = locked[%d][%d]" %(i,e,i,e))
    return "\n                & ".join(clauses)


def gen_accept_step_str(num_nodes:int, num_epochs:int):
    clauses = ["constants_next", "action = accept"]
    # enabling conditions
    actor_cases = []
    for i in range(num_nodes):
        actor_i_clauses = []
        # actor_i_clauses.append("!n%d.held" %i)
        # actor_i_clauses.append("accept_ep > n%d.epoch" %i)
        actor_i_clauses.append("transfer[%d][accept_ep]" %i)
        actor_cases.append("actor=%d: \n                %s;" %(i,"\n                & ".join(actor_i_clauses)))
    clauses.append("case\n            %s\n        esac" %("\n            ".join(actor_cases)))
    # actor actions
    actor_cases = []
    for i in range(num_nodes):
        actor_cases.append("actor=%d & accept_ep > n%d.epoch:\n                %s;" %(i,i, gen_accept_step_actor_action_str(num_nodes, num_epochs, i)))
    actor_cases.append("TRUE:\n                stutter_step;")
    clauses.append("case \n            %s\n        esac" %("\n            ".join(actor_cases)))
    return "    accept_step :=\n        %s;" %("\n        & ".join(clauses))
        
def gen_accept_step_actor_action_str(num_nodes:int, num_epochs:int, curr:int):
    clauses = []
    # All other nodes stutter
    for i in range(num_nodes):
        if i != curr:
            clauses.append("n%d_stutter" %i)
    # curr node takes the transition
    clauses.append("next(n%d.held) = TRUE" %curr)
    clauses.append("next(n%d.epoch) = accept_ep" %curr)
    # transfer unchanged
    for i in range(num_nodes):
        for e in range(num_epochs):
            clauses.append("next(transfer[%d][%d]) = transfer[%d][%d]" %(i,e,i,e))
    # send appropriate locked message
    for i in range(num_nodes):
        for e in range(num_epochs):
            if i == curr:
                clauses.append("next(locked[%d][%d]) = (accept_ep=%d ? TRUE : locked[%d][%d])" %(i,e,e,i,e))
            else:
                clauses.append("next(locked[%d][%d]) = locked[%d][%d]" %(i,e,i,e))
    return "\n                & ".join(clauses)


def gen_module_main_ASSIGN(num_nodes:int, num_epochs:int):
    print("ASSIGN")
    # Initialize nodes
    for i in range(num_nodes):
        print("    init(n%d.id)     := %d;" %(i,i))
        print("    init(n%d.held)   := first_node = %d;" %(i,i))
        print("    init(n%d.epoch)  := first_node = %d ? first_epoch : 0;" %(i,i))
    # Empty network
    for i in range(num_nodes):
        for e in range(num_epochs):
            print("    init(transfer[%d][%d]) := FALSE;" %(i,e))
    for i in range(num_nodes):
        for e in range(num_epochs):
            print("    init(locked[%d][%d])   := FALSE;" %(i,e))
            
def gen_module_main_TRANS(num_nodes:int, num_epochs:int):
    print("TRANS")
    print("    case")
    print("        action=grant   : grant_step;")
    print("        action=accept  : accept_step;")
    print("        action=stutter : stutter_step;")
    print("    esac;")
    print()
    
def gen_module_main_SPEC(num_nodes:int, num_epochs:int):
    print("INVARSPEC TypeOK;")
    print("INVARSPEC \n    %s;" %(gen_safety_spec_str(num_nodes, num_epochs)))
    print("INVARSPEC \n    %s;" %(gen_i4safety_spec_str(num_nodes, num_epochs)))
    # print("INVARSPEC \n    first_node=0 -> n0.held;")
    
def gen_safety_spec_str(num_nodes:int, num_epochs:int):
    """ No two nodes hold the lock """
    clauses = []
    for i in range(num_nodes):
        for j in range(num_nodes):
            if j>i:
                clauses.append("!(n%d.held & n%d.held)" %(i,j))
    return "\n    & ".join(clauses)

def gen_i4safety_spec_str(num_nodes:int, num_epochs:int):
    """ No two locked message of same epoch belonging to different node """
    clauses = []
    for e in range(num_epochs):
        for i in range(num_nodes):
            for j in range(num_nodes):
                clauses.append("(locked[%d][%d] & locked[%d][%d] -> n%d.id = n%d.id)" %(i,e,j,e,i,j))
    return "\n    & ".join(clauses)
    

if __name__ == "__main__":
    # positional arguments <#nodes> <#epochs>
    if len(sys.argv) != 3:
        print("Error: Expect  <#nodes> <#epochs> as input")
        sys.exit(1)
    num_nodes, num_epochs = int(sys.argv[1]), int(sys.argv[2])
    main(num_nodes, num_epochs)
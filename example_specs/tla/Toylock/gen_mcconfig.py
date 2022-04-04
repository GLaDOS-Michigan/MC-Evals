import sys
from itertools import chain, combinations

def main(num_nodes, num_epochs):
    tla_str = gen_tla_file(num_nodes, num_epochs)
    cfg_str = gen_cfg_file(num_nodes, num_epochs)
    with open('MCToylock.tla', 'w') as f:
        f.write(tla_str)
    with open('MCToylock.cfg', 'w') as f:
        f.write(cfg_str)

def gen_tla_file(num_nodes, num_epochs):
    """ Returns the MCToylock.tla file contents as string """ 
    nodes = ["n%d" %i for i in range(num_nodes)]
    
    res = []
    res.append("------------------------------ MODULE MCToylock ------------------------------")
    res.append("EXTENDS Toylock, TLC")
    res.append("CONSTANTS %s" %(", ".join(nodes)))
    res.append("")
    res.append("MCNode == {" + ", ".join(nodes) + "}")
    res.append("MCEpoch == 0..%d" %(num_epochs-1))
    res.append("")
    res.append("\* SYMMETRY definition")
    # res.append("symmetries == Permutations(Node)")
    res.append("")
    res.append("=============================================================================")
    return "\n".join(res)

def gen_cfg_file(num_nodes, num_epochs):
    """ Returns the MCToylock.tla file contents as string """ 
    nodes = ["n%d" %i for i in range(num_nodes)]
    
    res = []
    res.append("SPECIFICATION Spec")
    res.append("CONSTANTS")
    res.append(" ".join(["%s=%s" %(a,a) for a in nodes]))
    res.append("  Node     <- MCNode")
    res.append("  Epoch    <- MCEpoch")
    res.append("")
    res.append("\* SYMMETRY definition")
    # res.append("SYMMETRY symmetries")
    res.append("")
    res.append("INVARIANTS TypeOK Safety SafetyI4")
    return "\n".join(res)

if __name__ == "__main__":
    # positional arguments <#nodes> <#epochs>
    if len(sys.argv) != 3:
        print("Error: Expect <#nodes> <#epochs> as input")
        sys.exit(1)
    num_nodes, num_epochs = int(sys.argv[1]), int(sys.argv[2])
    main(num_nodes, num_epochs)
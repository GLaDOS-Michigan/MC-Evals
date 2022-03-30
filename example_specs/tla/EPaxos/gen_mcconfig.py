import sys
from itertools import chain, combinations

def main(num_replicas, num_commands, num_bals):
    tla_str = gen_tla_file(num_replicas, num_commands, num_bals)
    cfg_str = gen_cfg_file(num_replicas, num_commands, num_bals)
    with open('MCEPaxos.tla', 'w') as f:
        f.write(tla_str)
    with open('MCEPaxos.cfg', 'w') as f:
        f.write(cfg_str)

def gen_tla_file(num_replicas, num_commands, num_bals):
    """ Returns the MCEPaxos.tla file contents as string """ 
    replicas = ["r%d" %i for i in range(num_replicas)]
    commands = ["c%d" %i for i in range(num_commands)]
    
    res = []
    res.append("------------------------------ MODULE MCEPaxos ------------------------------")
    res.append("EXTENDS EPaxos, TLC")
    res.append("CONSTANTS %s" %(", ".join(replicas)))
    res.append("CONSTANTS %s" %(", ".join(commands)))
    res.append("")
    res.append("MC_Replicas == {" + ", ".join(replicas) + "}")
    res.append("MC_Commands == {" + ", ".join(commands) + "}")
    res.append("MC_MaxBallot == %d" %(num_bals))
    res.append("MC_FastQuorums(x) == { s \in SUBSET Replicas: x \\in s /\ Cardinality(s) = (Cardinality(Replicas) \div 2) + ((Cardinality(Replicas) \div 2) + 1) \div 2}")
    res.append("MC_SlowQuorums(x) == { s \in SUBSET Replicas: x \\in s /\ Cardinality(s) = (Cardinality(Replicas) \div 2) + 1}")
    res.append("n ==  CHOOSE c : c \\notin MC_Commands")
    res.append("")
    res.append("\* SYMMETRY definition")
    if num_commands > 1:
        res.append("symmetries == Permutations(MC_Replicas) \\union Permutations(MC_Commands)")
    else:
        res.append("symmetries == Permutations(MC_Replicas)")
    res.append("")
    res.append("=============================================================================")
    return "\n".join(res)

def gen_cfg_file(num_replicas, num_commands, num_bals):
    """ Returns the MCEPaxos.tla file contents as string """ 
    replicas = ["r%d" %i for i in range(num_replicas)]
    commands = ["c%d" %i for i in range(num_commands)]
    
    res = []
    res.append("SPECIFICATION Spec")
    res.append("CONSTANTS")
    res.append("  n=n "+ " ".join(["%s=%s" %(a,a) for a in replicas]) + " " + " ".join(["%s=%s" %(v,v) for v in commands]))
    res.append("  MaxBallot     <- MC_MaxBallot")
    res.append("  Replicas      <- MC_Replicas")
    res.append("  Commands      <- MC_Commands")
    res.append("  FastQuorums   <- MC_FastQuorums")
    res.append("  SlowQuorums   <- MC_SlowQuorums")
    res.append("  none          <- n")
    res.append("")
    res.append("\* SYMMETRY definition")
    res.append("SYMMETRY symmetries")
    res.append("PROPERTIES typeok Nontriviality Stability Consistency")
    return "\n".join(res)

if __name__ == "__main__":
    # positional arguments <#replicas> <#commands> <#ballots>
    if len(sys.argv) < 4:
        print("Error: Expect <#replicas> <#commands> <#ballots> as input")
        sys.exit(1)
    num_replicas, num_commands, num_bals = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    main(num_replicas, num_commands, num_bals)
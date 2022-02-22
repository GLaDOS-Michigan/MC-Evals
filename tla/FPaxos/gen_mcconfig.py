import sys
from itertools import chain, combinations

def main(num_accs, num_vals, num_bals, q1_size):
    tla_str = gen_tla_file(num_accs, num_vals, num_bals, q1_size)
    cfg_str = gen_cfg_file(num_accs, num_vals, num_bals, q1_size)
    with open('MCFPaxos.tla', 'w') as f:
        f.write(tla_str)
    with open('MCFPaxos.cfg', 'w') as f:
        f.write(cfg_str)

def gen_quorum(acceptors, qrm_size):
    """ Using members of acceptors, generate all quorums at least as large as qrm_size """
    assert len(acceptors) >= qrm_size
    powset = powerset(acceptors)
    res = [x for x in powset if len(x) >= qrm_size]
    return res

def gen_tla_file(num_accs, num_vals, num_bals, q1_size):
    """ Returns the MCFPaxos.tla file contents as string """ 
    acceptors = ["a%d" %i for i in range(num_accs)]
    values = ["v%d" %i for i in range(num_vals)]
    q1_quorums = gen_quorum(acceptors, q1_size)
    q2_quorums = gen_quorum(acceptors, len(acceptors)-q1_size+1)
    
    res = []
    res.append("------------------------------ MODULE MCFPaxos ------------------------------")
    res.append("EXTENDS FPaxos, TLC")
    res.append("CONSTANTS %s" %(", ".join(acceptors)))
    res.append("CONSTANTS %s" %(", ".join(values)))
    res.append("")
    res.append("MCAcceptor == {" + ", ".join(acceptors) + "}")
    res.append("MCValue == {" + ", ".join(values) + "}")
    res.append("MCQuorum1 == {" + ", ".join(["{"+",".join(x)+"}" for x in q1_quorums]) + "}")
    res.append("MCQuorum2 == {" + ", ".join(["{"+",".join(x)+"}" for x in q2_quorums]) + "}")
    res.append("MCBallot == 0..%d" %(num_bals-1))
    res.append("")
    res.append("\* SYMMETRY definition")
    res.append("symmetries == Permutations(MCAcceptor) \\union Permutations(MCValue)")
    res.append("")
    res.append("=============================================================================")
    return "\n".join(res)

def gen_cfg_file(num_accs, num_vals, num_bals, q1_size):
    """ Returns the MCFPaxos.tla file contents as string """ 
    acceptors = ["a%d" %i for i in range(num_accs)]
    values = ["v%d" %i for i in range(num_vals)]
    
    res = []
    res.append("SPECIFICATION Spec")
    res.append("CONSTANTS")
    res.append("  "+ " ".join(["%s=%s" %(a,a) for a in acceptors]) + " " + " ".join(["%s=%s" %(v,v) for v in values]))
    res.append("  Acceptor  <- MCAcceptor")
    res.append("  Value     <- MCValue")
    res.append("  Quorum1   <- MCQuorum1")
    res.append("  Quorum2   <- MCQuorum2")
    res.append("  Ballot    <- MCBallot")
    res.append("  None      =  None")
    res.append("")
    res.append("\* SYMMETRY definition")
    res.append("SYMMETRY symmetries")
    res.append("")
    res.append("INVARIANT SafeValue TypeOK")
    return "\n".join(res)

def powerset(iterable):
    """ powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3) """
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


if __name__ == "__main__":
    # positional arguments <#acceptors> <#values> <#ballots> <q1 size>
    if len(sys.argv) < 5:
        print("Error: Expect <#acceptors> <#values> <#ballots> <q1 size> as input")
        sys.exit(1)
    num_accs, num_vals, num_bals, q1_size = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    main(num_accs, num_vals, num_bals, q1_size)
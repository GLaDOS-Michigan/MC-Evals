#!/bin/bash

# echo "================================================================"
# echo "> Let's install some dependencies (distutils, tcl, xdot)"
# read -p "> press enter to continue?" userInput
# sudo apt-get install python3-distutils tcl8.6-dev xdot
# echo "> Done with dependencies"
# read -p "> press enter to continue?" userInput

# wget https://gitlab.eecs.umich.edu/amangoel/paper3/-/archive/master/paper3-master.zip

YICES="../../deps/yices_smt2 --incremental"
MATHSAT="../../deps/mathsat"
Z3="../../deps/z3"
BTORSIM="../../deps/btorsim"

# if z3 or yices installed using build.sh, uncomment the following lines
# YICES="yices-smt2 --incremental"
# Z3="z3"

echo "================================================================"
echo "> Let's run avr on the first case study cs1 (using VMT frontend)"
echo "> Experiment 1: apache-escape-absolute (with machine integers first i.e. 32-bit variables using bit-vector theory)"
echo "> check the C file inputs/cs1/c/apache-escape-absolute.c for understanding the problem"
echo "> [evaluates: case study 1.1 (using BV), VMT frontend, proof certificates, verifying certificates using yices2]"
read -p "> press enter to continue?" userInput
python3 avr.py -n apache_escape_absolute_bv inputs/cs1/bv/apache-escape-absolute_bv.vmt
echo "> [avr should say h i.e. safe (all output logs and files in output/work_apache_escape_bv)]"
echo

echo "> Let's check the proof certificate printed by avr for the last run using yices2 smt solver"
echo "> proof certificate is output/work_apache_escape_absolute_bv/proof.smt2"
read -p "> press enter to continue?" userInput
cd output/work_apache_escape_absolute_bv
echo "> calling yices2"
$YICES proof.smt2
cd ../..
echo "> [should report all three smt checks as unsat]"
read -p "> press enter to continue?" userInput
echo

echo "> Experiment 2: Now let's repeat the same (run apache-escape-absolute) with software integers i.e. unbounded variables using linear-integer-arithmetic theory"
echo "> [evaluates: case study 1.1 (using LIA), VMT frontend, proof certificates, verifying certificates using z3]"
read -p "> press enter to continue?" userInput
python3 avr.py -n apache_escape_absolute_lia inputs/cs1/lia/apache-escape-absolute_lia.vmt
echo "> [avr should say h i.e. safe (all output logs and files in output/work_apache_escape_absolute_lia)]"
echo

echo "> Let's check the proof certificate printed by avr for the last run using z3 smt solver"
echo "> Note: z3 may report minor warnings"
echo "> proof certificate is output/work_apache_escape_absolute_lia/proof.smt2"
read -p "> press enter to continue?" userInput
cd output/work_apache_escape_absolute_lia
echo "> calling z3"
$Z3 proof.smt2
cd ../..
echo "> [should report all three smt checks as unsat]"
echo "> Done with apache-escape-absolute"
read -p "> press enter to continue?" userInput
echo


echo "> Experiment 3: apache-get-tag (with machine integers first i.e. 32-bit variables using bit-vector theory)"
echo "> check the C file inputs/cs1/c/apache-get-tag.c for understanding the problem"
echo "> [evaluates: case study 1.2 (using BV), VMT frontend, proof certificates, verifying certificates using yices2]"
read -p "> press enter to continue?" userInput
python3 avr.py -n apache_get_tag_bv inputs/cs1/bv/apache-get-tag_bv.vmt
echo "> [avr should say h i.e. safe (all output logs and files in output/work_apache_get_tag_bv)]"
echo

echo "> Let's check the proof certificate printed by avr for the last run using yices2 smt solver"
echo "> proof certificate is output/work_apache_get_tag_bv/proof.smt2"
read -p "> press enter to continue?" userInput
cd output/work_apache_get_tag_bv
echo "> calling yices2"
$YICES proof.smt2
cd ../..
echo "> [should report all three smt checks as unsat]"
read -p "> press enter to continue?" userInput
echo

echo "> Experiment 4: Now let's repeat the same (run apache-get-tag) with software integers i.e. unbounded variables using linear-integer-arithmetic theory"
echo "> [evaluates: case study 1.2 (using LIA), VMT frontend, proof certificates, verifying certificates using mathsat]"
read -p "> press enter to continue?" userInput
python3 avr.py -n apache_get_tag_lia inputs/cs1/lia/apache-get-tag_lia.vmt
echo "> [avr should say h i.e. safe (all output logs and files in output/work_apache_get_tag_lia)]"
echo

echo "> Let's check the proof certificate printed by avr for the last run using mathsat smt solver"
echo "> proof certificate is output/work_apache_get_tag_lia/proof.smt2"
read -p "> press enter to continue?" userInput
cd output/work_apache_get_tag_lia
echo "> calling mathsat"
$MATHSAT proof.smt2
cd ../..
echo "> [should report all three smt checks as unsat]"
echo "> Done with apache-get-tag"
echo

echo "> Done with first case study (cs1)"
read -p "> press enter to continue?" userInput
echo


echo "================================================================"
echo "> Let's run avr on the second case study cs2 (using BTOR2 frontend)"
echo "> needham key authentication protocol"
echo "> check the description file inputs/cs2/description.xml for understanding the problem"
echo "> Experiment 5: needham_2A_2B (with 2 initiators and responders each)"
echo "> [evaluates: case study 2, BTOR2 frontend, counterexample traces, verifying certificates using BtorSIM]"
read -p "> press enter to continue?" userInput
python3 avr.py -n needham_2A_2B inputs/cs2/btor2/needham_2A_2B.btor2
echo "> [avr should say v i.e. reachable (all output logs and files in output/work_needham_2A_2B)]"
echo

echo "> Let's simulate the counterexample witness printed by avr for the last run using BtorSIM simulator"
echo "> counterexample witness is output/work_needham_2A_2B/cex.witness"
read -p "> press enter to continue?" userInput
cd output/work_needham_2A_2B
echo "> calling BtorSIM"
$BTORSIM needham_2A_2B.btor2 cex.witness -v --states
cd ../..
echo "> [should reach the bad state property in 6 steps]"
read -p "> press enter to continue?" userInput
echo

echo "> Now let's repeat the same (with 3 initiators and responders each)"
echo "> Experiment 6: needham_3A_3B (with 3 initiators and responders each)"
echo "> [evaluates: case study 2, BTOR2 frontend, counterexample traces, verifying certificates using BtorSIM]"
read -p "> press enter to continue?" userInput
python3 avr.py -n needham_3A_3B inputs/cs2/btor2/needham_3A_3B.btor2
echo "> [avr should say v i.e. reachable (all output logs and files in output/work_needham_3A_3B)]"
echo

echo "> Let's simulate the counterexample witness printed by avr for the last run using BtorSIM simulator"
echo "> counterexample witness is output/work_needham_3A_3B/cex.witness"
read -p "> press enter to continue?" userInput
cd output/work_needham_3A_3B
echo "> calling BtorSIM"
$BTORSIM needham_3A_3B.btor2 cex.witness -v --states
cd ../..
echo "> [should reach the bad state property in 6 steps]"
echo "> Done with needham protocol"
read -p "> press enter to continue?" userInput
echo

echo "> Done with second case study (cs2)"
read -p "> press enter to continue?" userInput
echo


echo "================================================================"
echo "> Let's run avr on a problem derived from verification of distributed protocols (using VMT frontend)"
echo "> Experiment 7: Lock_server protocol (with 2 clients and 1 server)"
echo "> check the ivy file inputs/distributed/lock_server/lock_server.ivy for understanding the protocol"
echo "> [evaluates: verifying distributed protocols, proof certificates]"
read -p "> press enter to continue?" userInput
python3 avr.py -n lock_server inputs/distributed/lock_server/lock_server.vmt
echo "> [avr should say h i.e. safe (all output logs and files in output/work_lock_server)]"
echo

echo "> Let's check the proof certificate printed by avr for the last run using yices2 smt solver"
echo "> proof certificate is output/work_lock_server/proof.smt2"
read -p "> press enter to continue?" userInput
cd output/work_lock_server
echo "> calling yices2"
$YICES proof.smt2
cd ../..
echo "> [should report all three smt checks as unsat]"
echo "================================================================"
read -p "> press enter to continue?" userInput
echo


echo "> Now let's run avr on a more complicated distributed protocol (using VMT frontend)"
echo "> Experiment 8: Learning switch (with 6 nodes)"
echo "> check the ivy file inputs/distributed/learning_switch/learning_switch.ivy for understanding the protocol"
echo "> [evaluates: verifying distributed protocols, proof certificates]"
read -p "> press enter to continue?" userInput
python3 avr.py -n learning_switch inputs/distributed/learning_switch/learning_switch.vmt
echo "> [avr should say h i.e. safe (all output logs and files in output/work_learning_switch)]"
echo

echo "> Let's check the proof certificate printed by avr for the last run using mathsat smt solver"
echo "> proof certificate is output/work_learning_switch/proof.smt2"
read -p "> press enter to continue?" userInput
cd output/work_learning_switch
echo "> calling mathsat"
$MATHSAT proof.smt2
cd ../..
echo "> [should report all three smt checks as unsat]"
echo "================================================================"
read -p "> press enter to continue?" userInput
echo


echo "> Let's run avr on a hardware verilog design (using Verilog frontend)"
echo "> Experiment 9: Model of a heap"
echo "> check the verilog file inputs/misc/verilog/heap.v for understanding the design"
echo "> Let's also use a timeout of a few minutes"
echo "> [evaluates: Verilog frontend]"
read -p "> press enter to continue?" userInput
python3 avr.py -n heap inputs/misc/verilog/heap.v --timeout 100
echo "> [avr should say f_* i.e. timeout failure (all output logs and files in output/work_heap)]"
echo

echo "> avr by default is using a config. ic3+sa+uf i.e. IC3+SA algorithm with uninterpreted functions (to focus on control-centric properties)"
echo "> This problem is too data centric (may take around 1000 seconds to solve using default config.)"
echo "> Experiment 10: So let's use avr's Proof Race script (avr_pr.py) to exploit multiprocessing over multiple cores to speed up verification"
echo "> Again use a timeout of a few minutes"
echo "> [evaluates: Verilog frontend, proof race, different techniques and add-ons]"
read -p "> press enter to continue?" userInput
python3 avr_pr.py -n heap inputs/misc/verilog/heap.v --timeout 100
echo "> [proof race should say safe (all output logs and files in output/pr_heap)]"
echo "> We can use proof race to identify which config. performed the best"
echo "> It should probably be \"python3 avr.py --abstract sa8 --level 5 --granularity 3 --interpol 1\" in the previous run"
echo "> which means run avr with:"
echo "  --- uninterpret operations beyond bit-width of 8 (sa8)"
echo "  --- allow fine syntax relations (fineness level 5)"
echo "  --- allow input variables in ic3 clause learning (granularity 3)"
echo "  --- and use interpolation"
echo

echo "> Let's check the proof certificate printed by avr for the last run using yices2 smt solver"
echo "> proof certificate is output/pr_heap/proof.smt2"
read -p "> press enter to continue?" userInput
cd output/pr_heap
echo "> calling yices2"
$YICES proof.smt2
cd ../..
echo "> [should report all three smt checks as unsat]"
echo "================================================================"
read -p "> press enter to continue?" userInput
echo


echo "> Let's run avr's proof race on an industrial hardware design (using Verilog frontend)"
echo "> Experiment 11: picoJava-II Core Instruction Cache Data RAM"
echo "> check the verilog file inputs/misc/verilog/picojava_icram.v for reference"
echo "> [evaluates: Verilog frontend, proof race, different techniques and add-ons]"
read -p "> press enter to continue?" userInput
python3 avr_pr.py -n picojava_icram inputs/misc/verilog/picojava_icram.v
echo "> [proof race should say safe (all output logs and files in output/pr_picojava_icram)]"
echo

echo "> Let's check the proof certificate printed by avr for the last run using yices2 smt solver"
echo "> proof certificate is output/pr_picojava_icram/proof.smt2"
read -p "> press enter to continue?" userInput
cd output/pr_picojava_icram
echo "> calling yices2"
$YICES proof.smt2
cd ../..
echo "> [should report all three smt checks as unsat]"
echo "================================================================"
read -p "> press enter to continue?" userInput
echo


echo "> Finally, let's explore few more utilities offered by avr for the user"
echo "> Experiment 12: Let's run avr on a simple verilog example"
echo "> swap_counter"
echo "> check the verilog file inputs/misc/verilog/swap_counter.v for reference"
echo "> [evaluates: utilities, design in .smt2, statistics, dot visualizations]"
read -p "> press enter to continue?" userInput
python3 avr.py -n swap_counter inputs/misc/verilog/swap_counter.v --dot "1111111"
echo "> [avr should say safe (all output logs and files in output/work_swap_counter)]"
echo

echo "> check the .smt2 version of the design in output/work_swap_counter/design.smt2 (printed by avr)"
read -p "> press enter to continue?" userInput

echo "> check the statistics file output/work_swap_counter/swap_counter.results for useful design statistics (printed by avr)"
echo "> for example,"
echo "> - the total number of state variable bits is: "
grep -w "i-total-state-bits:" output/work_swap_counter/swap_counter.results
read -p "> press enter to continue?" userInput
echo "> - the number of SMT calls made by avr is: "
grep -w "scalls:" output/work_swap_counter/swap_counter.results
read -p "> press enter to continue?" userInput
echo

echo "> check the graphical visualizations printed by avr in folder output/work_swap_counter/dot/"
echo "> for example,"
echo "> - the property cone looks like: "
read -p "> press enter to continue?" userInput
xdot output/work_swap_counter/dot/property.dot
echo "> - avr learns an axiom saying: not (Y > X and Y = 0)"
read -p "> press enter to continue?" userInput
xdot output/work_swap_counter/dot/ref/0_*.dot
read -p "> press enter to continue?" userInput
echo

echo "> Let's check the proof certificate printed by avr for the last run using yices2 smt solver"
echo "> proof certificate is output/work_swap_counter/proof.smt2"
read -p "> press enter to continue?" userInput
cd output/work_swap_counter
echo "> calling yices2"
$YICES proof.smt2
cd ../..
echo "> [should report all three smt checks as unsat]"

echo "================================================================"
read -p "> press enter to continue?" userInput
echo


echo "==================="
echo "Evaluation complete"
echo "==================="
text="
Evaluated:
\n    - All frontends (VMT, BTOR2 and Verilog)
\n    - Proof certificates (checked using yices2, mathsat, z3)
\n    - Counterexample witnesses (simulated using BtorSIM)
\n    - Case studies (apache buffer overflow, public key auth. protocol, distributed protocols)
\n    - Verifying distributed protocols (lock_server, learning switch)
\n    - Verifying hardware designs (heap, picoJava core)
\n    - Proof race (with different underlying options)
\n    - Utilities (dot visualization, statistics, design in .smt2 format)
"
echo -e $text
echo "================================================================"
echo "Hope you enjoyed this work!"


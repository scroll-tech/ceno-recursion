# CoBBl: SNARK over Basic Blocks

CoBBl is a full-stack SNARK system that divides a computation into blocks and verify their correctness in parallel. CoBBl is divided into two components:

#### CirC Blocks
A front-end SNARK compiler based on CirC that divides a program into blocks and generates all constraints related to verification.

#### Spartan Parallel
A modified Spartan proof system that supports data-parallelism and additional properties.

## Running the program
* First set up all compilers: `bash setup.sh`
* Next run the proof system on all benchmarks: `python3 tester.py`
* Finally generate the result: `python3 plotter.py > output`

## Output Format
A sample output can be viewed in `./output`

Current output format is consisted of a 6 x 4 table, corresponding to 4 matrices on 6 proofs 

#### Proofs
* `Baseline`: modified CirC compiler + unmodified Spartan
* `CoBBl For`: CoBBl proof on the exact same code as baseline (no while loops)
* `CoBBl 100`: Program with while loops with number of iterations = upper bound
* `CoBBl 90`: Program with while loops with number of iterations = 0.9 x upper bound
* `CoBBl 75`: Program with while loops with number of iterations = 0.75 x upper bound
* `CoBBl 50`: Program with while loops with number of iterations = 0.50 x upper bound

#### Matrices
* `Compiler`: time to convert the code into constraints
* `Preprocess`: time of one-time setup, mostly instance commitment
* `Prover`: prover setup time from witnesses to proof generation, excluding actual program execution
* `Verifier`: verification time, includes every computation performed by the verifier
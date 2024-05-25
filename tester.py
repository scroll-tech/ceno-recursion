import os

REPEAT = 5

# Convert a .raw file to a sequence of .zok & .input files and test them
def preprocess(b_name):
    global REPEAT

    f = open(f"zok_tests/raw/{b_name}.raw", 'r')
    line = f.readline().strip()

    # Read constants
    constants = {}
    while line != "INPUT:":
        line = f.readline().strip()

        components = line.split(' ')
        if len(components) == 2:
            constants[components[0]] = int(components[1])

    # Read inputs
    inputs = {}
    while line != "PROGRAM:":
        line = f.readline().strip()

        components = line.split(' ')
        if len(components) == 2:
            inputs[components[0]] = int(components[1])

    # Read program
    baseline = lambda x : ""
    cobbl = lambda x : ""
    # MODE: 0 - BASELINE; 1 - COBBL; 2 - BOTH
    mode = 2
    baseline_func_list = []
    cobbl_func_list = []
    line_segs_list = []
    while line:
        line = f.readline()
        stripped_line = line.strip()
        if stripped_line == "// BASELINE":
            mode = 0
        elif stripped_line == "// COBBL":
            mode = 1
        elif stripped_line == "// END_SPLIT":
            mode = 2
        elif line:
            # convert line as a lambda notation of CONSTANTS
            # line_segs_raw: [code, const_name}code, const_name}code, ...]
            line_segs_raw = line.split('{')
            # line_segs: [code, const_name, code, const_name, code, ...]
            line_segs = [line_segs_raw[0]]; [line_segs := line_segs + x for x in [y.split('}') for y in line_segs_raw[1:]]]
            line_segs_list.append(line_segs[:])
            # line_func: const_map -> "code const_val code const_val code"
            line_func = lambda k, x : "".join([line_segs_list[k][i] if i % 2 == 0 else str(x[line_segs_list[k][i]]) for i in range(len(line_segs_list[k]))])

            if mode in [0, 2]:
                baseline_func_list.append((line_func, len(line_segs_list) - 1))
            if mode in [1, 2]:
                cobbl_func_list.append((line_func, len(line_segs_list) - 1))
    
    baseline = lambda x : "".join([func(i, x) for (func, i) in baseline_func_list])
    cobbl = lambda x : "".join([func(i, x) for (func, i) in cobbl_func_list])
    f.close()
    
    # Process programs for each constant
    for _ in range(REPEAT):
        # Produce code
        with open(f"zok_tests/benchmarks/{b_name}.zok", "w") as f_baseline:
            f_baseline.write(baseline(constants))
        with open(f"zok_tests/benchmarks/{b_name}_cobbl.zok", "w") as f_cobbl:
            f_cobbl.write(cobbl(constants))

        # Produce variables
        pass

        for var in constants:
            constants[var] *= 2
        break

def execute_baseline(b_name):
    print("\n--\nBASELINE")
    os.system(f"cd circ_baseline && target/release/examples/circ --language zsharp {b_name} r1cs | \
                sed -n -e 's/Compiler time: //p' \
                    -e 's/  \* SNARK::encode //p' \
                    -e 's/  \* SNARK::prove //p' \
                    -e 's/  \* SNARK::verify //p'")

def execute_cobbl(b_name):
    print("\n--\nCOBBL - FOR")
    os.system(f"cd circ_blocks && target/release/examples/zxc {b_name} | \
            sed -n 's/Compiler time: //p'")
    os.system(f"cd spartan_parallel && RUST_BACKTRACE=1 target/release/examples/interface {b_name} | \
                sed -n -e 's/Preprocess time: //p' \
                    -e 's/  \* SNARK::prove //p' \
                    -e 's/  \* SNARK::verify //p'")
    
    b_name += "_cobbl"
    print("\n--\nCOBBL - WHILE")
    os.system(f"cd circ_blocks && target/release/examples/zxc {b_name} | \
            sed -n 's/Compiler time: //p'")
    os.system(f"cd spartan_parallel && RUST_BACKTRACE=1 target/release/examples/interface {b_name} | \
                sed -n -e 's/Preprocess time: //p' \
                    -e 's/  \* SNARK::prove //p' \
                    -e 's/  \* SNARK::verify //p'")

BENCHMARK = "find_min"
preprocess(BENCHMARK)
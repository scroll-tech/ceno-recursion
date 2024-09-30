import os

REPEAT = 5
TIMEOUT = 3000

# Process A * B or A + B or A - B by reading A & B from consts
def process_formula(consts, formula):
    form_segs = formula.split(' ')
    # form_segs is [const, op, const, op, const, ...]
    lhs = form_segs[0]
    try:
        lhs = int(lhs)
    except:
        lhs = consts[lhs]
    for i in range(1, len(form_segs), 2):
        rhs = form_segs[i + 1]
        try:
            rhs = int(rhs)
        except:
            rhs = consts[rhs]
        match form_segs[i]:
            case "+":
                lhs = lhs + rhs
            case "-":
                lhs = lhs - rhs
            case "*":
                lhs = lhs * rhs
    return lhs

# Convert a .raw file to a sequence of .zok & .input files and test them
def preprocess(b_name):
    global CONST_EXPAND
    global REPEAT

    f = open(f"zok_tests/raw/{b_name}.raw", 'r')
    line = f.readline().strip()

    # Read constants
    constants = {}
    const_expand = 0
    while line != "INPUT:":
        line = f.readline().strip()

        components = line.split(' ')
        if len(components) >= 2:
            constants[components[0]] = []
            if const_expand == 0:
                const_expand = len(components) - 1
            else:
                # Assert all constants have the same length
                assert(const_expand == len(components) - 1)
            for i in range(1, len(components)):
                constants[components[0]].append(int(components[i]))

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
            line_func = lambda k, x : "".join([line_segs_list[k][i] if i % 2 == 0 else str(process_formula(x, line_segs_list[k][i])) for i in range(len(line_segs_list[k]))])

            if mode in [0, 2]:
                baseline_func_list.append((line_func, len(line_segs_list) - 1))
            if mode in [1, 2]:
                cobbl_func_list.append((line_func, len(line_segs_list) - 1))
    
    baseline = lambda x : "".join([func(i, x) for (func, i) in baseline_func_list])
    cobbl = lambda x : "".join([func(i, x) for (func, i) in cobbl_func_list])
    f.close()
    
    f_result_name = f"zok_tests/raw/{b_name}_result.raw"
    os.system(f"echo \"{b_name} {const_expand} {REPEAT}\" > {f_result_name}")
    # Process programs for each constant value
    for i in range(const_expand):
        cur_const = {}
        for k in constants:
            cur_const[k] = constants[k][i]

        const_list = "; ".join([str(k) + " " + str(cur_const[k]) for k in cur_const])
        print(f"\n---\nCONSTANTS: {const_list}")
        os.system(f"echo \"{const_list}\" >> {f_result_name}")

        # Produce code
        with open(f"zok_tests/benchmarks/benchmarks/{b_name}.zok", "w") as f_baseline:
            f_baseline.write(baseline(cur_const))
        with open(f"zok_tests/benchmarks/benchmarks/{b_name}_cobbl.zok", "w") as f_cobbl:
            f_cobbl.write(cobbl(cur_const))

        for _ in range(REPEAT):
            # Produce variables. Each constant is of form max_XX, where XX is a variable
            # v = c
            print("\nTesting V = C...")
            for c in cur_const:
                v = c[4:]
                inputs[v] = cur_const[c]
            with open(f"zok_tests/benchmarks/benchmarks/{b_name}.input", "w") as f_input:
                f_input.writelines([f"{var} {inputs[var]}\n" for var in inputs])
                f_input.write("END")
            with open(f"zok_tests/benchmarks/benchmarks/{b_name}_cobbl.input", "w") as f_input:
                f_input.writelines([f"{var} {inputs[var]}\n" for var in inputs])
                f_input.write("END")

            # Default multicore to compare with CirC
            execute_baseline(b_name, f_result_name)
            execute_cobbl_for(b_name, f_result_name)
            # Disable multicore to compare with Jolt
            os.system(f"cd spartan_parallel && RUSTFLAGS=\"-C target_cpu=native\" cargo build --release --features profile --example interface 2> /dev/null")
            execute_cobbl_while(b_name, f_result_name, 100)
            execute_cobbl_no_opt(b_name, f_result_name, 100)

            # Enable multicore again to compare with CirC
            os.system(f"cd spartan_parallel && RUSTFLAGS=\"-C target_cpu=native\" cargo build --release --features multicore,profile --example interface 2> /dev/null")
            # v = 75% c
            print("\nTesting V = 75% C...")
            for c in cur_const:
                v = c[4:]
                inputs[v] = cur_const[c] * 3 // 4
            with open(f"zok_tests/benchmarks/benchmarks/{b_name}_cobbl.input", "w") as f_input:
                f_input.writelines([f"{var} {inputs[var]}\n" for var in inputs])
                f_input.write("END")
            execute_cobbl_while(b_name, f_result_name, 75)

            # v = 50% c
            print("\nTesting V = 50% C...")
            for c in cur_const:
                v = c[4:]
                inputs[v] = cur_const[c] // 2
            with open(f"zok_tests/benchmarks/benchmarks/{b_name}_cobbl.input", "w") as f_input:
                f_input.writelines([f"{var} {inputs[var]}\n" for var in inputs])
                f_input.write("END")
            execute_cobbl_while(b_name, f_result_name, 50)

def execute_baseline(b_name, f_name):
    print("BASELINE")
    os.system(f"echo 'BASELINE' >> {f_name}")
    os.system(f"timeout {TIMEOUT} bash -c \"cd circ_baseline && target/release/examples/circ --language zsharp benchmarks/{b_name} r1cs | \
                sed -n -e 's/Compiler time: //p' \
                    -e 's/Final R1cs size: //p' \
                    -e 's/  \* number_of_variables //p' \
                    -e 's/  \* number_non-zero_entries_A //p' \
                    -e 's/  \* number_non-zero_entries_B //p' \
                    -e 's/  \* number_non-zero_entries_C //p' \
                    -e 's/  \* SNARK::encode //p' \
                    -e 's/  \* SNARK::prove //p' \
                    -e 's/  \* SNARK::verify //p' \
                    -e 's/Total Proof Size: //p' \
                >> ../{f_name}\"")

def execute_cobbl_for(b_name, f_name):
    print("COBBL - FOR")
    os.system(f"echo 'COBBL_FOR' >> {f_name}")
    os.system(f"timeout {TIMEOUT} bash -c \"cd circ_blocks && target/release/examples/zxc benchmarks/{b_name} | \
            sed -n 's/Compiler time: //p' \
                >> ../{f_name}\"")
    os.system(f"timeout {TIMEOUT} bash -c \"cd spartan_parallel && RUST_BACKTRACE=1 target/release/examples/interface benchmarks/{b_name} | \
                sed -n -e 's/Preprocess time: //p' \
                    -e 's/Total Num of Blocks: //p' \
                    -e 's/Total Inst Commit Size: //p' \
                    -e 's/Total Var Commit Size: //p' \
                    -e 's/Total Cons Exec Size: //p' \
                    -e 's/  \* SNARK::prove //p' \
                    -e 's/  \* SNARK::verify //p' \
                    -e 's/Total Proof Size: //p' \
                >> ../{f_name}\"")

def execute_cobbl_while(b_name, f_name, perc):
    b_name += "_cobbl"
    print("COBBL - WHILE")
    os.system(f"echo 'COBBL_WHILE {perc}' >> {f_name}")
    os.system(f"timeout {TIMEOUT} bash -c \"cd circ_blocks && target/release/examples/zxc benchmarks/{b_name} | \
            sed -n 's/Compiler time: //p' \
                >> ../{f_name}\"")
    os.system(f"timeout {TIMEOUT} bash -c \"cd spartan_parallel && RUST_BACKTRACE=1 target/release/examples/interface benchmarks/{b_name} | \
                sed -n -e 's/Preprocess time: //p' \
                    -e 's/Total Num of Blocks: //p' \
                    -e 's/Total Inst Commit Size: //p' \
                    -e 's/Total Var Commit Size: //p' \
                    -e 's/Total Cons Exec Size: //p' \
                    -e 's/  \* SNARK::prove //p' \
                    -e 's/  \* SNARK::verify //p' \
                    -e 's/Total Proof Size: //p' \
                >> ../{f_name}\"")

def execute_cobbl_no_opt(b_name, f_name, perc):
    b_name += "_cobbl"
    print("COBBL - NO_OPT")
    os.system(f"echo 'COBBL_NO_OPT {perc}' >> {f_name}")
    os.system(f"timeout {TIMEOUT} bash -c \"cd circ_blocks && target/release/examples/zxc --no_opt benchmarks/{b_name} | \
            sed -n 's/Compiler time: //p' \
                >> ../{f_name}\"")
    os.system(f"timeout {TIMEOUT} bash -c \"cd spartan_parallel && RUST_BACKTRACE=1 target/release/examples/interface benchmarks/{b_name} | \
                sed -n -e 's/Preprocess time: //p' \
                    -e 's/Total Num of Blocks: //p' \
                    -e 's/Total Inst Commit Size: //p' \
                    -e 's/Total Var Commit Size: //p' \
                    -e 's/Total Cons Exec Size: //p' \
                    -e 's/  \* SNARK::prove //p' \
                    -e 's/  \* SNARK::verify //p' \
                    -e 's/Total Proof Size: //p' \
                >> ../{f_name}\"")

# BENCHMARK = ["find_min", "mat_mult", "kmp_search", "dna_align", "rle_codec", "sha256", "poseidon"]
# BENCHMARK = ["find_min_ff", "mat_mult_ff"]
BENCHMARK = ["find_min", "dna_align", "poseidon"]
os.system(f"./setup.sh 2> /dev/null")
for b in BENCHMARK:
    preprocess(b)
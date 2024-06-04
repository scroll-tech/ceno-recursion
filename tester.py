import os

CONST_EXPAND = 3
REPEAT = 5

# Process A * B or A + B or A - B by reading A & B from consts
def process_formula(consts, formula):
    form_segs = formula.split(' ')
    if len(form_segs) == 1:
        return consts[form_segs[0]]
    assert(len(form_segs) <= 3)
    lhs = consts[form_segs[0]]
    rhs = consts[form_segs[2]]
    match form_segs[1]:
        case "+":
            return lhs + rhs
        case "-":
            return lhs - rhs
        case "*":
            return lhs * rhs

# Convert a .raw file to a sequence of .zok & .input files and test them
def preprocess(b_name):
    global CONST_EXPAND
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
            line_func = lambda k, x : "".join([line_segs_list[k][i] if i % 2 == 0 else str(process_formula(x, line_segs_list[k][i])) for i in range(len(line_segs_list[k]))])

            if mode in [0, 2]:
                baseline_func_list.append((line_func, len(line_segs_list) - 1))
            if mode in [1, 2]:
                cobbl_func_list.append((line_func, len(line_segs_list) - 1))
    
    baseline = lambda x : "".join([func(i, x) for (func, i) in baseline_func_list])
    cobbl = lambda x : "".join([func(i, x) for (func, i) in cobbl_func_list])
    f.close()
    
    f_result_name = f"zok_tests/raw/{b_name}_result.raw"
    os.system(f"echo \"{b_name} {CONST_EXPAND} {REPEAT}\" > {f_result_name}")
    constants_base = dict(constants)
    # Process programs for each constant
    for _ in range(CONST_EXPAND):
        const_list = "; ".join([str(k) + " " + str(constants[k]) for k in constants])
        print(f"\n---\nCONSTANTS: {const_list}")
        os.system(f"echo \"{const_list}\" >> {f_result_name}")

        # Produce code
        with open(f"zok_tests/benchmarks/{b_name}.zok", "w") as f_baseline:
            f_baseline.write(baseline(constants))
        with open(f"zok_tests/benchmarks/{b_name}_cobbl.zok", "w") as f_cobbl:
            f_cobbl.write(cobbl(constants))

        for _ in range(REPEAT):
            # Produce variables. Each constant is of form max_XX, where XX is a variable
            # v = c
            print("\nTesting V = C...")
            for c in constants:
                v = c[4:]
                inputs[v] = constants[c]
            with open(f"zok_tests/benchmarks/{b_name}.input", "w") as f_input:
                f_input.writelines([f"{var} {inputs[var]}\n" for var in inputs])
                f_input.write("END")
            with open(f"zok_tests/benchmarks/{b_name}_cobbl.input", "w") as f_input:
                f_input.writelines([f"{var} {inputs[var]}\n" for var in inputs])
                f_input.write("END")
            execute_baseline(b_name, f_result_name)
            execute_cobbl_for(b_name, f_result_name)
            execute_cobbl_while(b_name, f_result_name, 100)

            # v = 90% c
            print("\nTesting V = 90% C...")
            for c in constants:
                v = c[4:]
                inputs[v] = constants[c] * 9 // 10
            with open(f"zok_tests/benchmarks/{b_name}_cobbl.input", "w") as f_input:
                f_input.writelines([f"{var} {inputs[var]}\n" for var in inputs])
                f_input.write("END")
            execute_cobbl_while(b_name, f_result_name, 90)

            # v = 75% c
            print("\nTesting V = 75% C...")
            for c in constants:
                v = c[4:]
                inputs[v] = constants[c] * 3 // 4
            with open(f"zok_tests/benchmarks/{b_name}_cobbl.input", "w") as f_input:
                f_input.writelines([f"{var} {inputs[var]}\n" for var in inputs])
                f_input.write("END")
            execute_cobbl_while(b_name, f_result_name, 75)

            # v = 50% c
            print("\nTesting V = 50% C...")
            for c in constants:
                v = c[4:]
                inputs[v] = constants[c] // 2
            with open(f"zok_tests/benchmarks/{b_name}_cobbl.input", "w") as f_input:
                f_input.writelines([f"{var} {inputs[var]}\n" for var in inputs])
                f_input.write("END")
            execute_cobbl_while(b_name, f_result_name, 50)

        for var in constants:
            constants[var] += constants_base[var]

def execute_baseline(b_name, f_name):
    print("BASELINE")
    os.system(f"echo 'BASELINE' >> {f_name}")
    os.system(f"cd circ_baseline && target/release/examples/circ --language zsharp {b_name} r1cs | \
                sed -n -e 's/Compiler time: //p' \
                    -e 's/  \* SNARK::encode //p' \
                    -e 's/  \* SNARK::prove //p' \
                    -e 's/  \* SNARK::verify //p' \
                >> ../{f_name}")

def execute_cobbl_for(b_name, f_name):
    print("COBBL - FOR")
    os.system(f"echo 'COBBL_FOR' >> {f_name}")
    os.system(f"cd circ_blocks && target/release/examples/zxc {b_name} | \
            sed -n 's/Compiler time: //p' \
                >> ../{f_name}")
    os.system(f"cd spartan_parallel && RUST_BACKTRACE=1 target/release/examples/interface {b_name} | \
                sed -n -e 's/Preprocess time: //p' \
                    -e 's/  \* SNARK::prove //p' \
                    -e 's/  \* SNARK::verify //p' \
                >> ../{f_name}")

def execute_cobbl_while(b_name, f_name, perc):
    b_name += "_cobbl"
    print("COBBL - WHILE")
    os.system(f"echo 'COBBL_WHILE {perc}' >> {f_name}")
    os.system(f"cd circ_blocks && target/release/examples/zxc {b_name} | \
            sed -n 's/Compiler time: //p' \
                >> ../{f_name}")
    os.system(f"cd spartan_parallel && RUST_BACKTRACE=1 target/release/examples/interface {b_name} | \
                sed -n -e 's/Preprocess time: //p' \
                    -e 's/  \* SNARK::prove //p' \
                    -e 's/  \* SNARK::verify //p' \
                >> ../{f_name}")

BENCHMARK = ["find_min", "mat_mult", "kmp_search"]
# BENCHMARK = ["find_min"]
for b in BENCHMARK:
    preprocess(b)
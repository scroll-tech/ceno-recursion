import matplotlib.pyplot as plt

def extract_time(f, l):
    # Jolt time_data contains 3 metrics: compiler, prover, verifier
    # CoBBl time_data contains 4 metrics: compiler, preprocessor, prover, verifier
    # Inputs are streams of form "X.XXXs/ms/μs", need to be converted to floats in ms
    time_data = []
    for _ in range(l):
        last_pos = f.tell()
        t = f.readline().strip()
        try:
            if t[-2] == 'm':
                time_data.append(float(t[:-2]))
            elif t[-2] == 'μ':
                time_data.append(float(t[:-2]) / 1000)
            else:
                time_data.append(float(t[:-1]) * 1000)
        except:
            time_data.append(0.0)
            f.seek(last_pos)
    return time_data

# parse raw/jolt_result.raw
def parse_jolt():
    jolt_result = {}

    f = open(f"zok_tests/raw/jolt_result.raw", 'r')
    line = f.readline().strip()
    while line:
        while line[:2] != "--":
            line = f.readline().strip()
        # Benchmark Name
        b_name = f.readline().strip()
        # Compiler, Prover, Verifier
        jolt_result[b_name] = extract_time(f, 3)
        line = f.readline().strip()

    f.close()
    return jolt_result

# parse raw/XXX_result.raw
def parse_cobbl(b_name, jolt_result):
    f = open(f"zok_tests/raw/{b_name}_result.raw", 'r')
    line = f.readline().strip()
    # first line is benchmark_name / const_expand / repeat
    line = line.split(' ')
    b_name = line[0]
    c_expand = int(line[1])
    repeat = int(line[2])

    for _ in range(c_expand):
        # first line is a list of [const_name, val]
        consts = f.readline().strip()
        # Record time entries for BASELINE, COBBL_FOR, COBBL_WHILE, COBBL_NO_OPT, COBBL_75, COBBL_50
        # Entreis: Compiler Time, Preprocess Time, Prover Time, Verifier Time
        time_entries = [[0.0] * 4 for _ in range(6)]
        # Record constraint entries for BASELINE, COBBL_FOR, COBBL_WHILE, COBBL_NO_OPT, COBBL_75, COBBL_50
        # Entries: Commit Size, Var Size, Exec Size, Extra Cons Size
        cons_entries = [[0] * 4 for _ in range(6)]
        for _ in range(repeat):
            # Circ Baseline: Num Cons, Compiler Time, Num Vars, Num NNZ (x3), Preprocess Time, Prover Time, Verifier Time
            # read entry name
            e = 0
            f.readline()
            last_pos = f.tell()
            t = f.readline().strip()
            try:
                cons_entries[e][2] = int(t) # Num Cons
            except:
                f.seek(last_pos)
            tmp_time = extract_time(f, 1)
            time_entries[e][0] = tmp_time[0]
            last_pos = f.tell()
            t = f.readline().strip()
            try:
                cons_entries[e][1] = int(t) # Num Vars
            except:
                f.seek(last_pos)
            last_pos = f.tell()
            t1 = f.readline().strip()
            t2 = f.readline().strip()
            t3 = f.readline().strip()
            try:
                cons_entries[e][0] = max(int(t1), int(t2), int(t3)) # Num NNZ (x3)
            except:
                f.seek(last_pos)
            tmp_time = extract_time(f, 3)
            for t in range(3):
                time_entries[e][t + 1] += tmp_time[t]
            # CoBBl: Compiler Time, (Num NNZ, Num Vars, Num Cons) x3, Preprocess Time, Prover Time, Verifier Time
            for e in range(1, 6):
                # read entry name
                f.readline()
                tmp_time = extract_time(f, 1)
                time_entries[e][0] = tmp_time[0]
                
                cons_entries[e] = [0] * 4
                for i in range(3):
                    cons_entries[e][0] += int(f.readline().strip()) # Num NNZ
                    cons_entries[e][1] += int(f.readline().strip()) # Num Vars
                    tmp_cons = int(f.readline().strip())
                    cons_entries[e][2] += tmp_cons # Num Cons
                    if i != 0:
                        cons_entries[e][3] += tmp_cons # Extra Cons

                tmp_time = extract_time(f, 3)
                for t in range(3):
                    time_entries[e][t + 1] += tmp_time[t]
        for e in range(6):
            for t in range(4):
                time_entries[e][t] /= repeat

        # Print out the result
        case_name = f"{b_name} - {consts}" if len(consts) > 0 else f"{b_name}"
        print(case_name)
        print("RUNTIME")
        print("{:10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}".format("", "CirC", "CoBBl For", "Jolt", "CoBBl While", "CoBBL NoOpt", "CoBBl 75", "CoBBl 50"))
        t_name = ["Compiler", "Preprocess", "Prover", "Verifier"]
        for j in range(4):
            print("{:10}".format(t_name[j]), end = '')
            # CirC
            for i in range(0, 2):
                if time_entries[i][j] != 0:
                    print("    {:10.2f}".format(time_entries[i][j]), end = '')
                else:
                    print("    {:>10}".format("-"), end = '')
            # Jolt
            if j != 1 and case_name in jolt_result.keys() and jolt_result[case_name][0 if j == 0 else j - 1] != 0:
                print("    {:10.2f}".format(jolt_result[case_name][0 if j == 0 else j - 1]), end = '')
            else:
                print("    {:>10}".format("-"), end = '')
            # CoBBl
            for i in range(2, 6):
                if time_entries[i][j] != 0:
                    print("    {:10.2f}".format(time_entries[i][j]), end = '')
                else:
                    print("    {:>10}".format("-"), end = '')
            print()

        print("--\nCONSTRAINTS")
        print("{:10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}".format("", "CirC", "CoBBl For", "CoBBl While", "CoBBl NoOpt", "CoBBl 75", "CoBBl 50"))
        t_name = ["Commit", "Var", "Exec", "Extra"]
        for j in range(4):
            print("{:10}".format(t_name[j]), end = '')
            # CirC & CoBBl
            for i in range(6):
                if cons_entries[i][j] != 0:
                    print("    {:>10}".format(cons_entries[i][j]), end = '')
                else:
                    print("    {:>10}".format("-"), end = '')
            print()

        print("\n--\n")
    
    line = f.readline().strip()

    f.close()

# Only record benchmark cases included in requested_b_name_list
def extract_circ_plot(b_name_list, requested_b_name_list):
    # circ_data is of size 3 (Compiler, Prover, Verifier) x Num_Bench x 3 (100, 75, 50)
    circ_data = [[], [], []]
    for b_name in b_name_list:
        f = open(f"zok_tests/raw/{b_name}_result.raw", 'r')
        line = f.readline().strip()
        # first line is benchmark_name / const_expand / repeat
        line = line.split(' ')
        b_name = line[0]
        c_expand = int(line[1])
        repeat = int(line[2])

        for _ in range(c_expand):
            # first line is a list of [const_name, val]
            consts = f.readline().strip()
            # Record time entries for BASELINE, COBBL_FOR, COBBL_WHILE, COBBL_NO_OPT, COBBL_75, COBBL_50
            # Entreis: Compiler Time, Preprocess Time, Prover Time, Verifier Time
            time_entries = [[0.0] * 4 for _ in range(6)]
            # Record constraint entries for BASELINE, COBBL_FOR, COBBL_WHILE, COBBL_NO_OPT, COBBL_75, COBBL_50
            # Entries: Commit Size, Var Size, Exec Size, Extra Cons Size
            cons_entries = [[0] * 4 for _ in range(6)]
            for _ in range(repeat):
                # Circ Baseline: Num Cons, Compiler Time, Num Vars, Num NNZ (x3), Preprocess Time, Prover Time, Verifier Time
                # read entry name
                e = 0
                f.readline()
                last_pos = f.tell()
                t = f.readline().strip()
                try:
                    cons_entries[e][2] = int(t) # Num Cons
                except:
                    f.seek(last_pos)
                tmp_time = extract_time(f, 1)
                time_entries[e][0] = tmp_time[0]
                last_pos = f.tell()
                t = f.readline().strip()
                try:
                    cons_entries[e][1] = int(t) # Num Vars
                except:
                    f.seek(last_pos)
                last_pos = f.tell()
                t1 = f.readline().strip()
                t2 = f.readline().strip()
                t3 = f.readline().strip()
                try:
                    cons_entries[e][0] = max(int(t1), int(t2), int(t3)) # Num NNZ (x3)
                except:
                    f.seek(last_pos)
                tmp_time = extract_time(f, 3)
                for t in range(3):
                    time_entries[e][t + 1] += tmp_time[t]
                # CoBBl: Compiler Time, (Num NNZ, Num Vars, Num Cons) x3, Preprocess Time, Prover Time, Verifier Time
                for e in range(1, 6):
                    # read entry name
                    f.readline()
                    tmp_time = extract_time(f, 1)
                    time_entries[e][0] = tmp_time[0]
                    
                    cons_entries[e] = [0] * 4
                    for i in range(3):
                        cons_entries[e][0] += int(f.readline().strip()) # Num NNZ
                        cons_entries[e][1] += int(f.readline().strip()) # Num Vars
                        tmp_cons = int(f.readline().strip())
                        cons_entries[e][2] += tmp_cons # Num Cons
                        if i != 0:
                            cons_entries[e][3] += tmp_cons # Extra Cons

                    tmp_time = extract_time(f, 3)
                    for t in range(3):
                        time_entries[e][t + 1] += tmp_time[t]
            for e in range(6):
                for t in range(4):
                    time_entries[e][t] /= repeat

            case_name = f"{b_name} - {consts}" if len(consts) > 0 else f"{b_name}"
            if case_name in requested_b_name_list:
                # Compiler, Prover, Verifier
                for j in range(3):
                    k = [0, 2, 3][j]
                    # CirC
                    if time_entries[0][k] == 0:
                        circ_data[j].append([0, 0, 0])
                    else:
                        circ_data[j].append([time_entries[1][k] / time_entries[0][k], time_entries[4][k] / time_entries[0][k], time_entries[5][k] / time_entries[0][k]])
        line = f.readline().strip()

        f.close()
    return (circ_data)

def extract_benchmark_plot(b_name):
    f = open(f"zok_tests/raw/{b_name}_result.raw", 'r')
    line = f.readline().strip()
    # first line is benchmark_name / const_expand / repeat
    line = line.split(' ')
    b_name = line[0]
    c_expand = int(line[1])
    repeat = int(line[2])

    # Convert data into runtime_data & constraint_data
    # runtime_data is of size 3 (Compiler, Prover, Verifier) x 2 (CirC, CoBBl) x Num_Expand
    runtime_data = [[[], []], [[], []], [[], []]]
    # constraint_data is of size 3 (Commit, Exec, Var) x 2 (CirC, CoBBl) x Num_Expand
    constraint_data = [[[], []], [[], []], [[], []]]

    for _ in range(c_expand):
        # first line is a list of [const_name, val]
        consts = f.readline().strip()
        # Record time entries for BASELINE, COBBL_FOR, COBBL_WHILE, COBBL_NO_OPT, COBBL_75, COBBL_50
        # Entreis: Compiler Time, Preprocess Time, Prover Time, Verifier Time
        time_entries = [[0.0] * 4 for _ in range(6)]
        # Record constraint entries for BASELINE, COBBL_FOR, COBBL_WHILE, COBBL_NO_OPT, COBBL_75, COBBL_50
        # Entries: Commit Size, Var Size, Exec Size, Extra Cons Size
        cons_entries = [[0] * 4 for _ in range(6)]
        for _ in range(repeat):
            # Circ Baseline: Num Cons, Compiler Time, Num Vars, Num NNZ (x3), Preprocess Time, Prover Time, Verifier Time
            # read entry name
            e = 0
            f.readline()
            last_pos = f.tell()
            t = f.readline().strip()
            try:
                cons_entries[e][2] = int(t) # Num Cons
            except:
                f.seek(last_pos)
            tmp_time = extract_time(f, 1)
            time_entries[e][0] = tmp_time[0]
            last_pos = f.tell()
            t = f.readline().strip()
            try:
                cons_entries[e][1] = int(t) # Num Vars
            except:
                f.seek(last_pos)
            last_pos = f.tell()
            t1 = f.readline().strip()
            t2 = f.readline().strip()
            t3 = f.readline().strip()
            try:
                cons_entries[e][0] = max(int(t1), int(t2), int(t3)) # Num NNZ (x3)
            except:
                f.seek(last_pos)
            tmp_time = extract_time(f, 3)
            for t in range(3):
                time_entries[e][t + 1] += tmp_time[t]
            # CoBBl: Compiler Time, (Num NNZ, Num Vars, Num Cons) x3, Preprocess Time, Prover Time, Verifier Time
            for e in range(1, 6):
                # read entry name
                f.readline()
                tmp_time = extract_time(f, 1)
                time_entries[e][0] = tmp_time[0]
                
                cons_entries[e] = [0] * 4
                for i in range(3):
                    cons_entries[e][0] += int(f.readline().strip()) # Num NNZ
                    cons_entries[e][1] += int(f.readline().strip()) # Num Vars
                    tmp_cons = int(f.readline().strip())
                    cons_entries[e][2] += tmp_cons # Num Cons
                    if i != 0:
                        cons_entries[e][3] += tmp_cons # Extra Cons

                tmp_time = extract_time(f, 3)
                for t in range(3):
                    time_entries[e][t + 1] += tmp_time[t]
        for e in range(6):
            for t in range(4):
                time_entries[e][t] /= repeat

        # Compiler, Prover, Verifier
        for j in range(3):
            k = [0, 2, 3][j]
            # CirC
            runtime_data[j][0].append(time_entries[0][k])
            runtime_data[j][1].append(time_entries[1][k])
            constraint_data[j][0].append(cons_entries[0][j])
            constraint_data[j][1].append(cons_entries[1][j])

    line = f.readline().strip()

    f.close()
    return (c_expand, runtime_data, constraint_data)

# Generate plots based on data
# circ_data is of size 3 (Compiler, Prover, Verifier) x Num_Bench x 3 (100, 75, 50)
# jolt_data is of size 3 (Compiler, Prover, Verifier) x Num_Bench x 2 (u32, ff)
def gen_circ_jolt_plots(runtime_benchmark_names, circ_data): #, jolt_data, constraint_data, opt_data):
    colors = [["maroon", "orangered", "salmon"], ["darkgreen", "seagreen", "yellowgreen"], ["steelblue", "dodgerblue", "skyblue"]]

    # Runtime graphs: Percentage comparison between compiler, prover, verifier
    runtime_subplot_name = ["Compiler %", "Prover %", "Verifier %"]
    circ_plot_name = "Circ - CoBBl"
    
    plt.figure(figsize=(14, 8)) 
    # Compiler, Prover, Verifier
    for i in range(3):
        plt.subplot(3, 1, i + 1)
        for bench in range(len(runtime_benchmark_names)):
            # 100, 75, 50
            for j in range(3):
                if j == 1:
                    plt.bar(5 * bench + j, circ_data[i][bench][j], color=colors[i][j], tick_label=runtime_benchmark_names[bench])
                else:
                    plt.bar(5 * bench + j, circ_data[i][bench][j], color=colors[i][j])
                plt.annotate((f"%0.2f" % (circ_data[i][bench][j] * 100)), (5 * bench + j - 0.4, circ_data[i][bench][j] + (0.02 if i == 2 else 0.002)))
        if i == 2:
            plt.axhline(y=1, linestyle='--', color="red")
        ax = plt.gca()
        ax.set_xticks([5 * bench + 1 for bench in range(len(runtime_benchmark_names))])
        ax.set_xticklabels(runtime_benchmark_names)
        vals = ax.get_yticks()
        ax.set_yticklabels(['{:,.0%}'.format(x) for x in vals])
        plt.title(runtime_subplot_name[i])

    plt.tight_layout()
    plt.savefig('paper/graph/fig_eval_circ.png')

# runtime_data is of size 3 (Compiler, Prover, Verifier) x 2 (CirC, CoBBl) x Num_Expand
# constraint_data is of size 3 (Commit, Exec, Var) x 2 (CirC, CoBBl) x Num_Expand
def gen_benchmark_plot(num_expand, runtime_data, constraint_data):
    benchmark_runtime_name = "Runtime Comparison for Find Min"
    x_data = [200 * x for x in range(num_expand)]
    runtime_subplot_name = ["Compile Time (ms)", "Prove Time (ms)", "Verification Time (ms)"]
    plt.figure(figsize=(14, 8)) 
    # Compiler, Prover, Verifier
    for i in range(3):
        plt.subplot(2, 3, i + 1)
        plt.plot(x_data, runtime_data[i][0], label="CirC", marker='o')
        for j, txt in enumerate(runtime_data[i][0]):
            plt.annotate(f"%0.0f" % txt, (x_data[j] * 1.02, runtime_data[i][0][j] * 0.98))
        plt.plot(x_data, runtime_data[i][1], label="CoBBl", marker='o')
        for j, txt in enumerate(runtime_data[i][1]):
            plt.annotate(f"%0.0f" % txt, (x_data[j] * 1.02, runtime_data[i][1][j] * 0.98))
        plt.title(runtime_subplot_name[i])
        plt.legend()

    constraint_subplot_name = ["Instance Size (non-zero entries)", "Number of Variables", "Number of Executed Constraints"]
    # Compiler, Prover, Verifier
    for i in range(3):
        plt.subplot(2, 3, 3 + i + 1)
        plt.plot(x_data, constraint_data[i][0], label="CirC", marker='o')
        for j, txt in enumerate(constraint_data[i][0]):
            plt.annotate(f"%0.0f" % txt, (x_data[j] * 1.02, constraint_data[i][0][j] * 0.98))
        plt.plot(x_data, constraint_data[i][1], label="CoBBl", marker='o')
        for j, txt in enumerate(constraint_data[i][1]):
            plt.annotate(f"%0.0f" % txt, (x_data[j] * 1.02, constraint_data[i][1][j] * 0.98))
        plt.title(constraint_subplot_name[i])
        plt.legend()
    
    plt.tight_layout()
    plt.savefig('paper/graph/fig_eval_find_min.png')


BENCHMARK = ["find_min", "mat_mult", "kmp_search", "dna_align", "rle_codec", "find_min_ff", "mat_mult_ff", "sha256", "poseidon"]
# BENCHMARK = ["find_min"]
jolt_result = parse_jolt()
for b in BENCHMARK:
    parse_cobbl(b, jolt_result)

# Graph 1
requested_b_name_list = [
    "find_min - max_high 1000", 
    "mat_mult - max_n 4", 
    "kmp_search - max_n 480; max_m 48",
    "dna_align - max_n 10",
    "rle_codec - max_n 300",
    "sha256 - max_n 4",
    "poseidon"
]
runtime_benchmark_names = [
    "Find Min, len = 1000", 
    "Matrix Mult, size = 4x4",
    "Pattern Match, len = 480 / 48",
    "LCS, len = 10",
    "RLE, len = 300",
    "Sha256, len = 4",
    "Poseidon, len = 8"
]
circ_data = extract_circ_plot(BENCHMARK, requested_b_name_list)
print(circ_data)
gen_circ_jolt_plots(runtime_benchmark_names, circ_data)

# Graph 2
(num_expand, runtime_data, constraint_data) = extract_benchmark_plot("find_min")
gen_benchmark_plot(num_expand, runtime_data, constraint_data)
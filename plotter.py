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
    while line:
        # first line is benchmark_name / const_expand / repeat
        line = line.split(' ')
        b_name = line[0]
        c_expand = int(line[1])
        repeat = int(line[2])

        for _ in range(c_expand):
            # first line is a list of [const_name, val]
            consts = f.readline().strip()
            # Record time entries for BASELINE, COBBL_FOR, COBBL_WHILE, COBBL_NO_OPT
            # Entreis: Compiler Time, Preprocess Time, Prover Time, Verifier Time
            time_entries = [[0.0] * 4 for _ in range(4)]
            # Record constraint entries for BASELINE, COBBL_FOR, COBBL_WHILE, COBBL_NO_OPT
            # Entries: Commit Size, Var Size, Exec Size, Extra Cons Size
            cons_entries = [[0] * 4 for _ in range(4)]
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
                for e in range(1, 4):
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
            for e in range(4):
                for t in range(4):
                    time_entries[e][t] /= repeat

            # Print out the result
            case_name = f"{b_name} - {consts}" if len(consts) > 0 else f"{b_name}"
            print(case_name)
            print("RUNTIME")
            print("{:10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}".format("", "CirC", "CoBBl For", "Jolt", "CoBBl While", "CoBBL NoOpt"))
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
                for i in range(2, 4):
                    if time_entries[i][j] != 0:
                        print("    {:10.2f}".format(time_entries[i][j]), end = '')
                    else:
                        print("    {:>10}".format("-"), end = '')
                print()

            print("--\nCONSTRAINTS")
            print("{:10}    {:>10}    {:>10}    {:>10}    {:>10}".format("", "CirC", "CoBBl For", "CoBBl While", "CoBBl NoOpt"))
            t_name = ["Commit", "Var", "Exec", "Extra"]
            for j in range(4):
                print("{:10}".format(t_name[j]), end = '')
                # CirC & CoBBl
                for i in range(4):
                    if cons_entries[i][j] != 0:
                        print("    {:>10}".format(cons_entries[i][j]), end = '')
                    else:
                        print("    {:>10}".format("-"), end = '')
                print()

            print("\n--\n")
        
        line = f.readline().strip()

    f.close()

# Generate plots based on data
# circ_data is of size 3 (Compiler, Prover, Verifier) x Num_Bench x 3 (100, 75, 50)
# jolt_data is of size 3 (Compiler, Prover, Verifier) x Num_Bench x 2 (u32, ff)
# constraint_data is of size 3 (Commit, Exec, Var) x 2 (Circ, CoBBl) x Num_Expand
def gen_plots(circ_data): #, jolt_data, constraint_data, opt_data):
    colors = [["maroon", "orangered", "salmon"], ["darkgreen", "seagreen", "yellowgreen"], ["steelblue", "dodgerblue", "skyblue"]]

    # Runtime graphs: Percentage comparison between compiler, prover, verifier
    runtime_benchmark_names = ["Find Min, N = 1000", "Mat Mult, N = 4x4"]
    runtime_subplot_name = ["Compiler %", "Prover %", "Verifier %"]
    circ_plot_name = "Circ - CoBBl"
    for i in range(3):
        plt.subplot(3, 1, i + 1)
        for bench in range(len(runtime_benchmark_names)):
            # 100, 75, 50
            for j in range(3):
                if j == 1:
                    plt.bar(5 * bench + j, circ_data[i][bench][j], color=colors[i][j], tick_label=runtime_benchmark_names[bench])
                else:
                    plt.bar(5 * bench + j, circ_data[i][bench][j], color=colors[i][j])
        ax = plt.gca()
        ax.set_xticks([5 * bench + 1 for bench in range(len(runtime_benchmark_names))])
        ax.set_xticklabels(runtime_benchmark_names)
        plt.title(runtime_subplot_name[i])

    plt.tight_layout()
    plt.show()


BENCHMARK = ["find_min", "mat_mult", "kmp_search", "dna_align", "rle_codec", "find_min_ff", "mat_mult_ff", "sha256", "poseidon"]
# BENCHMARK = ["find_min"]
# jolt_result = parse_jolt()
# for b in BENCHMARK:
#     parse_cobbl(b, jolt_result)
circ_data = [[[15, 13, 11], [15, 13, 11]], [[16, 14, 12], [16, 14, 12]], [[120, 100, 80], [120, 100, 80]]]
gen_plots(circ_data)
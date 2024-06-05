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
            # Next 6 entries are BASELINE, COBBL_FOR, COBBL_WHILE 100, 90, 75, 50
            entries = [[0.0] * 4 for _ in range(6)]
            for _ in range(repeat):
                for e in range(6):
                    # read entry name
                    f.readline()
                    tmp_time = extract_time(f, 4)
                    for t in range(4):
                        entries[e][t] += tmp_time[t]
            for e in range(6):
                for t in range(4):
                    entries[e][t] /= repeat

            # Print out the result
            case_name = f"{b_name} - {consts}"
            print(case_name)
            print("{:10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}".format("", "CirC", "CoBBl For", "Jolt", "CoBBl 100", "CoBBl 90", "CoBBl 75", "CoBBl 50"))
            t_name = ["Compiler", "Preprocess", "Prover", "Verifier"]
            for j in range(4):
                print("{:10}".format(t_name[j]), end = '')
                # CirC
                for i in range(0, 2):
                    if entries[i][j] != 0:
                        print("    {:10.2f}".format(entries[i][j]), end = '')
                    else:
                        print("    {:>10}".format("-"), end = '')
                # Jolt
                if j != 1 and case_name in jolt_result.keys() and jolt_result[case_name][0 if j == 0 else j - 1] != 0:
                    print("    {:10.2f}".format(jolt_result[case_name][0 if j == 0 else j - 1]), end = '')
                else:
                    print("    {:>10}".format("-"), end = '')
                # CoBBl
                for i in range(2, 6):
                    if entries[i][j] != 0:
                        print("    {:10.2f}".format(entries[i][j]), end = '')
                    else:
                        print("    {:>10}".format("-"), end = '')
                print()
            print("\n--\n")
        
        line = f.readline().strip()

    f.close()

BENCHMARK = ["find_min", "mat_mult", "kmp_search", "dna_align"]
# BENCHMARK = ["dna_align"]
jolt_result = parse_jolt()
for b in BENCHMARK:
    parse_cobbl(b, jolt_result)
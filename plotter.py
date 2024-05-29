def extract_time(f):
    compiler_s = f.readline().strip()
    preprocessor_s = f.readline().strip()
    prover_s = f.readline().strip()
    verifier_s = f.readline().strip()
    # Time_data contains 4 metrics: compiler, preprocessor, prover, verifier
    # Inputs are streams of form "X.XXXs/ms/μs", need to be converted to floats in ms
    time_data = []
    for t in [compiler_s, preprocessor_s, prover_s, verifier_s]:
        if t[-2] == 'm':
            time_data.append(float(t[:-2]))
        elif t[-2] == 'μ':
            time_data.append(float(t[:-2]) / 1000)
        else:
            time_data.append(float(t[:-1]) * 1000)
    return time_data

# parse raw/XXX_result.raw
def parse(b_name):
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
                    tmp_time = extract_time(f)
                    for t in range(4):
                        entries[e][t] += tmp_time[t]
            for e in range(6):
                for t in range(4):
                    entries[e][t] /= repeat
            
            # Print out the result
            print(f"{b_name} - {consts}")
            print("{:10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}    {:>10}".format("", "Baseline", "CoBBl For", "CoBBl 100", "CoBBl 90", "CoBBl 75", "CoBBl 50"))
            print("{:10}".format("Compiler"), end = '')
            for i in range(6):
                print("    {:10.2f}".format(entries[i][0]), end = '')
            print()
            print("{:10}".format("Preprocess"), end = '')
            for i in range(6):
                print("    {:10.2f}".format(entries[i][1]), end = '')
            print()
            print("{:10}".format("Prover"), end = '')
            for i in range(6):
                print("    {:10.2f}".format(entries[i][2]), end = '')
            print()
            print("{:10}".format("Verifier"), end = '')
            for i in range(6):
                print("    {:10.2f}".format(entries[i][3]), end = '')
            print("\n\n--\n")
        
        line = f.readline().strip()

    f.close()

BENCHMARK = ["find_min", "mat_mult"]
# BENCHMARK = ["kmp_search"]
for b in BENCHMARK:
    parse(b)
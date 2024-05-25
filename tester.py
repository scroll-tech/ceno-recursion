import os

BENCHMARK = "kmp_search"

print("\n--\nCOBBL")
os.system(f"cd circ_blocks && target/release/examples/zxc {BENCHMARK} | \
          sed -n 's/Compiler time: //p'")
os.system(f"cd spartan_parallel && RUST_BACKTRACE=1 target/release/examples/interface {BENCHMARK} | \
            sed -n -e 's/Preprocess time: //p' \
                -e 's/  \* SNARK::prove //p' \
                -e 's/  \* SNARK::verify //p'")

print("\n--\nBASELINE")
os.system(f"cd circ_baseline && target/release/examples/circ --language zsharp {BENCHMARK} r1cs | \
            sed -n -e 's/Compiler time: //p' \
                -e 's/  \* SNARK::encode //p' \
                -e 's/  \* SNARK::prove //p' \
                -e 's/  \* SNARK::verify //p'")
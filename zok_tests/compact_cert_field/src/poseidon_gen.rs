// Generate a poseidon zok file where every constants are registers
use crate::poseidon_constants::*;
use rug::Integer;
use std::fs::File;
use std::io::Write;

pub fn poseidon_gen(N: usize, Batch: usize) {
    assert!(Batch == 1 || Batch == 2);

    let (c, m) = gen_consts();

    // Generate Zok File
    let file_name = format!("../benchmarks/compact_cert/poseidon{}.zok", N);
    let mut f = File::create(file_name).unwrap();

    if Batch == 2 {
        writeln!(&mut f, "from \"./poseidon_struct.zok\" import DoubleHash").unwrap();
    }

    write!(&mut f, "def poseidon{}_batch{}(", N, Batch).unwrap();
    for i in 0..Batch {
        for j in 1..N + 1 {
            if i == 0 && j == 1 {
                write!(&mut f, "field state{}_{}", j, i).unwrap();
            } else {
                write!(&mut f, ", field state{}_{}", j, i).unwrap();
            }
        }
    }
    if Batch == 2 {
        writeln!(&mut f, ") -> DoubleHash:").unwrap();
    } else {
        writeln!(&mut f, ") -> field:").unwrap();
    }

    for i in 0..Batch {
        writeln!(&mut f, "    field state0_{} = 0", i).unwrap();
    }
    writeln!(&mut f, "").unwrap();
    for i in 0..c.len() {
        writeln!(&mut f, "    field c{} = {}", i, Integer::from(&c[i])).unwrap();
    }
    writeln!(&mut f, "").unwrap();
    for i in 0..m.len() {
        writeln!(&mut f, "    field m{} = {}", i, Integer::from(&m[i])).unwrap();
    }
    writeln!(&mut f, "").unwrap();
    // Iterations
    let t = N + 1;
    let rounds_p = [56, 57, 56, 60, 60, 63, 64, 63];
    let p = rounds_p[t - 2];
    let round = 8;
    for b in 0..Batch {
        for r in 0..round + p {
            writeln!(&mut f, "    // --").unwrap();
            writeln!(&mut f, "    // r = {}", r).unwrap();
            writeln!(&mut f, "    // ark").unwrap();
            let it = t * r;
            for i in 0..t {
                writeln!(&mut f, "    state{}_{} = state{}_{} + c{}", i, b, i, b, it + i).unwrap();
            }
            writeln!(&mut f, "    // sbox").unwrap();
            writeln!(&mut f, "    field new_state0_{} = state0_{} ** 5", b, b).unwrap();
            if r < round / 2 || r >= round / 2 + p {
                for i in 1..t {
                    writeln!(&mut f, "    field new_state{}_{} = state{}_{} ** 5", i, b, i, b).unwrap();
                }
            } else {
                for i in 1..t {
                    writeln!(&mut f, "    field new_state{}_{} = state{}_{}", i, b, i, b).unwrap();
                }
            }
            writeln!(&mut f, "    // mix").unwrap();
            for i in 0..t {
                write!(&mut f, "    state{}_{} = new_state{}_{} * m{}", i, b, 0, b, i * 9).unwrap();
                for j in 1..t {
                    write!(&mut f, " + new_state{}_{} * m{}", j, b, i * 9 + j).unwrap();
                }
                writeln!(&mut f, "").unwrap();
            }
        }
    }
    if Batch == 2 {
        writeln!(&mut f, "    return DoubleHash {{").unwrap();
        writeln!(&mut f, "        hash0: state0_0,").unwrap();
        writeln!(&mut f, "        hash1: state0_1").unwrap();
        writeln!(&mut f, "    }}").unwrap();
    } else {
        writeln!(&mut f, "    return state0").unwrap();
    }
}
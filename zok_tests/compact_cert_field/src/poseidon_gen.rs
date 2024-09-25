// Generate a poseidon zok file where every constants are registers
use crate::poseidon_constants::*;
use rug::Integer;
use std::fs::File;
use std::io::Write;

pub fn poseidon_gen(N: usize) {
    let (c, m) = gen_consts();

    // Generate Zok File
    let file_name = format!("../benchmarks/compact_cert/poseidon{}.zok", N);
    let mut f = File::create(file_name).unwrap();

    write!(&mut f, "def poseidon{}(field state1", N).unwrap();
    for i in 2..N + 1 {
        write!(&mut f, ", field state{}", i).unwrap();
    }
    writeln!(&mut f, ") -> field:").unwrap();

    writeln!(&mut f, "    field state0 = 0").unwrap();
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
    for r in 0..round + p {
        writeln!(&mut f, "    // --").unwrap();
        writeln!(&mut f, "    // r = {}", r).unwrap();
        writeln!(&mut f, "    // ark").unwrap();
        let it = t * r;
        for i in 0..t {
            writeln!(&mut f, "    state{} = state{} + c{}", i, i, it + i).unwrap();
        }
        writeln!(&mut f, "    // sbox").unwrap();
        writeln!(&mut f, "    field new_state0 = state0 ** 5").unwrap();
        if r < round / 2 || r >= round / 2 + p {
            for i in 1..t {
                writeln!(&mut f, "    field new_state{} = state{} ** 5", i, i).unwrap();
            }
        } else {
            for i in 1..t {
                writeln!(&mut f, "    field new_state{} = state{}", i, i).unwrap();
            }
        }
        writeln!(&mut f, "    // mix").unwrap();
        for i in 0..t {
            write!(&mut f, "    state{} = new_state{} * m{}", i, 0, i * 9).unwrap();
            for j in 1..t {
                write!(&mut f, " + new_state{} * m{}", j, i * 9 + j).unwrap();
            }
            writeln!(&mut f, "").unwrap();
        }
    }
    writeln!(&mut f, "    return state0").unwrap();
}
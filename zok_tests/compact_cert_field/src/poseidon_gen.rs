// Generate a poseidon zok file where every constants are registers
use crate::poseidon_constants::*;
use rug::Integer;
use std::fs::File;
use std::io::Write;

pub fn poseidon_gen() {
    let (c, m) = gen_consts();

    // Generate Zok File
    let file_name = format!("../benchmarks/compact_cert/poseidon.zok");
    let mut f = File::create(file_name).unwrap();

    writeln!(&mut f, "def poseidon(u32 N, field[ro 0] inputs) -> field:").unwrap();
    writeln!(&mut f, "    assert(N == 5)").unwrap();
    writeln!(&mut f, "").unwrap();
    writeln!(&mut f, "    field state0 = 0").unwrap();
    writeln!(&mut f, "    field state1 = inputs[0]").unwrap();
    writeln!(&mut f, "    field state2 = inputs[1]").unwrap();
    writeln!(&mut f, "    field state3 = inputs[2]").unwrap();
    writeln!(&mut f, "    field state4 = inputs[3]").unwrap();
    writeln!(&mut f, "    field state5 = inputs[4]").unwrap();
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
    let t = 6;
    for r in 0..72 {
        writeln!(&mut f, "    // --").unwrap();
        writeln!(&mut f, "    // r = {}", r).unwrap();
        writeln!(&mut f, "    // ark").unwrap();
        let it = t * r;
        for i in 0..6 {
            writeln!(&mut f, "    state{} = state{} + c{}", i, i, it + i).unwrap();
        }
        writeln!(&mut f, "    // sbox").unwrap();
        writeln!(&mut f, "    field new_state0 = state0 ** 5").unwrap();
        if r < 4 || r >= 68 {
            for i in 1..6 {
                writeln!(&mut f, "    field new_state{} = state{} ** 5", i, i).unwrap();
            }
        } else {
            for i in 1..6 {
                writeln!(&mut f, "    field new_state{} = state{}", i, i).unwrap();
            }
        }
        writeln!(&mut f, "    // mix").unwrap();
        writeln!(&mut f, "    state0 = new_state0 * m0 + new_state1 * m1 + new_state2 * m2 + new_state3 * m3 + new_state4 * m4 + new_state5 * m5").unwrap();
        writeln!(&mut f, "    state1 = new_state0 * m9 + new_state1 * m10 + new_state2 * m11 + new_state3 * m12 + new_state4 * m13 + new_state5 * m14").unwrap();
        writeln!(&mut f, "    state2 = new_state0 * m18 + new_state1 * m19 + new_state2 * m20 + new_state3 * m21 + new_state4 * m22 + new_state5 * m23").unwrap();
        writeln!(&mut f, "    state3 = new_state0 * m27 + new_state1 * m28 + new_state2 * m29 + new_state3 * m30 + new_state4 * m31 + new_state5 * m32").unwrap();
        writeln!(&mut f, "    state4 = new_state0 * m36 + new_state1 * m37 + new_state2 * m38 + new_state3 * m39 + new_state4 * m40 + new_state5 * m41").unwrap();
        writeln!(&mut f, "    state5 = new_state0 * m45 + new_state1 * m46 + new_state2 * m47 + new_state3 * m48 + new_state4 * m49 + new_state5 * m50").unwrap();
    }
    writeln!(&mut f, "    return state0").unwrap();
}
// Generate a poseidon zok file where every constants are registers
use crate::poseidon_constants::*;
use std::{fs::File, io::Write};

pub fn poseidon_gen() {
    let c = POSEIDON_C;
    let mc = MDS_MATRIX_CIRC;
    let md = MDS_MATRIX_DIAG;

    // Generate Zok File
    let file_name = "../benchmarks/ceno_demo/poseidon.zok".to_string();
    let mut f = File::create(file_name).unwrap();

    writeln!(&mut f, "def poseidon(field[12] input) -> field[12]:").unwrap();
    for i in 0..INPUT_WIDTH {
        writeln!(&mut f, "    field state{} = input[{}]", i, i).unwrap();
    }
    writeln!(&mut f).unwrap();
    for i in 0..c.len() {
        writeln!(&mut f, "    field c{} = {}", i, c[i]).unwrap();
    }
    writeln!(&mut f).unwrap();
    for i in 0..mc.len() {
        writeln!(&mut f, "    field mc{} = {}", i, mc[i]).unwrap();
    }
    for i in 0..md.len() {
        writeln!(&mut f, "    field md{} = {}", i, md[i]).unwrap();
    }
    writeln!(&mut f).unwrap();
    // Iterations
    let t = INPUT_WIDTH;
    for r in 0..2 * HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS {
        writeln!(&mut f, "    // --").unwrap();
        writeln!(&mut f, "    // r = {}", r).unwrap();
        writeln!(&mut f, "    // ark").unwrap();
        let it = t * r;
        for i in 0..INPUT_WIDTH {
            writeln!(&mut f, "    state{} = state{} + c{}", i, i, it + i).unwrap();
        }
        writeln!(&mut f, "    // sbox").unwrap();
        writeln!(&mut f, "    field new_state0 = state0 ** 7").unwrap();
        if !(HALF_N_FULL_ROUNDS..HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS).contains(&r) {
            for i in 1..INPUT_WIDTH {
                writeln!(&mut f, "    field new_state{} = state{} ** 7", i, i).unwrap();
            }
        } else {
            for i in 1..INPUT_WIDTH {
                writeln!(&mut f, "    field new_state{} = state{}", i, i).unwrap();
            }
        }
        writeln!(&mut f, "    // mix").unwrap();
        for r in 0..INPUT_WIDTH {
            write!(&mut f, "    state{} = new_state{} * md{}", r, r, r).unwrap();
            for i in 0..INPUT_WIDTH {
                write!(&mut f, " + new_state{} * mc{}", (r + i) % INPUT_WIDTH, i).unwrap();
            }
            writeln!(&mut f).unwrap();
        }
    }
    write!(&mut f, "    return [state0").unwrap();
    for i in 1..INPUT_WIDTH {
        write!(&mut f, ", state{}", i).unwrap();
    }
    writeln!(&mut f, "]").unwrap();
}

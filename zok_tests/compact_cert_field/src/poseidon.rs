use crate::field::Fp;
use crate::poseidon_constants::*;

fn ark(state: &mut [Fp], c: [Fp; 441], it: usize) {
    for i in 0..state.len() {
        state[i] += c[it + i];
    }
}

fn sbox(state: &mut [Fp], f: usize, p: usize, r: usize) {
    state[0] = state[0] * state[0] * state[0] * state[0] * state[0];
    for i in 1..state.len() {
        state[i] = if (r < f/2) || (r >= f/2 + p) { state[i] * state[i] * state[i] * state[i] * state[i] } else { state[i] };
    }
}

fn mix(state: &[Fp], m: [Fp; 81]) -> Vec<Fp> {
    let mut out = Vec::new();
    for i in 0..state.len() {
        let mut acc = Fp::from(0);
        for j in 0..state.len() {
            acc += state[j] * m[i * 9 + j];
        }
        out.push(acc);
    }
    return out
}

pub fn poseidon(n: usize, inputs: &[Fp]) -> Fp {
    assert!(n > 0 && n <= 5) ;// max 5 inputs

    let t = n + 1;
    let rounds_p = [56, 57, 56, 60, 60, 63, 64, 63];

    let f = 8;
    let p = rounds_p[t - 2];

    // Constants are padded with zeroes to the maximum value calculated by
    // t * (f + p) = 497, where `t` (number of inputs + 1) is a max of 7.
    // This is done to keep the function generic, as resulting array size depends on `t`
    // and we do not want callers passing down constants.
    // This should be revisited once compiler limitations are gone.

    let (c, m) = gen_consts();

    let mut state = vec![Fp::from(0)];
    for i in 1..t {
        state.push(inputs[i - 1]);
    }

    for r in 0..f+p {
        ark(&mut state, c, r * t);
        sbox(&mut state, f, p, r);
        state = mix(&state, m);
    }

    return state[0]
}
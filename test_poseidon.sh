#!/bin/bash
echo "const u32 REPETITION = $1" > zok_tests/benchmarks/poseidon_test/poseidon_const.zok &&
cd circ_blocks &&
target/release/examples/zxc poseidon_test/poseidon_struct
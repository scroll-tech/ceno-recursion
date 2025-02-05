#!/bin/bash
set -euxo pipefail

profile="dev"
#profile="release"

echo "const u32 REPETITION = $1" > zok_tests/benchmarks/poseidon_test/poseidon_const.zok

cd circ_blocks
cargo run --profile="${profile}" --example zxc poseidon_test/poseidon_struct

#!/bin/bash
set -euxo pipefail

(
  cd circ_blocks
  cargo build --release --example zxc --no-default-features --features r1cs,smt,zok,spartan_parallel
)

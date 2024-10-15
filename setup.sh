#!/bin/bash
cd circ_baseline && cargo build --release --example circ --no-default-features --features r1cs,smt,zok,spartan &&
cd ../circ_blocks && cargo build --release --example zxc --no-default-features --features r1cs,smt,zok &&
cd ../spartan_parallel && RUSTFLAGS="-C target_cpu=native" cargo build --release --features multicore,profile --example interface
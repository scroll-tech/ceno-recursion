#!/bin/bash
set -euxo pipefail

cd spartan_parallel
RUST_BACKTRACE=1 \
    cargo run --release \
        --example interface -- ceno_demo/tower_verifier

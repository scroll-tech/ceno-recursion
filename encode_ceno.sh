#!/bin/bash
set -euxo pipefail

cd circ_blocks

cargo run --release \
    --example zxc -- ceno_demo/tower_verifier

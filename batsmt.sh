#!/bin/sh

cargo build --release || exit 1
export RUST_LOG=info
exec ./target/release/batsmt-run $@

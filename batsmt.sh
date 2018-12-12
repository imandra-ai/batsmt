#!/bin/sh

cargo build --release
export RUST_LOG=info
exec ./target/release/batsmt-run $@

#!/bin/sh

cargo build || exit 1

export RUST_BACKTRACE=1
export RUST_LOG=trace
exec ./target/debug/batsmt-run $@

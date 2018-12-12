#!/bin/sh

cargo build

export RUST_BACKTRACE=1
export RUST_LOG=debug
exec ./target/debug/batsmt-run $@

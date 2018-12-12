#!/usr/bin/env bash

if [ -z "$FREQ" ] ; then FREQ=1200 ; fi

perf record -F "$FREQ" --call-graph=dwarf $@

perf script \
  | stackcollapse-perf --kernel \
  | sed 's/batsmt//g' \
  | flamegraph > perf.svg


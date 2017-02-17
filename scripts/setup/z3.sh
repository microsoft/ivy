#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# z3 setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

self=$(basename $0)
gitroot=$(git rev-parse --show-toplevel)
target=$gitroot/submodules/z3/build/z3

if [ ! -x "$target" ]; then
   echo "$self: i couldn't find the z3 executable; rebuilding..."
   cd $gitroot/submodules/z3
   git clean -fdx
   python scripts/mk_make.py
   cd build && make
else
   echo "$self: i found the z3 executable at '$target'; build skipped."
fi


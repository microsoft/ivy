#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# z3 setup script

# exit on any unobserved failure.
set -e

self=$(basename $0)
gitroot=$(git rev-parse --show-toplevel)

case $1 in
    "env")
        echo "# type \`eval \"\$(sh $0 env)\"\` to add the following"
        echo "# to the environment."
        echo "export PATH=$gitroot/submodules/z3/build:\$PATH"
        echo "export LD_LIBRARY_PATH=$gitroot/submodules/z3/build:\$LD_LIBRARY_PATH"
        echo "export PYTHONPATH=$gitroot/submodules/z3/build/python:\$PYTHONPATH"
        ;;
    "build")
        # show what's happening.
        set -x
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
        ;;
    *)
        echo "usage: $self env|build"
esac


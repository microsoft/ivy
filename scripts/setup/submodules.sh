#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# submodule setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

gitroot=$(git rev-parse --show-toplevel)

git submodule init
git submodule update

# this shouldn't do anything if we're using vagrant (see `/scripts/setup/vagrant.sh`).
if [ "x$1" == "x--vagrant" ]; then
   git submodule foreach '$SHELL ../../scripts/setup/git.sh'
fi

$SHELL $gitroot/scripts/setup/z3.sh build

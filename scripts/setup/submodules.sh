#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# submodule setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

git submodule init
git submodule update

# this shouldn't do anything if we're using vagrant (see `/scripts/setup/vagrant.sh`).
if [ "$(pwd)" == "/vagrant" ] && [ "$(whoami)" == "vagrant" ]; then
   git submodule foreach '$SHELL ../../scripts/setup/git.sh'
fi

$SHELL scripts/setup/z3.sh

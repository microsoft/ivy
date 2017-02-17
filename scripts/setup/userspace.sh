#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# userspace setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

gitroot=$(git rev-parse --show-toplevel)

$SHELL $gitroot/scripts/setup/python.sh

if [ "x$1" == "x--vagrant" ] && ! grep -q 'cd /vagrant' $HOME/.profile; then
   echo 'cd /vagrant' >> $HOME/.profile
fi


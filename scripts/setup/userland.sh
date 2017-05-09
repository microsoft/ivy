#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# userland setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

gitroot=$(git rev-parse --show-toplevel)

$SHELL $gitroot/scripts/setup/python.sh

if [ "x$1" = "x--vagrant" ] && ! grep -q 'cd /vagrant' $HOME/.profile; then
   echo 'cd /vagrant' >> $HOME/.profile
   echo 'eval "export PATH=$HOME/.local/bin:$PATH"' >> $HOME/.profile
   echo 'eval "$(sh /vagrant/scripts/setup/z3.sh env)"' >> $HOME/.profile
fi

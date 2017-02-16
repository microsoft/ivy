#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# userspace setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

$SHELL scripts/setup/python.sh

if ! grep -q 'cd /vagrant' $HOME/.profile; then
   echo 'cd /vagrant' >> $HOME/.profile
fi



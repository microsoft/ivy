#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# vagrant bootstrap script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

# this solves a problem with upgrading the `grub-pc` package. see
# https://github.com/mitchellh/vagrant/issues/289
(echo "set grub-pc/install_devices /dev/sda" | debconf-communicate) || true > /dev/null

cd /vagrant

$SHELL ./scripts/setup/debian.sh
sudo -H -u vagrant -- $SHELL ./scripts/setup/userland.sh --vagrant
sudo -H -u vagrant -- $SHELL ./scripts/setup/submodules.sh --vagrant

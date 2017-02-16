#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# debian/ubuntu setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

APT_PACKAGES="vim-tiny git python python-dev python-pip libgmp-dev graphviz graphviz-dev"

apt-get update && apt-get -y upgrade
apt-get -y install $APT_PACKAGES


#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# pip setup script

gitroot=$(git rev-parse --show-toplevel)

PIP_PACKAGES="ipython ply pygraphviz"

pip install --user $PIP_PACKAGES

mkdir -p $HOME/.ipython/nbextensions
rm -f $HOME/.ipython/nbextensions/ivy
ln -s $gitroot/ivy $HOME/.ipython/nbextensions/ivy

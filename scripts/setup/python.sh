#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# pip setup script

gitroot=$(git rev-parse --show-toplevel)

PIP_PACKAGES="ipython[notebook] ply pygraphviz"

# ipython requires a version of pip >= 9.0.1 to function properly with
# python 2.7. see <https://github.com/ipython/ipython/blob/master/README.rst>
pip install --user --upgrade pip
export PATH=$HOME/.local/bin:$PATH

if [ "x$1" = "x--force" ]; then
    force=--force-reinstall
fi

pip install --user --upgrade $force $PIP_PACKAGES

mkdir -p $HOME/.ipython/nbextensions
rm -f $HOME/.ipython/nbextensions/ivy
ln -s $gitroot/ivy $HOME/.ipython/nbextensions/ivy

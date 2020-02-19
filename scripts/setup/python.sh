#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# pip setup script

gitroot=$(git rev-parse --show-toplevel)

# pass `--force` as an argument to force reinstallation of packages.
if [ "x$1" = "x--force" ]; then
    force=--force-reinstall
fi

pip install --user --upgrade $force --editable $gitroot

# there's appears to be a fix for a bug in pygraphviz on debian-based systems
# that hasn't been released yet. the following command works around the issue.
# see <https://github.com/pygraphviz/pygraphviz/issues/71> for more information.
pip install --user --upgrade --force-reinstall pygraphviz --install-option="--include-path=/usr/include/graphviz" --install-option="--library-path=/usr/lib/graphviz/"

# required by ivy_graphviz, which is imported when running the ivy executable
pip install pydot
# begin: ipython support (unmaintainted)
## `ipython[notebook]` requires a version of pip >= 9.0.1 to function properly
## with python 2.7. see <https://github.com/ipython/ipython/blob/master/README.rst>
#pip install --user --upgrade pip
#export PATH=$HOME/.local/bin:$PATH
#pip install --user --upgrade $force ipython[notebook]
#
#mkdir -p $HOME/.ipython/nbextensions
#rm -f $HOME/.ipython/nbextensions/ivy
#ln -s $gitroot/ivy $HOME/.ipython/nbextensions/ivy
# end: ipython support (unmaintainted)

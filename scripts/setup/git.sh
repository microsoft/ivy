#!/bin/sh

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# git repository setup script-- destructive and therefore
# normally only used when setting up git workspaces shared across
# platforms (e.g. vagrant and WSL).

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

self=$(basename $0)
pwd=$(readlink -e $(pwd))

git clean -fdx -e Vagrantfile -e .vagrant
rm -rf vendor

if [ "$(git config core.eol)" != "lf" ]; then
   echo "$self: resetting eol configuration in git repository '$(pwd)'..."
   git config core.eol lf
   git config core.autocrlf input
   git reset --hard
   git checkout-index --force --all
else
   echo "$self: the eol configuration in git repository '$(pwd)' appears correct."
fi

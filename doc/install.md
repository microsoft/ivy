---
layout: page
title: Installing IVy
---
## prerequisites

### python 2.7

Get it from [here](https://www.python.org/downloads) or as part of
your Linux distribution.

### Z3

Following the instructions [here](https://github.com/Z3Prover/z3) to
install Z3. Set the environment variable Z3DIR to the prefix at which
you installed Z3. By defult this is /usr/local, in which case:

    $ export Z3DIR = /usr/local

### Python packages

Install the python packages ply and pygraphviz. On Ubuntu, install them
like this:

    $ sudo apt-get install python-ply python-pygraphviz

### tcl/tk/tcldot

To use the Tk-based user interface, you need to install the python
package tk, the tix widget set, and the tcldot package (part of
graphviz). On Ubuntu, install them all like this:

    $ sudo apt-get install python-tk tix libgv-tcl

## install

Get the source like this:

    $ git clone https://github.com/Microsoft/ivy.git

Set the environment variable IVYDIR to point to the root of Ivy's
source tree, like this:

    $ cd ivy
    $ export IVYDIR=`pwd`

Add Ivy's bin directory to your path, like this:

    $ export PATH=`pwd`/bin:$PATH

## run

Run Ivy on an example, using the Tcl/Tk user interface:

    $ cd examples/ivy
    $ ivy client_server.ivy

## emacs mode

An emacs major mode for Ivy is available in lib/emacs/ivy-mode.el. Put this file
somewhere in your emacs load path and add the following code to your
.emacs:

    (add-to-list 'auto-mode-alist '("\\.ivy\\'" . ivy-mode))
    (autoload 'ivy-mode  "ivy-mode.el" "Major mode for editing Ivy code" t nil)





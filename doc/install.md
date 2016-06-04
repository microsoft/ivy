---
layout: page
title: Installing IVy
---
## Prerequisites

### Python 2.7

Get it from [here](https://www.python.org/downloads) or as part of
your Linux distribution. You should make sure to get the `pip`
utility.  This is standard on versions from 2.7.9.

You can install IVy in a python virtual environment if you don't want
to pollute your local python setup. Before the following instructions,
do this:

    $ pip install virtualenv
    $ virtualenv ivy_env
    $ cd ivy_env
    $ . bin/activate

### Z3

Following the instructions [here](https://github.com/Z3Prover/z3) to
install Z3. You can test whether Z3 is correctly installed like this:

    $ python
    >>> import z3

If you want to install Z3 in a virtual environment, you can install Z3
like this:

    $ make install PREFIX=/path/to/ivy_env

### Python packages

Install the python packages ply, pygraphviz and tarjan. On Ubuntu, install them
like this:

    $ sudo apt-get install python-ply python-pygraphviz
    $ pip install tarjan

As an alternative, pip can install all the packages, but you need to make sure
the dependencies on system packages are met:

    $ sudo apt-get install graphviz graphviz-dev python-dev
    $ pip install ply pygraphviz tarjan

This latter is the option if you are making a virtual environment.

### Tcl/Tk/Tix

To use the Tk-based user interface, you need to install the python
package tk, and the tix widget set. On Ubuntu, install them like
this:

    $ sudo apt-get install python-tk tix

## Install IVy

Get the source like this:

    $ git clone https://github.com/Microsoft/ivy.git
    $ cd ivy

Install into your local Python like this

    $ sudo python setup.py install

If you want to run from the source tree for development purposes, do
this instead:

    $ sudo python setup.py develop

If you don't want to do a system-wide install (and you aren't using a
virtual environment) there are various ways to install in your home
directory. For example:

    $ python setup install --home=~

See the [python documenation](https://docs.python.org/2/install/) for
general instructions on installing python packages.

## Run

Run Ivy on an example, like this:

    $ cd doc/examples
    $ ivy client_server_example.ivy

## Emacs mode

An emacs major mode for Ivy is available in lib/emacs/ivy-mode.el. Put this file
somewhere in your emacs load path and add the following code to your
.emacs:

    (add-to-list 'auto-mode-alist '("\\.ivy\\'" . ivy-mode))
    (autoload 'ivy-mode  "ivy-mode.el" "Major mode for editing Ivy code" t nil)





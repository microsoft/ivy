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

## Windows notes

Installing on windows can be a bit challenging, but here are a few
suggestions that may get you throuhg it.

### Installing Python and Python packages

Install Python 2.7.11 in the normal way. Before installing packages, you may also
need to install the [Visual C++ compiler for Python](http://aka.ms/vcpython27).

### Installing Z3

After installing Z3, you need to make sure Python can find it. You can try setting
the PYTHONPATH environment variable to point to the Z3 `bin` directory. It might
help to make sure Z3 is installed in a directory without spaces in the name. As a
last resort, you can just copy the '.py' and '.dll' files into your Python installation.
If you installed Python in `c:/Python27`, then copy the files into:

    c:/Python27/lib/site-packages/

If things are installed correctly, the following should produce no errors:

    > python
    >>> import z3
    >>> z3.init('libz3.dll')

### Installing Graphviz

Get `graphviz-2.38` from [graphviz.org](http://graphviz.org). This site is often down,
so you may have to be patient. Versions downloaded from alternative sites may be broken.
Install into some directory without spaces in the name, for example `c:/Graphviz`.

### Using scripts

The `pip` package installation utility is found in `c:/Python27/Scripts`. You should put
this directory in your PATH, since the IVY command line scripts will also be installed there
by default. Try installing the `tarjan` and `ply` packages like this:

    > pip install tarjan
    > pip install ply

### Installing Pygraphviz

You can try installing `pygraphviz` like this:

    > pip install pygraphviz

However, this is likely to fail as pip will not find the graphviz
headers and libraries. As an alternative, download the release 1.3 of
pygraphviz from
[here](https://github.com/pygraphviz/pygraphviz/releases). After unpacking
the sources, do this:

    > cd pygraphviz-pygraphviz-1.3
    > python setup.py install --include-path=c:/Graphviz/include --library-path=c:/Graphviz/lib/debug/lib

This tells explicitly where you installed the graphviz headers and libraries. If this seems to
work, you can test it like this:

    > python
    >>> import pygraphviz.agraph

### Installing Ivy

Now you can now try to install Ivy, like this:

    > git clone https://github.com/Microsoft/ivy.git
    > cd ivy
    > python setup.py install

If you have put `c:/Python27/Scripts` in your `PATH`, you should now be able to run IVy like this:

    > ivy ui=cti doc/examples/client_server_example.ivy




 
---
layout: page
title: Installing IVy
---

There are two ways to install ivy:

1. [Install from source](#source)
2. [Install a binary release](#binary)

<a name="source"></a> Installing from source
--------------------------------------------

1. [Install from source on Linux](#linuxnotes)
2. [Install from source on Windows](#windowsnotes)
3. [Install from source on Mac](#macnotes)


<a name="source"></a> Installing a binary release
--------------------------------------------

1. [Install from source on Linux](#linuxbinary)


<a name="linuxnotes"></a> Installation from source on Linux
===========================================================

This describes the steps need to install IVy on Ubuntu 18.04. This may
also work on other Debian-based distributions.

### Prerequisites

    $ sudo apt-get install python python-pip g++ cmake python-ply python-pygraphviz git python-tk tix pkg-config

### Install IVy

Get the source like this:

    $ git clone --recurse-submodules https://github.com/Microsoft/ivy.git
    $ cd ivy

Build the submodules like this (it takes a while):

    $ python build_submodules.py

Install into your local Python like this:

    $ sudo python setup.py install

If you want to run from the source tree for development purposes, do
this instead:

    $ export PYTHONPATH=~/lib/python2.7/site-packages:$PYTHONPATH
    $ python setup.py develop --prefix=~

This installs Ivy into your home directory, so you don't need sudo.
Also put the first command in your .profile script, so Python will
find Ivy in the future.

See the [python documentation](https://docs.python.org/2/install/) for
general instructions on installing python packages.

### Run

Run Ivy on an example, like this:

    $ cd doc/examples
    $ ivy client_server_example.ivy

Or, if you only want to use Ivy on the command line, test it like this:

    $ ivy_check trace=true doc/examples/client_server_example_new.ivy
    
Ivy should print out a counterexample trace.

### Emacs mode

An emacs major mode for Ivy is available in `lib/emacs/ivy-mode.el`. Put this file
somewhere in your emacs load path and add the following code to your
`.emacs`:

    (add-to-list 'auto-mode-alist '("\\.ivy\\'" . ivy-mode))
    (autoload 'ivy-mode  "ivy-mode.el" "Major mode for editing Ivy code" t nil)

<a name="windowsnotes"></a> Windows installation from source
============================================================

Installing on from source on Windows can be a bit challenging, but here are a few
suggestions that may get you through it.

### Installing Python and Python packages

Install Python 2.7.11 in the normal way. Before installing packages, you may also
need to install the [Visual C++ compiler for Python](http://aka.ms/vcpython27).

### Installing Z3

Install Z3 using the instructions [here](https://github.com/Z3Prover/z3/wiki/Using-Z3Py-on-Windows).
We will assume that you havce installed Z3 in `c:\z3`. If not, modify the instructions below accordingly.
Make sure to follow the instructions on setting the environmenet variables `PATH` and `PYTHONPATH`.
In addition, set environment variable `Z3DIR` to `c:\z3`.

If things are installed correctly, the following should produce no errors:

    > python
    >>> import z3

### Installing Graphviz

You only need graphviz to use the Ivy GUI. For normal verification and
testing tasks, you don't need this.  Get `graphviz-2.38` from
[graphviz.org](http://graphviz.org). This site is often down, so you
may have to be patient. Versions downloaded from alternative sites may
be broken.  Install into some directory without spaces in the name,
for example `c:/Graphviz`.

### Using scripts

The `pip` package installation utility is found in `c:/Python27/Scripts`. You should put
this directory in your `PATH`, since the IVY command line scripts will also be installed there
by default. Try installing the `tarjan` and `ply` packages like this:

    > pip install tarjan
    > pip install ply

### Installing Ivy

Now you can now try to install Ivy, like this:

    > cd c:\
    > git clone https://github.com/Microsoft/ivy.git
    > cd ivy
    > python setup.py develop

Using the `develop` command instead of `install` is helpful, since you
then don't have to install again after each time you modify the code
or pull a new version.  If you have put `c:/Python27/Scripts` in your
`PATH`, you should now be able to run IVy like this:

    > ivy ui=cti doc/examples/client_server_example.ivy

Or, if you only want to use Ivy on the command line, test it like this:

    > ivy_check trace=true doc/examples/client_server_example_new.ivy
    
Ivy should print out a counterexample trace.

To be able to compile Ivy programs or Ivy testers, you also need to
have some verison of Visual Studio installed. At a minimum you need the
command line build tools for C++ installed. You can get them free of charge
[here](https://visualstudio.microsoft.com/downloads/). 

<a name="macnotes"></a> Installation from source on MacOS High Sierra and Mojave
================================================================================

1. Install Xcode from App Store
2. Install Xcode command line tools

    xcode-select --install

3. Install Xserver

    - [https://www.xquartz.org](https://www.xquartz.org)

4. Macports

        $ sudo xcodebuild -license

   Install Macports from [https://www.macports.org/install.php](https://www.macports.org/install.php). Select
   matching macOS 10.12 or 10.13 depending on macOS running on
   machine.  On macOS 10.13 Mojave, make sure you've installed all
   patches because various steps below were broken until about
   7/15/2019 patch.

        $ sudo easy_install pip (required on 10.13 Mojave and/or required by 8/1/2019)
        $ sudo port install graphviz-gui
        $ sudo port select --set python python27
        $ sudo port select --set python2 python27
        $ sudo pip install pygraphviz --install-option="--include-path=/opt/local/include" --install-option="--library-path=/opt/local/lib"
        $ sudo port install Tix
        $ sudo port install py27-ply
        $ sudo port install py27-ipython
        $ sudo port install py27-tkinter # for 10.13 Mojave
        $ sudo port install git

5. Install Ivy:

    $ git clone --recurse-submodules https://github.com/Microsoft/ivy.git
    $ cd ivy

    Build the submodules like this (it takes a while):

        $ python build_submodules.py

    Install into your local Python like this

        $ sudo python setup.py install

    If you want to run from the source tree for development purposes, do
    this instead:

        $ export PYTHONPATH=~/lib/python2.7/site-packages:$PYTHONPATH
        $ python setup.py develop --prefix=~

    This installs Ivy into your home directory, so you don't need sudo.
    Also put the first command in your .profile script, so Python will
    find Ivy in the future.

    See the [python documentation](https://docs.python.org/2/install/) for
    general instructions on installing python packages.


6. running a test

        $ cd doc/examples
        $ ivy_check diagnose=true client_server_example.ivy


<a name="release"></a> Binary releases
--------------------

Ivy is released as a Python package in the PyPI repository.

### <a name="linuxbinary"> Install binary release on Linux

    $ sudo apt-get install python python-pip g++ python-ply python-pygraphviz python-tk tix
    $ sudo pip install ms-ivy

Note, if you omit `sudo` in the second command, Ivy will be installed into `~\.local\bin`.
In this case, you should put this directory in your `PATH`. 

This does not install the documentation and example files. You can get
these from github like this (see the directory `ivy\doc`):

    $ sudo apt-get install git
    $ git clone https://github.com/Microsoft/ivy.git


### <a name="windowsbinary"> Install binary release on Windows

Windows binary distributions are not yet available.

### <a name="macbinary"> Install binary release on Mac

Mac binary distributions are not yet available.

 

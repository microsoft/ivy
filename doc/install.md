---
layout: page
title: Installing IVy
---

There are three ways to install ivy:

1. [Install a binary release](#release)
2. [Install from source in a virtual environment with Vagrant](#vagrant)
3. [Install from source](#source)

The last two are preferred, since releases are infrequent.

<a name="release"></a> Installing a release
--------------------

Binary releases of IVy are available 
on [IVy's Github release page](https://github.com/Microsoft/ivy/releases).

### Linux

On Debian-based linux ditributions such as Ubuntu, download and
install the file `ms-ivy_X.X_YYYY.deb` where `X.X` is the IVy version and
`YYYY` is the machine architecture. Use your system's package manager to
install this package, or the following commands:

    $ sudo dpkg -i ms-ivy_X.X_YYYY.deb
    $ sudo apt-get install -f

The first command will report missing dependencies, which will be
installed by the second command.

### Windows

The Windows binary distribution is in the form of a zip
archive. Download the file `ivy.X.Y-.Windows-z86.zip`, where `X.X` is
the IVy version (this will work on both 32-bit and 64 bit Intel
Windows). Use Windows Explorer to extract this archive in the
directory `C:\`. This should give you a directory `C:\ivy`. To use IVy
in a command window, first execute this command:

    > C:\ivy\scripts\activate

### Mac

There currently is no binary distribution for Mac. Use instead the
virtual machine approach or an installation from source, as described
below.

<a name="vagrant"></a> Installing in a virtual environment with Vagrant
------------------------------------------------

IVy users and contributors may also deploy IVy within a container
using [Vagrant](https://www.vagrantup.com/).

### Windows

On Windows, [Virtualbox](https://virtualbox.org) is currently the recommended container provider.

1. Clone the `IVy` repository (e.g. `git clone https://github.com/Microsoft/ivy.git`).
2. Download and install [Vagrant](https://www.vagrantup.com/).
3. Download and install [Virtualbox](http://virtualbox.org).
4. Type `vagrant plugin install vagrant-vbguest` to install the [`vagrant-vbguest`](https://github.com/dotless-de/vagrant-vbguest) plugin (optional but recommended).
5. Download and install an X11 server for Windows (e.g. [Xming](http://www.straightrunning.com/XmingNotes/)).
6. Type `vagrant up` [from an administrator console](https://github.com/mitchellh/vagrant/issues/3854) to prepare a new development environment. This is likely to take some time to complete the first time it is done, because [z3](https://github.com/Z3Prover/z3) must be compiled from its sources.
7. Launch your X11 server and type `vagrant ssh` in a console window to get access to IVy from a shell within the container.

### Linux

On Linux, [Docker](https://docker.com) is also available as a container provider, and will yield better performance than the Virtualbox backend.

1. Clone the `IVy` repository (e.g. `git clone https://github.com/Microsoft/ivy.git`).
2. Install [Vagrant](https://www.vagrantup.com/).
3. Install [Docker](https://docker.com).
4. (Debian-based systems) Ensure your user is in the `docker` group.
5. Type `vagrant up --provider=docker`.
6. Type `vagrant ssh` to get access to IVy from a shell.

Linux users also have the option of directly executing the provisioning scripts in the `scripts/setup` directory, bypassing any inconvenience a container might impose. The scripts are divided in such a way as to facilitate this. Those interested should take note, however, that the scripts have only been tested with Ubuntu and Debian Vagrant guest images so far.


### MacOS

- MacOS installation instructions should be similar to the Windows instructions, with the exception that [an X11 server for MacOS](https://www.xquartz.org/) should be used.
- Docker support may work in MacOS as it does in Linux with little-or-no modification but whether this is indeed the case remains unconfirmed at the time of this writing.


<a name="source"></a> Installing from source
--------------------------------------------

This document describes the steps need to install IVy from the Github
repository. The specific commands given apply to Ubuntu Linux version
14.04. Windows and Mac users should also refer to the [Windows](#windowsnotes) and [Mac](#macnotes)
notes below.
 
### Prerequisites

#### Python 2.7

Get it from [here](https://www.python.org/downloads) or as part of
your Linux distribution. You should make sure to get the `pip`
utility.  This is standard on versions from 2.7.9.

You can install IVy in a python virtual environment if you don't want
to pollute your local python setup. If you want to use a virtual
environment, do the following before following the remaining
installation instructions:

    $ pip install virtualenv
    $ virtualenv ivy_env
    $ cd ivy_env
    $ . bin/activate

#### Z3

Follow the instructions [here](https://github.com/Z3Prover/z3) to
install Z3. You can test whether Z3 is correctly installed running this:

    $ python
    >>> import z3

If you want to install Z3 in a virtual environment, you can install Z3
like this:

    $ make install PREFIX=/path/to/ivy_env

#### Python packages

Install the python packages `ply`, `pygraphviz` and `tarjan`. On Ubuntu, install them
like this:

    $ sudo apt-get install python-ply python-pygraphviz
    $ pip install tarjan

To use the IVy command line tools only, there is no need to install `python-pygraphviz`.

Make sure you get version 3.4 of python-ply as some later versions are broken.
As an alternative, `pip` can install all the packages, but you need to make sure
the dependencies on system packages are met:

    $ sudo apt-get install graphviz graphviz-dev python-dev pkg-config
    $ pip install ply pygraphviz tarjan

This latter is the option if you are making a virtual environment.

#### Tcl/Tk/Tix

To use the Tk-based user interface, you need to install the python
package tk, and the tix widget set. On Ubuntu, install them like
this:

    $ sudo apt-get install python-tk tix

This step is not necessary if using the IVy command line tools only.


### Install IVy


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

    $ python setup.py install --home=~

See the [python documentation](https://docs.python.org/2/install/) for
general instructions on installing python packages.

### Run

Run Ivy on an example, like this:

    $ cd doc/examples
    $ ivy client_server_example.ivy

### Emacs mode

An emacs major mode for Ivy is available in `lib/emacs/ivy-mode.el`. Put this file
somewhere in your emacs load path and add the following code to your
`.emacs`:

    (add-to-list 'auto-mode-alist '("\\.ivy\\'" . ivy-mode))
    (autoload 'ivy-mode  "ivy-mode.el" "Major mode for editing Ivy code" t nil)

<a name="windowsnotes"></a> Windows notes
-------------

Installing on Windows can be a bit challenging, but here are a few
suggestions that may get you through it.

### Installing Python and Python packages

Install Python 2.7.11 in the normal way. Before installing packages, you may also
need to install the [Visual C++ compiler for Python](http://aka.ms/vcpython27).

### Installing Z3

After installing Z3, you need to make sure Python can find it. You can try setting
the `PYTHONPATH` environment variable to point to the Z3 `python` directory. It might
help to make sure Z3 is installed in a directory without spaces in the name. As a
last resort, you can just copy the `python/z3` directory into your Python installation.
If you installed Python in `c:/Python27`, then copy it into:

    c:/Python27/lib/site-packages/z3

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
this directory in your `PATH`, since the IVY command line scripts will also be installed there
by default. Try installing the `tarjan` and `ply` packages like this:

    > pip install tarjan
    > pip install ply

### Installing Pygraphviz

You can try installing `pygraphviz` like this:

    > pip install pygraphviz

However, this is likely to fail as `pip` will not find the graphviz
headers and libraries. As an alternative, download the release 1.3 of
`pygraphviz` from
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

<a name="macnotes"></a> Mac notes
--------------------------------

There are two options for Mac users: using the native Aqua interface
or X11. Here we will describe the X11 approach.

### XQuartz

Install [XQuartz](https://www.xquartz.org).

### MacPorts

Install [MacPorts](https://www.macports.org).

### Install prerequisites

    $ sudo port install graphviz python27 py27-pip py27-pygraphviz py27-ply py27-tkinter tix git
    $ sudo pip install tarjan

### Install Z3

    $ unzip z3-4.4.1-x64-osx-10.11.zip
    $ export PYTHONPATH=`pwd`/z3-4.4.1-x64-osx-10.11/bin:

### Install IVy

    $ git clone https://github.com/Microsoft/ivy.git
    $ cd ivy
    $ sudo python2.7 setup.py install
    $ export PATH="/opt/local/Library/Frameworks/Python.framework/Versions/2.7/bin:$PATH"

The last command is to make the ivy command-line scripts
available. For some reason, the first time you run ivy, it takes
several minutes to start.

### Aqua Python

In principle, it is also possible to use the native Aqua interface by
installing an appropriate python package. In this case, you might
install `graphviz` using MacPorts, and then install `pygraphviz` from
source as in the Windows notes above. This is untested, however.

 

---
layout: page
title: Installing IVy
---

There are two ways to install ivy, in order of preference:

1. [Install from source](#source)
2. [Install from source in a virtual environment with Vagrant](#vagrant)

<a name="source"></a> Installing from source
--------------------------------------------

1. [Install from source on Linux](#linuxnotes)
2. [Install from source on Windows](#windowsnotes)
3. [Install from source on Mac](#macnotes)


<a name="linuxnotes"></a> Installation from source on Linux
===========================================================

This describes the steps need to install IVy from the Github
repository on Linux. The specific commands given apply to Ubuntu Linux version
18.04. 

### Prerequisites

#### Python 2.7

Get it from [here](https://www.python.org/downloads) or as part of
your Linux distribution. On Ubuntu, do this:

    sudo apt-get install python

You should make sure to get the `pip` utility.  This is standard on
python versions from 2.7.9. If `which pip` doesn't produce any result,
do this:

    sudo apt-get install python-pip

You can install IVy in a python virtual environment if you don't want
to pollute your local python setup. If you want to use a virtual
environment, do the following before following the remaining
installation instructions:

    $ pip install virtualenv
    $ virtualenv ivy_env
    $ cd ivy_env
    $ . bin/activate

#### GCC

You need to have a C++ compiler installed. If you don't already have one, do this:

    sudo apt-get install g++


    
and put the above command in `~/.profile` as well.

Now test your installation like this:

    $ python
    >>> import z3

If you don't get an error message, Z3 may be installed. If you do get
an error message, it definitely isn't.

If you don't want to do a system-wide installation, you can find some
instructions
[here](http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/SMT____Z3-INSTALLATION). If
you follow these instructions, then also do this:

    export Z3DIR=$HOME/usr
    
and put the above command in your .profile as well.


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


6. running test

        $ cd doc/examples
        $ ivy_check diagnose=true client_server_example.ivy


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



<a name="release"></a> Binary releases
--------------------

Some old binary releases of IVy are available 
on [IVy's Github release page](https://github.com/Microsoft/ivy/releases). New binary releases are not being created however.

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

There currently is no binary distribution for Mac. 

 

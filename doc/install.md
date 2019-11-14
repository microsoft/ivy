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
In fact, be careful *not* to use sudo when installing in your home
directory, as the files will be owned by root. Also put the first
command in your .profile script, so Python will find Ivy in the
future.

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

Installing on from source on Windows can be a bit challenging, but here are a few
suggestions that may get you through it.

<a name="windowsdeps"></a> Windows prerequisites
=================================================

### Security exceptions

If you want to compile programs or testers in Ivy, you may need to
install a security exception to prevent the antivirus software from
scanning your programs each time they are run (which makes startup of
programs very slow). This is a generic problem with compiling binary
code on Windows. If you are using Windows 10 and your antivirus is
Windows defender, exceptions are found under Start > Settings > Update
& Security > Windows Security > Virus & Threat Protection > Virus &
Threat Protection Settings > Manage Settings. Add an exception for the
directory in which you plan to do development. This should cover all
subdirecties as well. If you just want to do verification without
compiling, this step is not necessary.

### Visual studio

Install Visual Studio 2019. You may be able to get away with other
versions of the Visual Studio compiler tools, but only Visual Studio
2019 is documented here.  Some free tools that might be helpful are
available [here](https://visualstudio.microsoft.com/downloads/).

### Python and Python packages

Install Python 2.7.11 in the normal way. Make sure to install 64-bit
Python. Install Python in `c:/Python27` and put `c:/Python27` in your
PATH.

The `pip` package installation utility is found in `c:/Python27/Scripts`. You should put
this directory in your `PATH`, since the IVY command line scripts will also be installed there
by default. Try installing the `tarjan` and `ply` packages like this:

    > pip install tarjan
    > pip install ply

### Graphviz

You only need graphviz to use the Ivy GUI. For command line verification and
testing tasks, you don't need this.  Get `graphviz-2.38` from
[graphviz.org](http://graphviz.org). Install into some directory
without spaces in the name, for example `c:/Graphviz2.38`. Make sure that
`c:/Graphviz2.38/bin` is in your `PATH`.

### OPENSSL

OpenSSL binaries for Windows can be found
[here](https://slproweb.com/products/Win32OpenSSL.html).  You need the
full 64-bit version. Be sure to install in the default directory
`c:\OpenSSL-Win64`. These OpenSSL binaries are missing a file
`include/ms/applink.c`. Do this:

    > mkdir c:\OpenSSL-Win64\include\ms
    > copy c:\OpenSSL-Win64\include\openssl\applink.c c:\OpenSSL-Win64\include\ms

You also need to copy the libcrypto DLL into someplace the system will
find it:

    > copy c:\OpenSSL-Win64\libcrypto-1_1-x64.dll c:\Windows\SysWOW64\

### Windows SDK

Install Windows SDK version 10.0.14393.0 from
[here](https://developer.microsoft.com/en-us/windows/downloads/sdk-archive). You
have to get exactly this version, even if you have a newer
version. The windows build tool is very fussy about this. Note, this
version number may change. You'll get an error mesage when compiling
if it does. Install the version that it asks for.

<a name="windowsnotes"></a> Windows installation from source
============================================================

### Installing Ivy

First, install the [Windows prerequisites](#windowsdeps).

### Install git

Install git from [here](https://gitforwindows.org). If you install it
in `c:/Git`, then put `c:\Git\cmd` in your `PATH`.

### Install Ivy

    > cd c:\
    > git clone https://github.com/Microsoft/ivy.git
    > cd ivy
    > git submodule init
    > git submodule update
    > python build_submodules
    > python setup.py develop

Using the `develop` command instead of `install` is helpful, since you
then don't have to install again after each time you modify the code
or pull a new version.  If you have put `c:/Python27/Scripts` in your
`PATH`, you should now be able to run IVy like this:

    > ivy ui=cti doc/examples/client_server_example.ivy

Or, if you only want to use Ivy on the command line, test it like this:

    > ivy_check trace=true doc/examples/client_server_example.ivy
    

<a name="macnotes"></a> Installation from source on MacOS High Sierra and Mojave
================================================================================

These instructions have been tested for macOS 10.12 Sierra up to macOS
10.15 Catalina.

1. Install Xcode from App Store
2. Install Xcode command line tools

        xcode-select --install

3. Install Xserver

    - [https://www.xquartz.org](https://www.xquartz.org)

4. Macports

        $ sudo xcodebuild -license

   Install Macports from [https://www.macports.org/install.php](https://www.macports.org/install.php). Select
   the version matching The macOS matching the macOS version running on your
   machine.  On macOS 10.13 Mojave, make sure you've installed all
   patches because various steps below were broken until about
   7/15/2019 patch.

        $ sudo easy_install pip  # required on 10.13 Mojave and/or required by 8/1/2019)
        $ sudo port install graphviz-gui
        $ sudo port select --set python python27
        $ sudo port select --set python2 python27
        $ sudo pip install pygraphviz --install-option="--include-path=/opt/local/include" --install-option="--library-path=/opt/local/lib"
        $ sudo port install Tix
        $ sudo port install py27-ply
        $ sudo port install py27-ipython
        $ sudo port install py27-tkinter # for 10.13 Mojave
        $ sudo port install git
        $ sudo port install cmake

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


<a name="binary"></a> Binary releases
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

First, install the [Windows prerequisites](#windowsdeps).

Then install the Ivy binaries:

    > pip install ms-ivy

This does not install the documentation and example files. You can get
these from the source repository. See [Windows installation from
source](#windowsnotes).

### <a name="macbinary"> Install binary release on Mac

Mac binary distributions are not yet available.

 

# ivy

IVy is a research tool intended to allow interactive development of
protocols and their proofs of correctness and to provide a platform
for developing and experimenting with automated proof techniques. In
particular, IVy provides interactive visualization of automated
proofs, and supports a use model in which the human protocol designer
and the automated tool interact to expose errors and prove
correctness.

## prerequisites

### python 2.7

Get it from [here](https://www.python.org/downloads) or as part of
your Linux distribution.

### Z3

Following the instructions [here](https://github.com/Z3Prover/z3) to
install Z3. Set the environment variable Z3DIR to the prefix at which
you installed Z3. By defult this is /usr/local, in which case:

    $ export Z3DIR = /usr/local

### tcldot

This is needed to run the Tcl/Tk-based user interface. You do not need
this to use the browser-based user interface or the command-line
interface. On Ubuntu, install it like this:

    $ sudo apt-get install libgv-tcl

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





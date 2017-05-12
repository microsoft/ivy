# ivy

IVy is a research tool intended to allow interactive development of
protocols and their proofs of correctness and to provide a platform
for developing and experimenting with automated proof techniques. In
particular, IVy provides interactive visualization of automated
proofs, and supports a use model in which the human protocol designer
and the automated tool interact to expose errors and prove
correctness.

## Installation

### Releases

A pre-release Windows installer is available on [IVy's Github release page](https://github.com/Microsoft/ivy/releases).

### Vagrant

IVy users and contributors may also deploy IVy within an container using Vagrant.

#### Windows

On Windows, [Virtualbox](http://virtualbox.org) is currently the recommended container provider.

1. Clone the `IVy` repository (e.g. `git clone https://github.com/Microsoft/ivy.git`).
2. Download and install [Vagrant](http://vagrantup.com).
3. Download and install [Virtualbox](http://virtualbox.org).
4. Type `vagrant plugin install vagrant-vbguest` to install the [`vagrant-vbguest`](https://github.com/dotless-de/vagrant-vbguest) plugin (optional but recommended).
5. Download and install an X11 server for Windows (e.g. [Xming](http://www.straightrunning.com/XmingNotes/)).
6. Type `vagrant up` [from an administrator console](https://github.com/mitchellh/vagrant/issues/3854) to prepare a new development environment. This is likely to take some time to complete the first time it is done, because [z3](https://github.com/Z3Prover/z3) must be compiled from its sources.
7. Launch your X11 server and type `vagrant ssh` in a console window to get access to IVy from a shell within the container.

#### Linux

On Linux, [Docker](http://docker.com) is also available as a container provider, and will yield better performance than the Virtualbox backend.

1. Clone the `IVy` repository (e.g. `git clone https://github.com/Microsoft/ivy.git`).
2. Install [Vagrant](http://vagrantup.com).
3. Install [Docker](http://docker.com).
4. (Debian-based systems) Ensure your user is in the `docker` group.
5. Type `vagrant up --provider=docker`.
6. Type `vagrant ssh` to get access to IVy from a shell.

Linux users also have the option of directly executing the provisioning scripts in the `scripts/setup` directory, bypassing a container. Those interested should take note that the scripts have only been tested with Ubuntu and Debian Vagrant guest images.

#### MacOS

- MacOS installation instructions should be similar to the Windows instructions, with the exception that [an X11 server for MacOS](https://www.xquartz.org/) should be used.
- Docker support for may function in MacOS but this remains unconfirmed at the time of this writing.

## Further Reading

For further information on IVy, see [the IVy web site](http://microsoft.github.io/ivy/).





Specification-based testing of QUIC
-----------------------------------

This directory contains work on a formal specification of the QUIC
protocol in the Ivy language. This specification can be used to test
implementations of QUIC using compositional specification-based
testing methods.  The currently targeted version is IETF draft 18, as
described in
[this document](https://tools.ietf.org/html/draft-ietf-quic-transport-18).

The specification is written in a way that allows monitoring of
packets on the wire, as well as modular testing of implementations.
That is, from the specification we can produce an automated tester
that takes one role in the protocol. The tester uses symbolic execution
and an SMT solver to randomly generate protocol traffic that
complies with the specification. For example, if the tester is taking
the client role, it generates packets that are legal for the client to
send, and these are transmitted to the server being tested. The
responses sent by the server are then checked for compliance with the
specification.

This approach has certain advantages when compared to interoperablilty
testing. First, the specification-based tester can generate stimulus
that can't be produced by any current implementation and perhaps would
only be produced by attackers. Because it is randomized, it tends to
generate the unusual cases that specifiers may not have
considered. Second, it checks for actual specification compliance and
not just for correct interopation. Ensuring compliance to the
specification can be helpful for future protocol developers who have
deal with compatibility with legacy implementations.

In addition, the formal specification can be seen as
documentation, since it gives an unambiguous interpretation of
statements made in natural language in the IETF specification
documents.

A guide to the specification
============================

The specification is given in terms of a set of protocol events or
"actions" in the Ivy language. These events abstractly represent
occurrences at various layers of the protocol stack, for example, the
transmission of a QUIC packet, or the transfer of data to or from an
application. To each of these events are attached *monitors*. The
monitors assert requirements on the events that determine protocol
compliance and also record history information by updating shared
variables. This information makes it possible to specify legal
sequences of events, and also to specify the required relationships
between events occurring at different protocol layers.

The protocol can be though of as composed of multiple layers. From top
to bottom: Application, Security, Frame, Packet, Protection and
Datagram (UDP).  The specification: is divided into files correspoding
to these layers:

- Application: quic_application.ivy
- Security: quic_security.ivy
- Frame: quic_frame.ivy
- Packet: quic_packet.ivy
- Protection: quic_protection.ivy

At each layer, we define necessary data types, state variables, and
actions. Each action has a specification in terms of a *before* clause
(its guard or precondition) and an *after* (its state update). The
exception is the protection layer which simply provides procedures for
encrypting and decrypting packets.

Some additional files:
- Byte-level encoding of packets: quic_ser.ivy
- Byte-level decoding of packets: quic_deser.ivy

The packet encoding and decoding are currently implemented in C++.

The Ivy language used to express the specification is described
[here](http://microsoft.github.io/ivy/language.html). An example of
using Ivy for specification-based tesing can be found
[here](http://microsoft.github.io/ivy/examples/testing/intro.html).

The specification is intended to be a "literate" document, containing
a natural language description of the protocol, interleaved with the
formal description. This is somewhat a work in progress, however, with
some aspects more clearly documented than others.

The specification as it stands has a number of limitations. First, it
covers only a subset of features of QUIC. Currently, enough features
are covered for the test client to have a successful dialog with
server implementations, but much work remains to be done in specifying
all of the protocol features. Second, the specification does not deal
with quantitative time, meaning certain aspects of the QUIC
specification relating to transmission rates and timeouts can't be
stated. 

The remainder of this document describes how to use the 
specification to test implementations.


Installation steps
==================

In the sequel, "this directory" means the directory containing the
file you are reading (relative to the root of the Ivy tree, it is
`doc/examples/quic`).

First, Ivy must be installed, as described
[here](http://microsoft.github.io/ivy/install.html).     
After you have finished with the Ivy installation, do the following
steps just one a given machine.

### Make a build and a temp directory

If there are no directories `build` and `test/temp` in "this
directory", create them now:

    $ mkdir build
    $ mkdir test/temp

### Install some packages

    $ pip install pexpect

### Build the server tester

There are various testers available that generate different sorts of
traffic for the server. The most basic one is
`quic_server_test_stream.ivy`, in "this directory". Build it like this

    ivyc target=test quic_server_test_stream.ivy

If successful, this will produce a binary file
`build/quic_server_test_stream`.

Other testers you can build are:

    quic_server_test_max.ivy
    quic_server_test_connection_close.ivy
    quic_client_test_stream.ivy
    quic_client_test_max.ivy

Implementations of QUIC
-----------------------

### picoquic

Source code and build instructions:

    https://github.com/private-octopus/picoquic
    
To get draft 18 of the QUIC standard, use this commit
before updating submodules:

    git checkout 95dd82f
    

Run a server:

    ./picoquicdemo -L -l -
    
Run a client:

    ./picoquicdemo localhost
    
### quant

Source code and build instructions:

    https://github.com/NTAP/quant

To run the quant server in "this directory":

    $QUANT_DIR/Debug/bin/server -d . -c leaf_cert.pem -k leaf_cert.key -p 4443
    
    
### MinQUIC

#### Steps to get started with MinQUIC

- Install the [go language](https://golang.org/doc/install) on your platform.
- Follow the instructions [here](https://github.com/ekr/minq) to install MinQUIC.

##### Go installation notes:

Some instructions for installing specifically on Ubuntu are
[here](https://github.com/golang/go/wiki/Ubuntu). Note that you need
to make sure that the go binary is in your path, and do this:

    $ cd ~
    $ mkdir go
    $ cd go
    $ mkdir src
    $ export GOPATH=`pwd`
    $ echo export GOPATH=`pwd` >> ~/.profile 

##### MinQUIC installation notes

To get MinQUIC running, this command may be helpful:

    cd $GOPATH/src
    go get github.com/cloudflare/cfssl/helpers

### Google QUIC

The Google implementation of QUIC is part of Chromium code base, and
is supposed to be IEFT compatible if you used version 99. However,
this in itself seems to be non-standard behavior, and it has not yet
proved possible to interoperate with Google QUIC. For anyone willing
to attempt to rectify this, some instructions to install it are here:

    http://www.chromium.org/quic/playing-with-quic

After compiling and certificate creation, to run the test server, from
the `src` directory of Chromium:

    ./out/Debug/quic_server \
      --quic_response_cache_dir=/tmp/quic-data/www.example.org \
      --certificate_file=net/tools/quic/certs/out/leaf_cert.pem \
      --key_file=net/tools/quic/certs/out/leaf_cert.pkcs8 --quic-enable-version-99

To run the test client:

    out/Default/quick_client --host=127.0.0.1 --port=6121 --disable-certificate-verification https://www.example.org/ --quic-enable-version-99


Run the server and client testers
=================================

First, set an envionment variable to tell the test script where to find
your implementations of QUIC:

    export QUIC_IMPL_DIR=~
    
This is assuming you built the QUIC implementations in subdirectories
of your home directory. If you put them somewhere else, adjust
accordingly.

Do this to test the server implementation of picoquic:

    $ cd test
    $ python test.py iters=1 server=picoquic test=quic_server_test_stream
    
You may get output that looks something like this:

    output directory: temp/175
    ../quic_server_test_max (0) ...
    server pid: 9410
    timeout 20 ./build/quic_server_test_max seed=0 the_cid=0 server_cid=1 client_port=4987 client_port_alt=4988
    quic_server_test.ivy: line 518: error: assumption failed
    client return code: 1
    FAIL
    error: 1 tests(s) failed

You can see here the output directory that was created and the command
that was run. In this case the test reported a failure. You can look
at the given source code line to see where the failure was. Looking in
the output directory, we have the following:

    $ ls temp/175
    quic_server_test_stream0.err  quic_server_test_stream0.iev  quic_server_test_stream0.out

For each test run (there was only one in our case), we have the log of
ivy events (extension `.iev`) the standard output from the server
(extension `.out`) and the standard error from the server (extension
`.err`). You can use the ivy event viewer to look at the ivy event log:

    $ ivy_ev_viewer temp/175/quic_server_test_stream0.iev
    
If you compiled other testers, you can adjust the `test` parameter of
the test script.  To test a client, do this:

    $ cd test
    $ python test.py iters=1 client=picoquic test=quic_client_stream

The test script has various parameters. Try this to get the usage summary:

    $ python test.py help
    usage:
        test.py [option...]
    options:
        dir=<output directory to create>
        iters=<number of iterations>
        {client,server}={picoquic,quant,winquic}
        test=<test name pattern>
        stats={true,false}
        run={true,false}

With `run=false` the script does not actually run the server or
client. You can run the the server or the client in another shell, or
on another machine.


View the log
============

View the log with the following command:

    ivy_ev_viewer log.iev

Useful links
============

Capturing network traffic:

    https://askubuntu.com/questions/11709/how-can-i-capture-network-traffic-of-a-single-process

Network namespaces:

    http://code.google.com/p/coreemu/wiki/Namespaces

Using CORE to create virtual networks

    https://stackoverflow.com/questions/12671587/isolated-test-network-on-a-linux-server-running-a-web-server-lightttpd-and-cu

Running Google QUIC toy client/server

    http://www.chromium.org/quic/playing-with-quic

LibQUIC: just the QUIC API extracted from Chromium

    https://github.com/devsisters/libquic

Linux build instructions for Chromium:

    https://chromium.googlesource.com/chromium/src/+/master/docs/linux_build_instructions.md

To run a picoquic client instance

    ~/projects/picoquic/picoquicdemo -v ff000012 localhost 4443

TODO list
=========

- Generate new connection id, require fresh connection ids to be used if available,
  handle retire_connection id.
  
- Version negotiation

- Retry and new token

- Enforce max stream id transport parameter

- Make picoquic server send some data (perhaps echo server, or random data)

- Test multiple clients

- Preferred server address

- Closing and draining states

    - after sending close, all packets must contain a matching close
    - after receiving close or stateless reset, send at most one close and nothing else
    
- Stateless reset

- Frame types:

    - BLOCKED (implemented, but no properties)
    - STREAM_BLOCKED (implemented, but no properties)
    - RETIRE_CONNECTION_ID (not implemented)
    - STOP_SENDING (implemented, but what to enforce?)
    - ACK (ECN section)
    - NEW_TOKEN (can receive it, but no properties)
    
- Ack-only packet rules (reinstate)

- Retransmissions (seems to be only liveness properties)

- Test the key phase bit

Other possibly useful instructions
----------------------------------

### Virtual networking and packet capture

Optionally, to monitor implementations of the protocol, it is useful
to run them in a virtual network environment. For this we use the
[CORE virtual networking environment](https://www.nrl.navy.mil/itd/ncs/products/core),
the `tcpdump` command and the `pcap` library. To install these on an
Ubuntu system with version 14.04 or higher, do the following:

    sudo apt-get install core-network tcpdump libpcap-dev

On Ubuntu 18.04 you have to install from source. Get the source from
the link above and follow the README. 

Note: this is only useful if you want to monitor packets using
tcpdump, as it helps elimiante background noise. It isn't needed for
testing purposes.

### Picotls

The testers make use of the `picotls` implementation of TLS. Install
it according to the instructions
[here](https://github.com/h2o/picotls). 

Here are some rough instructions on Ubuntu (YMMV):

    $ cd
    $ sudo apt install libssl-dev pkg-config
    $ export OPENSSL_INCLUDE_DIR=/usr/include/openssl
    $ git clone https://github.com/h2o/picotls.git
    $ cd picotls
    $ git submodule init
    $ git submodule update
    $ cmake .
    $ make

Windows: Instructions for installing picotls on Windows are
[here](https://github.com/h2o/picotls/blob/master/WindowsPort.md).
OpenSSL binaries for Windows can be found
[here](https://slproweb.com/products/Win32OpenSSL.html).
These OpenSSL binaries are missing a file `include/ms/applink.c` that
you will have to get from the OpenSSL source repository.
You also need to copy the libcrypto DLL into "this directory":

    copy c:\OpenSSL-Win64\bin\libcrypto-1_1-x64.dll

Continuing with general instructions:  Then you need to tell the Ivy
compiler where to find the `picotls` library and headers (unless you
copy them to standard locations). Use this command, where
`PICOTLS_DIR` is the directory in which `picotls` was built:

    $ ivy_libs add picotls $PICOTLS_DIR .
    
Notice the dot in the above, which is essential.

### Build the Ivy packet monitor

*Note: skip this step, as the packet monitor doesn't currently work.*

To build the Ivy monitor, change to "this directory" and compile
`quic_monitor.ivy` like this:

    ivyc quic_monitor.ivy

This should create a binary file `quic_monitor`. 

Virtual network startup
=======================

*Note: the packet monitor doesn't currently work because it needs a
way to get the negotiated secrets from TLS. When it does again work,
the following instructions can be used.*

If you want to use virtual networking on linux to isolate QUIC, this
step should be performed once, and then redone after each reboot of
the machine (or after you shut down the virtual network
configuration).

Use the following command in "this directory" (the one containing this
file) to set up a suitable virtual network on your system:

    sudo ./vnet_setup.sh


Running QUIC and capturing packets
==================================

*Note: the packet monitor doesn't currently work because it needs a
way to get the negotiated secrets from TLS. When it does again work,
the following instructions can be used.*

If you haven't done the above virtual network startup step since the
last reboot of your machine, do it now.

We will use MinQUIC as an example, here, but the commands can be
monitored to run different implementations (or mix implementations).

Change to the directory containing MinQUIC:

    cd $GOPATH/src/github.com/kenmcmil/minq

Create three terminals, A, B and C.

Terminal A: run a server in node `n0`:
    
    sudo vcmd -c /tmp/n0.ctl -- `which go` run `pwd`/bin/server/main.go --addr=10.0.0.1:4433 --server-name=10.0.0.1

Terminal B: trace packets with `tcpdump`:

    sudo tcpdump -s 0 -i veth0 -w mycap.pcap

Terminal C: run a client in node `n1`:

    sudo vcmd -c /tmp/n1.ctl -- `which go` run `pwd`/bin/client/main.go --addr=10.0.0.1:4433

Text typed into terminal C should appear on terminal A. The connection
will time out after five seconds of inactivity. When the client
finishes, kill the `tcpdump` process in terminal B with SIGINT
(control-C). You should now have a file `mycap.pcap` containing
captured packets.

To run the server with logging, do this:

    MINQ_LOG='*' MINT_LOG='*' go run bin/server/main.go

Running the Ivy monitor
=======================

*Note: the packet monitor doesn't currently work because it needs a
way to get the negotiated secrets from TLS. When it does again work,
the following instructions can be used.*

To run the Ivy monitor, change to "this directory".  Copy your packet
capture file `mycap.pcap` into "this directory" and then do:

    ./quic_monitor mycap.pcap > log.iev

The file `log.iev` should have lines like this:

    < show_packet({protocol:udp,addr:0xa000002,port:0x869b},{protocol:udp,addr:0xa000001,port:0x1151},{hdr_long:0x1,hdr_type:0x7f,hdr_cid:0x7c74846907e4ce90,hdr_version:0xff000009,hdr_pkt_num:0x3dee3059,payload:[{frame.stream:{off:0x1,len:0x1,fin:0,id:0,offset:0,length:0x282,data:[0x16,0x3,0x3,...]}}]})

These are decoded packets. Each line consists of a source endpoint, a
destination endpoint and a packet. The structure of packets is
described in [quic_packet.ivy](quic_packet.md).

If the specification is violated by the packet trace, the file will
end with an error message indicating the requirement that was
violated.


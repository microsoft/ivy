Ivy specification of QUIC
-------------------------

This directory contains work on specifying the QUIC protocol in Ivy.
The currently targeted version is 9, as described in [this
document](https://tools.ietf.org/html/draft-ietf-quic-transport-09).

The specification is written in a way that allows monitoring of
packets on the wire, and will eventually allow for modular testing of
implementations and possibly a fully verified implementation.

The Ivy spec is being developed from the informal IETF draft cited
above. Ambiguities are resolved by observing the behavior of existing
implementations. In particular, we use the evolving specification to
monitor packet traces captured from implementations.  This allows us
to check consistency and possibly discover incompatibilities between
implementations.

Installation steps
==================

Do these steps just once on a given machine.

### Virtual networking and packet capture

To monitor implementations of the protocol, it is useful to run them
in a virtual network environment. For this we use the [CORE virtual
networking
environment](https://www.nrl.navy.mil/itd/ncs/products/core), the
`tcpdump` command and the `pcap` library. To install these on an Ubuntu
system with version 14.04 or higher, do the following:

    sudo apt-get install core-network tcpdump libpcap-dev

On Ubuntu 18.04 you have to install from source. Get the source from
the link above and follow the README. 

### Botan

For test generation, the Botan implementation of TLS is used. Install
version 2.6.0 from [here](https://botan.randombit.net/releases/). Instructions
are [here](https://botan.randombit.net/).

Install Botan like this (from the Botan source directory):

    ./configure.py
    make
    sudo make install
    sudo ln -s /usr/local/include/botan-2/botan /usr/local/include/botan
    cp src/lib/tls/tls_reader.h /usr/local/include/botan

The last two commands are needed because Botan installs itself in a
way that it can't find its own header files, and it forgets a header
file (at least in 2.6.0).


Implementations of QUIC
-----------------------

### Google QUIC

The Google implementation of QUIC is supposed to be IEFT compatible if
you used version 99. It is part of Chromium code base.

Some instructions to install it are here:

    http://www.chromium.org/quic/playing-with-quic

Before, compiling, you need to patch it to disable packet protection.
A patch against commit `1720d2a` can be found in `chromium_diffs.txt`.

After compiling and certificate creation, to run the test server, from
the `src` directory of Chromium:

    ./out/Debug/quic_server \
      --quic_response_cache_dir=/tmp/quic-data/www.example.org \
      --certificate_file=net/tools/quic/certs/out/leaf_cert.pem \
      --key_file=net/tools/quic/certs/out/leaf_cert.pkcs8 --quic-enable-version-99

To run the test client:

    out/Default/quick_client --host=127.0.0.1 --port=6121 --disable-certificate-verification https://www.example.org/ --quic-enable-version-99



### MinQUIC

This implementation of version 9 in the go language is available [on
github](https://github.com/ekr/minq). However, for Ivy you should use
the fork [here](https://github.com/kenmcmil/minq) which has been
modified to disable crypto.

#### Steps to get started with MinQUIC and Ivy

- Install the [go language](https://golang.org/doc/install) on your platform.
- Follow the instructions [here](https://github.com/kenmcmil/minq) to install MinQUIC.

##### Go installation notes:

Some instructions for installing specifically on Ubuntu are [here](https://github.com/golang/go/wiki/Ubuntu). Note that you need to make sure that the go binary is in your path, and do this:

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

### picoquic

Source code and build instructions:

    https://github.com/private-octopus/picoquic
    
Run a server:

    ./picoquicdemo
    
Run a client 

    ./picoquicdemo localhost
    
### quant

To run the quant server in this directory:

    ~/projects/quant/Debug/bin/server -d . -c leaf_cert.pem -k leaf_cert.key 


Virtual network startup
=======================

This step should be performed once, and then redone after each reboot
of the machine (or after you shut down the virtual network
configuration).

Use the following command in this directory (the one containing this
file!) to set up a suitable virtual network on your system:

    sudo ./vnet_setup.sh




Running MinQUIC and capturing packets
=====================================

If you haven't done the above virtual network startup step since the
last reboot of your machine, do it now.

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

Build and run the Ivy monitor
=============================

To build the Ivy monitor, change to this directory and compile `quic_monitor.ivy` like this:

    ivyc quic_monitor.ivy

This should create a binary file `quic_monitor`. Copy `mycap.pcap` into this directory and then do:

    ./quic_monitor mycap.pcap > log.iev

The file `log.iev` should have lines like this:

    < show_packet({protocol:udp,addr:0xa000002,port:0x869b},{protocol:udp,addr:0xa000001,port:0x1151},{hdr_long:0x1,hdr_type:0x7f,hdr_cid:0x7c74846907e4ce90,hdr_version:0xff000009,hdr_pkt_num:0x3dee3059,payload:[{frame.stream:{off:0x1,len:0x1,fin:0,id:0,offset:0,length:0x282,data:[0x16,0x3,0x3,...]}}]})

These are decoded packets. Each line consists of a source endpoint, a
destination endpoint and a packet. The structure of packets is
described in [quic_packet.ivy](quic_packet.md).

If the specification is violated by the packet trace, the file will
end with an error message indicating the requirement that was
violated. 

Build and run the server tester
===============================

    ivyc target=test quic_server_test.ivy


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

TODO list
=========

- Generate new connection id, require fresh connection ids to be used if available,
  handle retire_connection id.
  
- Version negotiation

- Retry and new token

- Enforce transport parameters in stream frames (update to quic15)

- Make picoquic server send some data (perhaps echo server, or random data)

- Test multiple streams, multiple clients

- Preferred server address

- Closing and draining states

    - after sending close, all packets must contain a matching close
    - after receiving close or stateless reset, send at most one close and nothing else
    
- Stateless reset

- Frame types:

    - MAX_DATA
    - BLOCKED
    - STREAM_BLOCKED
    - RETIRE_CONNECTION_ID
    - STOP_SENDING
    - ACK (ECN section)
    - NEW_TOKEN
    
- Ack-only packet rules (reinstate)

- Retransmissions (seems to be only liveness properties)

- Packet protection


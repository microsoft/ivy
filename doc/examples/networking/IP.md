Testing an IP router
--------------------

We will test an emulated IP router against our IP specification.

The IP specification
====================

We have several specifications for IP.

- Subdirectory `ip_spec_nofrag`. This specification for IP just
describes the IP packets seen on the ethernet. There is just one
event `ip.transmit` that corresponds to an IP packet making a "hop"
over the ethernet. Fragmentation is not specified.

- Subdirectory `ip_spec_frag1`. This specification is similar to the
above in that it only specifies IP packets seen on the
ethernet. However, it also allows a router or an originating host to
perform fragmentation. As in the previous spec, a router is allowed to
forward any data it has seen in the past. This spec makes life easy for
routers, but receivers of fragmented packets may fail to assemble them
correctly, due to ambiguity of datagram identifiers. 

- Main directory. This specification gives higher-level semantics to
IP, describing an event `ip.send` that corresonds to the higher layer
transferring a packet to IP to be delivered. In this spec, we require
every `ip.transmit` event to contain "up-to-date" data, relative to the
`ip.send` events. This makes life hard for the routers, since they don't
know when a fragment that they are transmitting is out-of-date. According to
this spec, we can see the router committing protocol violations.

We could also write a specification that requires the originator to be
sure that no datagrams with the chosen identifier exist in the network
(in the spirit of RFC 791) but this is unimplementable (why?).

We observe in the case of IP that there is no specification that makes
the originator, the router and the reassembler implementable at the
same time.  This is a fundamental flaw in the design of IP. See
[RFC 4963](https://tools.ietf.org/html/rfc4963) for a detailed
description of this problem and its implications.

In practice, because of performance issues and possible reassembly
errors, fragmentation is generally avoided by using MTU discovery
(also known as PMTUD -- RFC 1191), but this also has its problems.

From [Wikipedia](https://en.wikipedia.org/wiki/Path_MTU_Discovery):

> Many network security devices block all ICMP messages for perceived
> security benefits,[7][8] including the errors that are necessary for
> the proper operation of PMTUD. This can result in connections that
> complete the TCP three-way handshake correctly, but then hang when
> data is transferred. This state is referred to as a black hole
> connection.[9]

> Some implementations of PMTUD attempt to prevent this problem by
> inferring that large payload packets have been dropped due to MTU
> rather than because of link congestion. However, in order for the
> Transmission Control Protocol (TCP) to operate most efficiently, ICMP
> Unreachable messages (type 3) should be permitted. A robust method for
> PMTUD that relies on TCP or another protocol to probe the path with
> progressively larger packets has been standardized in RFC 4821.[10]

> A workaround used by some routers is to change the maximum segment
> size (MSS) of all TCP connections passing through links with MTU lower
> than the Ethernet default of 1500. This is known as MSS clamping.[11]

Notice in the last paragraph that routers are actually changing the
content of TCP packets! What could go wrong with this approach? You
can see that questionable engineering of the internet has led to
fragile ad-hoc workarounds. Some people use the term "ossification" to
describe the current frozen state of TCP, which cannot change because
of the intrusive workarounds implemented in routers and other
"middleboxes".

There is a nice article on these issues from
[Cloudflare](https://blog.cloudflare.com/ip-fragmentation-is-broken/).

What might have happened if the inventors of the Internet had tried
writing a formal specification of IP back in 1981?

Test failures
==============

1) Spec: `ip_spec_nofrag/ip_spec.ivy`. Ivy event trace file:
`ip_test_fail1.iev`. Here, a short IP datagram has been padded with
zeros. You might want to consult Google to see why this happens.  Is
this phenomemon described in the RFC for IP? Should it be? Should the
length field be specified to give the actual packet length, is padding
after the payload OK?

This failure occurred because the IP packet decoder used the actual
datagram length rather than the length field in the header. This was
relying on an assumption about the length field that might not be
correct. How can we know?

By the way, the decoder has been fixed to accomodate this issue, so
you won't see this trace in your own testing.

2) Spec: `ip_spec_frag1/ip_spec.ivy`. Ivy event trace file:
`dont_fragment_offset_error.iev`. In this trace, the tester sends a
datagram that is a fragment with an offset of 1 (i.e., 8 bytes) but
the "don't fragment" flag is set.  The router forwards a fragment with
the offset set to zero! Obviously this behavior is incorrect, but what
is the correct behavior? Drop the datagram? Pass it through unchanged?
Does RFC 791 say anything about this?

What if an application sent datagram fragments with "don't fragment"
set, in order to prevent further fragmentation? That might work for a
long time, but then this Cisco router would produce incorrect short
datagrams at the destination (or perhaps this is just a GNS3 bug?). Is
there some danger in the policy of trying to handle all packets even
if they seem malformed?

3) Spec: `ip_spec.ivy`. Ivy event trace file: `reused_identifier.iev`.
In this trace, the last `ip.send` event reuses identifier zero, while
an existing datagram with identifier zero is still being handled by
the router. As a result, the router subsequently forwards a datagram
with stale data. Here, in an attempt to allow correct reassembly of
fragments when identifiers are reused, we have many the router role
unimplementable.


GNS3 setup
==========

Set up GNS3 as described in README.md and make sure it's working.


Router image installation
=========================

We need a router image installed to run an emulated router. This
is an image of and actual Cisco IOS. First, we need to download it.

For details, see this page:

    https://www.computernetworkingnotes.com/ccna-study-guide/how-to-add-install-or-import-ios-in-gns3.html

Start by googling the following terms:

    intitle:index.of cisco ios parent directory bin
    
    
You should get this page:

    http://s.d3v.ma3x.org/GNS3/Cisco%20IOS%20Images/
    
Download this file:

    c3725-adventerprisek9-mz124-11.image

You may find some other, perhaps more recent version.

Now in GDS3, got to the routers panel (which will be empty) and select
"+ New Template" at the bottom.

Select "Install an appliance from the GNS3 server"

Udder "routers", select Cisco 3725 and click install

Select "Install the appliance on your local computer"

Select the file c3725-*.image and click "Import"

Import the image you just downloaded. GNS3 will comaplain that this is
not the correct image, but say "Yes" to install it "at your own risk".

Finish the installation dialog.

Create the docker image
=======================

Pull the latest Ivy source from the networking branch:

    pushd ../ivy
    git checkout networking
    git pull origin networking
    popd

Build the IP testers:

    ivyc target=test ip_test.ivy
    cd ip_spec_nofrag
    ivyc target=test ip_test.ivy
    cd ../ip_spec_frag1
    ivyc target=test ip_test.ivy
    cd ..

Build the docker container:

    sudo docker build --tag=networking .
    

Testing a router
================

Load this project into GNS3:

    ip_test_gns3/ip_test-1.gns3

Click the big `play` button to start all nodes, then right-click
`network-1` select `Console`.  If you like, cd into one of the
directories `ip_spec_nofrag` or `ip_spec_frag1` to use an alternate
specification.

Run the router tests using this command:

    ./ip_test.sh iters=50
    
To do 20 runs, use the option `runs=20`. The testing will stop after
the first assertion violation. 
    
Notice that using `ip_spec_frag1`, the tesing may get rather slow at
some point. Thus is because we are keeping a lot of history
information and feeding it into Z3. In the main directory, you will
probably find an error due to forwarding of stale datagram fragments
fairly quickly. See the files `ip_spec.ivy` and `ip_test.ivy` for a
detailed discussion. 


Creating a layout
=================

The remainder of this document describes how to create the test setup
from scratch.

 and skip to `Run the IP tester` below.

Or, to create the loayout from scratch, continue with the following steps.

Start by creating a layout similar to the one shown in
`ip_test_layout.png`.  We have one router we wish to test, with two
ethernet ports. We will test it by driving these two ports from a
virtual host running the `networking` docker container (see
README.md).


Configure the docker container network
======================================

Right-click in `networking-1` and select `Configure`. Select the `Edit` button
under `Network configuration` and put in the following text:

auto eth0
iface eth0 inet static
	address 10.1.1.2
	netmask 255.255.255.0
	gateway 0.0.0.0


auto eth1
iface eth1 inet static
	address 10.1.2.2
	netmask 255.255.255.0
	gateway 0.0.0.0

Note that the space before `address`, `netmask` and `gateway` is a tab character!


Configure the router
====================

Start the router (right-click and select "Start"). Open a terminal on
the router (right-click and select "Console"). This is just as if you
had a terminal plugged into a real router.

Some information on configuring the router can be found here:

   https://docs.gns3.com/1d1huu6z9-wWGD_ipTSQZqy2mpaxiqzymu-YQo6at_Jg/index.html

Configure the router like this:

    R1#conf t
    Enter configuration commands, one per line.  End with CNTL/Z.
    R1(config)#int fa0/0
    R1(config-if)#ip add 10.1.1.1 255.255.255.0
    R1(config-if)#int loop 0
    R1(config-if)#
    *Mar  1 00:23:06.551: %LINEPROTO-5-UPDOWN: Line protocol on Interface Loopback0, changed state to up
    R1(config-if)#ip add 1.1.1.1 255.255.255.255
    R1(config-if)#end
    R1#
    *Mar  1 00:23:41.407: %SYS-5-CONFIG_I: Configured from console by console
    R1#conf t
    Enter configuration commands, one per line.  End with CNTL/Z.
    R1(config)#int fa0/1
    R1(config-if)#ip add 10.1.2.1 255.255.255.0
    R1(config-if)#end
    R1#
    *Mar  1 00:25:11.947: %SYS-5-CONFIG_I: Configured from console by console
    R1#conf t
    Enter configuration commands, one per line.  End with CNTL/Z.
    R1(config)#int fa0/0
    R1(config-if)#no shut
    R1(config-if)#int 
    *Mar  1 00:26:16.599: %LINK-3-UPDOWN: Interface FastEthernet0/0, changed state to up
    *Mar  1 00:26:17.599: %LINEPROTO-5-UPDOWN: Line protocol on Interface FastEthernet0/0, changed state to up
    R1(config-if)#int fa0/1
    R1(config-if)#no shut
    R1(config-if)#
    *Mar  1 00:26:29.279: %LINK-3-UPDOWN: Interface FastEthernet0/1, changed state to up
    *Mar  1 00:26:30.279: %LINEPROTO-5-UPDOWN: Line protocol on Interface FastEthernet0/1, changed state to up
    R1(config-if)#end 
    R1#
    *Mar  1 00:29:18.239: %SYS-5-CONFIG_I: Configured from console by console
    R1#conf t
    Enter configuration commands, one per line.  End with CNTL/Z.
    R1(config)#router ospf 1
    R1(config-router)#router-id 1.1.1.1
    R1(config-router)#network 0.0.0.0 255.255.255.255 area 0
    R1(config)#ip default-gateway 10.1.1.2
    R1(config)#ip route 0.0.0.0 0.0.0.0 10.1.1.2
    R1(config)#ip routing
    R1(config-router)#end
    R1#
    *Mar  1 00:30:35.059: %SYS-5-CONFIG_I: Configured from console by console
    R1# copy run start

To see debugging on console:
============================

    R1#debug ip packet detail

Start the virtual host
======================


In the console window, make sure you can ping both interfaces of the router, and
get their ethernet address with the `arp` command:


    root@networking-1:/app# ping 10.1.1.1
    PING 10.1.1.1 (10.1.1.1) 56(84) bytes of data.
    64 bytes from 10.1.1.1: icmp_seq=1 ttl=255 time=26.8 ms
    64 bytes from 10.1.1.1: icmp_seq=2 ttl=255 time=11.9 ms
    64 bytes from 10.1.1.1: icmp_seq=3 ttl=255 time=5.98 ms
    ^C
    --- 10.1.1.1 ping statistics ---
    3 packets transmitted, 3 received, 0% packet loss, time 2003ms
    rtt min/avg/max/mdev = 5.981/14.919/26.857/8.782 ms
    root@networking-1:/app# ping 10.1.2.1
    PING 10.1.2.1 (10.1.2.1) 56(84) bytes of data.
    64 bytes from 10.1.2.1: icmp_seq=1 ttl=255 time=12.7 ms
    64 bytes from 10.1.2.1: icmp_seq=2 ttl=255 time=6.73 ms
    64 bytes from 10.1.2.1: icmp_seq=3 ttl=255 time=11.6 ms
    64 bytes from 10.1.2.1: icmp_seq=4 ttl=255 time=5.53 ms
    ^C
    --- 10.1.2.1 ping statistics ---
    4 packets transmitted, 4 received, 0% packet loss, time 3004ms
    rtt min/avg/max/mdev = 5.535/9.170/12.781/3.089 ms
    root@networking-1:/app# arp 10.1.1.1
    Address                  HWtype  HWaddress           Flags Mask            Iface
    10.1.1.1                 ether   c2:01:13:48:00:00   C                     eth0
    root@networking-1:/app# arp 10.1.2.1
    Address                  HWtype  HWaddress           Flags Mask            Iface
    10.1.2.1                 ether   c2:01:13:48:00:01   C                     eth1
    root@networking-1:/app# 


Find out the network interface indices:

    root@networking-1:/app# ip link show
    1: lo: <LOOPBACK,UP,LOWER_UP> mtu 65536 qdisc noqueue state UNKNOWN mode DEFAULT group default qlen 1000
        link/loopback 00:00:00:00:00:00 brd 00:00:00:00:00:00
    77: eth0: <BROADCAST,MULTICAST,UP,LOWER_UP> mtu 1500 qdisc fq_codel state UNKNOWN mode DEFAULT group default qlen 1000
        link/ether 3a:96:52:fb:0c:45 brd ff:ff:ff:ff:ff:ff
    78: eth1: <BROADCAST,MULTICAST,UP,LOWER_UP> mtu 1500 qdisc fq_codel state UNKNOWN mode DEFAULT group default qlen 1000
        link/ether d6:cb:be:76:93:3e brd ff:ff:ff:ff:ff:ff

In the above example, the indices are 77 abd 78. These numbers are needed by Ivy to refer to the
specific interfaces while testing

If oyu mae    

    


Run the ip tester, plugging in the MAC addresses of the router interfaces and the indices
of the two host interfaces:

    ./ip_test router_mac1=0xc20113480000 router_mac2=0xc20113480001 host_intf1=77 host_intf2=78
    
Notice we have converted the ethernet addresses to hex numbers.


Rebuild the tester and run again
================================

Unfortunately, GNS3 will not automatically reload the latest version
of the docker container, even if you use the "reload" command. The
only way I have found to do this is to open a different GNS3 project,
then open you project again. Alternatively, you can quit GNS3 and
start it again.

After starting your layout, you can check whether the latest docker
container is running by this command on the host:

    sudo docker container ls

It should show the version as networking:latest.

GNS3 project
============

If you have installed the exact IOS image described above, you
might be able to open the project `ip_test_gns3/ip_test-1.gns3`. This
will have the layout already configured and ready to go and also
has router MAC addresses that match the default values in ip_test.ivy,
so you don't have to put these on the command line.

Wrapper script
==============

The wrapper stript `ip_test.sh` will run `ip_test` (in the docker
container networking-1 console). This captures the network interface
indexes (which change every time you run the container) so you don't need
to enter these as command-line parameters. You just run it like this:

    ./ip_test.sh <options>
    
where `<options>` are options of `ip_test`.  If you are using the GNS3
project in the repo, or if you set the mac address of the router in
your project as in `ip_test_gns3/ip_test-1.gns3`, then you don't have
to put the mac addresses on the command line. Hint: change the
parameter `mac_addr`.













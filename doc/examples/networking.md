---
layout: page
title: Networking
---

We saw previously how to [run the leader election example using a
REPL](helloworld.html).  Via the REPL, the user acted the role of the
environment, including the network. This is, of course somewhat
unsatisfactory. Ideally, we would like a real network to take this
role.

In this section, we'll see how to accomplish that. That is, we will
implment a protocol as a collection of processes communicating over a
network.

## A network interface

Ivy provides a simple interface to the Unix Datagram protocol (UDP) in
a module called `udp`. Here is the interface specification:

    module udp_simple(addr,pkt) = {

	import action recv(dst:addr,v:pkt)
	export action send(src:addr,dst:addr,v:pkt)

	object spec = {
	    relation sent(V:pkt, N:addr)
	    init ~sent(V, N)

	    before send {
		sent(v,dst) := true
	    }
	    before recv {
		assert sent(v,dst)
	    }
	}

	instance impl(X:addr) : udp_wrapper(addr,pkt,X)
	private impl
    }

The interface is a module with two parameters: the type `addr` of
network addresses, and the type `pkt` of packets.  It has two actions,
`recv` and `send`.  These are very similar to actions of the abstract
transport interface we used in the leader election protocol.  The only
difference is that the `send` action the source address of the packet
as a paramater as well as the destination address. We'll see the rason
for this shortly. Action `recv` is imported by the interface (meaning
the user must implement it) while `send` is exported (meaning that the
module implements it).

As in the leader example, the specification promises that only packets
that have been sent wil be received (but packets may be dropped,
duplicated or re-ordered). 

For now, ignore the definition of object `impl`. We'll come back to it
later. 

Let's begin by writing a simple test program that uses `udp_simple`:

    #lang ivy1.6

    type a  # network addresses
    type p  # packets

    include udp
    instance foo : udp_simple(a,p)

    import foo.recv
    export foo.send

    interpret a->bv[1]
    interpret p->bv[16]

    extract iso_impl = foo.impl

Here, we define a type of network addresses `a` and a type of packets
`p`. We include the `udp` module (which is part of IVy's system
libraries). We then make an instance of `udp_simple`. To allow us to
interact with this module, we import the `recv` action from the
environment and export `send`.  Finally, we interp the types:
addresses are one-bit numbers and packets are 16-bit numbers.  Since
we don't want to compile the specification, we extract just the
implementation of the interface, which is `foo.impl`.

We compile and run this program as follows:

    $ ivy_to_cpp target=repl isolate=iso_impl udp_test.ivy
`   $ g++ -o udp_test udp_test.cpp
    $ ./udp_test
    >

Now we can send a packets:

    > foo.send(0,1,2)
    > foo.recv(1,2)
     
What happend here? When we started the REPL, IVY bound addresses 0 and
1 to two UDP port numbers. Call then ports A and B. We called
`foo.send` to send a packet from address 0 to address 1 with content
2. The module `foo` somehow marshalled the number 2 into a packet and
sent it out on port A.  It then printed a new prompt. At this point,
the packet was received on the port B. This caused `foo.recv` to be
called, resulting in the print-out `foo.recv(1,2)` after the prompt.

We can try it again.

    foo.send(1,0,3)
    > foo.recv(0,3)

A packet sent out on port B was received on port A.

## Parallel processes

It's not very interesting, though, for one process to send packets to
itself. What we want is to have multiple processes talking to each
other. IVy can create parallel processes for us starting from a
[parameterized object](leader.html). Each value of the parameter
becomes an individual process. This transformation is called
*parameter stripping*.

# Parameter stripping

The `upd_simple` specification is an example of a parameterized
object.  Each action has an initial parameter of type `addr` that we
can think of as an instance of the object, or as identifying the
process performing the action. This is why `send` has the parameter
`src`. The source address is the one performing the `send` action.

We can extract just one process as follows:

    extract iso_impl(me) = foo.impl(me)

Here, `me` is a symbolic constant that represents the first parameter
of of each action. The first parameter is "stripped" by replacing it
with the symbolic constant `me`.

Before thinking about this too hard, let's just run it to see what
happens. We compile as usual:

    $ ivy_to_cpp target=repl isolate=iso_impl udp_test2.ivy
`   $ g++ -o udp_test2 udp_test2.cpp

Now, open up a new terminal that we'll call terminal A. In that
terminal try to run `upd_test2`:

    A: $ ./udp_test2
    A: usage: udp_test2 me

Ivy says we need to give the value of the parameter `me` to create a
process. In other words, we have to give the network address of the
process we want to run. So let's do that:

    A: $ ./udp_test2 0
    A: >

Now we start up another terminal (call it terminal B) and run a process with
address 1:

    B: $ ./udp_test2 1
    B: >

Now, let's send a packet from A to B:

    A: > foo.send(1,2)
    A: > 

    B: foo.recv(2)

Notice that we omit the `src` parameter of `foo.send`, since that was
given on the command line. Similarly, when terminal B receives the packet,
it 









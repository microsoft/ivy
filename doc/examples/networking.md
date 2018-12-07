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
implement a protocol as a collection of processes communicating over a
network.

## A network interface

Ivy provides a simple interface to the Unix Datagram Protocol (UDP) in
a module called `udp`. Here is the interface specification:

    module udp_simple(addr,pkt) = {

        import action recv(dst:addr,v:pkt)
        export action send(src:addr,dst:addr,v:pkt)

        object spec = {
            relation sent(V:pkt, N:addr)
            after init {
                sent(V, N) := false
            }

            before send {
                sent(v,dst) := true
            }
            before recv {
                assert sent(v,dst)
            }
        }

        instance impl(X:addr) : udp_wrapper(addr,pkt,X)
    }

The interface is a module with two parameters: the type `addr` of
network addresses, and the type `pkt` of packets.  It has two actions,
`recv` and `send`.  These are very similar to actions of the abstract
transport interface we used in the leader election protocol.  The only
difference is that the `send` action takes the source address of the packet
as a parameter as well as the destination address. We'll see the reason
for this shortly. Action `recv` is imported by the interface (meaning
the user must implement it) while `send` is exported (meaning that `udp_simple`
implements it).

As in the leader example, the specification promises that only packets
that have been sent will be received (but packets may be dropped,
duplicated or re-ordered). 

For now, ignore the definition of object `impl`. We'll come back to it
later. 

Let's begin by writing a simple test program that uses `udp_simple`:

    #lang ivy1.7

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
environment and export `send`.  Finally, we interpret the types:
addresses are one-bit numbers and packets are 16-bit numbers.  Since
we don't want to compile the specification, we extract just the
implementation of the interface, which is `foo.impl`.

We compile and run this program as follows:

    $ ivy_to_cpp target=repl isolate=iso_impl udp_test.ivy
    $ g++ -o udp_test udp_test.cpp
    $ ./udp_test
    >

Now we can send a packets:

    > foo.send(0,1,2)
    > foo.recv(1,2)
     
What happened here? When we started the REPL, IVY bound addresses 0 and
1 to two UDP port numbers. Call them ports A and B. We called
`foo.send` to send a packet from address 0 to address 1 with content
2. The module `foo` somehow marshaled the number 2 into a packet and
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

    extract iso_impl(me:a) = foo.impl(me)

Here, `me` is a symbolic constant that represents the first parameter
of of each action. The first parameter is "stripped" by replacing it
with the symbolic constant `me`.

Before thinking about this too hard, let's just run it to see what
happens. We compile as usual:

    $ ivy_to_cpp target=repl isolate=iso_impl udp_test2.ivy
    $ g++ -o udp_test2 udp_test2.cpp

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
given on the command line. Similarly, when terminal B receives the
packet, it prints `foo.recv(2)`, because the first parameter `dst` is
implicit.

We can, of course, send a packet in the opposite direction:

    B: foo.send(0,3)
    B: >

    A: foo.recv(3)

Also, one terminal can send a packet to itself:

    A: foo.send(0,4)
    A: > foo.recv(4)

(again, the packet is received after the prompt is printed).

IVy places some restriction on extracts with parameters. These
restrictions guarantee that the parallel processes behave as if they
were running sequentially in a single process space (technically, the
Ivy guarantees that the actions are
[*serializable*](https://en.wikipedia.org/wiki/Serializability)). We'll
discuss these restrictions shortly. For now let's look at using the
`udp_simple` interface in our leader election protocol.

# Running a distributed protocol

Recall that the leader election protocol had an interface `trans` that
represented the network. Since this interface has the same specification
`udp_simple`, we can replace object `trans` with this code:

    include udp
    instance trans : udp_simple(node.t,id.t)

Notice that we use `node.t` as the `addr` type and `id.t` as the `pkt`
type. We also have to remove these declarations:

    import trans.send
    export trans.recv

This is because `send` is now provided by `trans`, and `recv` is now
called by `trans`, not by the REPL. The environment is now just:

    import serv.elect
    export app.async

Finally, we change the `extract` declaration to include the
*implementation* of `trans`:

    extract iso_impl(me:node.t) = app(me),trans.impl(me),node_impl,id_impl,asgn

That is, we don't want the specification object `trans.spec` in the
code we actually run. Notice that we strip the first parameter of both
`app` and `trans.impl`. We don't strip parameters from `node_impl`,
`id_impl`, `asgn` because these objects provide functions without any
state (they are a bit like static methods in a C++ class). We'll
discuss this issue later in more detail.

Before running the protocol, we ought to try to verify it:

    $ ivy_check leader_election_ring_udp.ivy
    Checking isolate iso_app...
    trying ext:app.async...
    trying ext:trans.recv...
    Checking isolate iso_id...
    Checking isolate iso_node...
    trying ext:node.get_next...
    OK

The verification succeeds. This makes sense, since the specification
of `trans` hasn't changed, so our inductive invariant is still good.
We might ask why we didn't have to verify `trans.impl`. This is
because this object is part of IVy's trusted code base. In fact,
`udp_simple` is implemented in C++ and makes use of the operating
system's API, which we can't formally verify. We can only verify
`trans.impl` by testing.

For now, let's try to run our protocol. As before, we compile it like this:

    $ ivy_to_cpp target=repl isolate=iso_impl leader_election_ring_udp.ivy
    $ g++ -o leader_election_ring_udp leader_election_ring_udp.cpp 

Recall that we interpret the type `node.t` as one-bit numbers. That
means that we have two processes in our ring numbered 0 and 1. So let's
create them in our terminals A and B:

    A: $ ./leader_election_ring_udp 0
    A: >

    B: $ ./leader_election_ring_udp 1
    B: >

The protocol is running, but it hasn't done anything yet. We need to
call the `async` action of one of the processes to get it to transmit its id:

    A: > app.async
    A: > serv.elect

Notice again the the implicit `node.t` parameters of these actions are
omitted. Obviously, node 0 has the highest id, since it elected
itself.  What we didn't see was node 0's id being transmitted to node
1, then being forwarded back to node 0, causing node 0 to be
elected. Just to make sure things are working, let's try the
following:

    B: > app.async
    B: >

Clearly, node 1's id did not pass node 0, so node 1 is not elected.

# The timeout interface

Our protocol works, but is still unsatisfactory in at least one
way. That is, it only does something in response to a call to
`app.async`. We'd like `app.async` to be connected to some kind of
system event so it repeats at some interval. We can do this using the
system `timeout` module. This contains the following interface:

    module timeout_sec = {

        import action timeout

        object spec = {
        }

        instance impl : timeout_wrapper
    }

This interface is pretty simple. It calls imported action `timeout`
without any specification. In fact, the implementation uses the
operating system's facilities to call `timeout` approximately once
per second.

To test, this interface, let's write a simple program that just imports
`timeout` from the REPL:

    #lang ivy1.7

    include timeout

    instance foo : timeout_sec

    import foo.timeout

Here's what we get:

    $ ivy_to_cpp target=repl timeout_test.ivy 
    $ g++ -o timeout_test timeout_test.cpp
    $ ./timeout_test
    > foo.timeout
    foo.timeout
    foo.timeout
    foo.timeout
    ...

The program prints `foo.timeout` once per second. Now let's modify the leader
election program so the the `app.async` action is called once per second.

First, we instantiate a timer for each process, like this:

    include timeout
    instance sec(X:node.t) : timeout_sec

Then we modify the protocol so that it implements `sec.timeout`. That is, we change this line:

        action async(me:node.t) = {

to this:

        implement sec.timeout(me:node.t) {

Notice that the parameter doesn't change: we have one timer per
process. We also have to remove this line, since action `app.async` no longer exists:

    export app.async

Finally, we include the implementation of `sec` in the extract:

    extract iso_impl(me:node.t) = app(me),trans.impl(me),sec.impl(me),node_impl,id_impl,asgn

Notice that `sec.impl` also has one parameter stripped, since we have
one timer per process. We compile as before:

    $ ivy_to_cpp target=repl isolate=iso_impl leader_election_ring_udp2.ivy
    $ g++ -o leader_election_ring_udp2 leader_election_ring_udp2.cpp 

Now we run the processes in terminals A and B:

    A: $ ./leader_election_ring_udp2 0
    A: >

    B: $ ./leader_election_ring_udp2 1
    B: >

    A:  serve.elect
    A:  serve.elect
    A:  serve.elect
    ...

Notice that nothing happens when we start node 0. It is sending packets
once per second, but they are being dropped because no port is yet
open to receive them. After we start node 1, it forwards node 0's
packets, which causes node 0 to be elected (and to continues to be
elected once per second).

A note: suppose we had neglected to include `sec.impl` in the extract.
Since the action `sec.timeout` is called from outside the extract, it
is implicitly exported to the environment. Since this is likely not
what we want, Ivy gives the following warning:

    $ ivy_to_cpp target=repl isolate=iso_impl leader_election_ring_udp2.ivy
    leader_election_ring_udp2.ivy: line 131: warning: action sec.timeout is implicitly exported

## Serializability

As mentioned above, IVy guarantees serializability. This means that
actions executed by concurrent process produce the same input/output
result as if the actions had been executed [*in isolation*](https://en.wikipedia.org/wiki/ACID) in some
order. By isolation, we mean that each action completes before any other action
begins.

To guarantee serializability, IVy requires that processes be
*non-interfering*.  This means that one process cannot have a
side-effect that is visible to another process.

As an example of interference, consider the following program:

    #lang ivy1.7

    type t

    individual bit : bool

    object foo(me:t) = {
        action flip = {
            bit := ~bit
        }
    }

    export foo.flip

    extract iso_foo(me:t) = foo(me)

This program has one parallel process for each value of a type
`t`. Each process provides a method that modifies a global variable
`bit`. Obviously, this is not a distributed program, because the processes
share a variable. Here's what happens when we try to compile the program:

    ivy_to_cpp target=repl isolate=iso_foo interference2.ivy
    interference2.ivy: line 9: error: assignment may be interfering

If processes don't modify any state components in common, they are
non-interfering. This means that if we execute action of distinct
processes in parallel, the result is the same as if we had executed
them sequentially in either order. Thus, the actions are serializable.

We could fix the above program by creating one copy of the bit for each 
process:

    #lang ivy1.7

    type t

    individual bit(X:t) : bool

    object foo(me:t) = {
        action flip = {
            bit(me) := ~bit(me)
        }
    }

    export foo.flip

    extract iso_foo(me:t) = foo(me),bit(me)

This program compiles successfully. But what would happen if
one process tried to access the variable of another process.
Consider this program:

    #lang ivy1.7

    type t

    individual bit(X:t) : bool

    object foo(me:t) = {
        action flip(x:t) = {
            bit(me) := ~bit(x)
        }
    }

    export foo.flip

    extract iso_foo(me:t) = foo(me),bit(me)

Here, object `foo(me)` accesses the `bit` of some process `x`,
where `x` is an input. Here's what happens when we compile:

    ivy_to_cpp target=repl isolate=iso_foo interference4.ivy
    interference4.ivy: error: cannot strip parameter x from bit

Ivy recognizes that `bit(me)` is an access to the current process'
copy of `bit`, but it cannot compile `bit(x)`, because `x` might not
be equal to `me`. 

# Effects on the environment

Of course, to communicate with each other, processes must have a
visible effect on something. That something is the environment, which
includes the operating system and the physical network. A call to
`trans.send` has an effect on the environment, namely sending a
packet. The Ivy run-time guarantees, however, that actions remain
serializable despite these effects, using [Lipton's theory of left-movers
and right-movers](http://dl.acm.org/citation.cfm?id=361234). In the theory's terms,
receiving a packet is right-mover, while sending a packet is a
left-mover. Every action consists of zero or one receive events followed by
any number of send events. The theory tells use that such actions are
serializable.  That is, we can re-order any concurrent execution by
commuting left-movers and right-movers such that the result is an
equivalent isolated execution.

This, however, is an issue only for IVy's implementers. Users can
simply rely on the fact that concurrent execution will appear
equivalent to sequential execution, assuming the program passes
`ivy_check`.

# Immutable objects and initial states

Ivy allows immutable objects (that is, read-only objects) such as the
`pid` map in the leader protocol, to be shared between processes.
Each process refers to its own local copy of the immutable object.  In
the case of the `pid` map, IVy solved for a value of this function
satisfying the given axiom that no two nodes have the same id. A table
of this function was stored in the compiled process.

Currently, IVy has some limitations in its ability to generate the
immutable objects and also to generate initial states for parametrized
processes. Consider, for example, this program:

    #lang ivy1.7

    type t

    object foo(me:t) = {
        individual bit:bool
        after init {
            bit := false
        }

        action get_bit returns (x:bool) = {
            x := bit
        }
    }

    export foo.get_bit

    extract iso_foo(me:t) = foo(me)

IVy can compile this program and run it:

    $ ./paraminit 0
    > foo.get_bit
    0
    > 

Note that it is allowed for the initial condition to depend on the
parameter `me`. For example, we could write:

    after init {
        bit := me = 0
    }

That is, we want `bit` to be true initially only for process 0. 
This version can also be stripped and gives the expected result:

    $ ivy_to_cpp target=repl isolate=iso_foo paraminit3.ivy 
    $ g++ -o paraminit3 paraminit3.cpp
    $ ./paraminit3 0
    > foo.get_bit
    1
    >   ^C
    $ ./paraminit3 1
    > foo.get_bit
    0
    > 








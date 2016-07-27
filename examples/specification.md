---
layout: page
title: Specifications
---

Formal verification is primarily about establishing relationships
between specifications at differing levels of abstraction. 

Consider, for example, a network protocol, such as the [TCP
protocol](https://en.wikipedia.org/wiki/Transmission_Control_Protocol)
that is widely used to communicate streams of data over the Internet.
At a high level of abstraction, TCP is a *service*, providing methods
for establishing connections, and sending or receive data. This
service provides guarantees to its users of reliable in-order
transmission of streams of bytes. At a lower level of abstraction, TCP
can be seen as a *protocol*. The protocol is a set of rules (laid out
in [RFC 675](https://tools.ietf.org/html/rfc675) and later documents)
that implements service guarantees of TCP by exchanging datagrams
over an unreliable network.

The service and protocol specifications of TCP are views of the same
process observed at different interfaces. That is, TCP is sandwiched
between a higher-level application (say, a web browser and web server)
and the lower-level datagram protocol (typically the IP protocol) as shown below:

![Network Stack](../images/network_stack1.png)

The TCP service specification describes the events we observe at the
interface between the application layer and the transport layer.  The
IP service specification describes the events we observe at the
interface between the transport layer and the network layer.  The TCP
protocol specification describes the *relation* between events at this
interface and the lower-level interface between transport and network
layers.

If we were develping the TCP protocol specification, we would like to
verify that the IP service and the TCP protocol together implement the
TCP service specification. That is, if events at the transport/network
interface are consistent with the IP service specification, and if we
execute the TCP protocol according to its specification, then events
at the application/transport interface should be consistent with the TCP
service specification. From the point of view of the TCP protocol, we
say that the IP service specification is an *assumption*, while the
TCP service specification is a *guarantee*. 

IVy has features that allow us to perform this kind of reasoning. It allows us to:

- Define objects with interfaces
- Write specifications about interfaces
- Prove assume/guarantee relationships between these specifications

In IVy, interfaces and specifications are objects. An interface is
object with unimplemented actions (a bit like an instance of an
abstract class in C++). A specification is a special object that
monitors the calls and returns across an interface.

# Monitors as specifications

To specify services such as TCP, we need to make statements about the
*sequences* of events that can occur at an interface. For example, in
TCP, we need to make statements relating the sequences of send and
receive events to abstract data streams that are transmitted between
clients. Specifications about sequences of events in time are often
referred to as *temporal* specifications.

A common approach to tempral specification is to define a specialized
logical notation called a [*temporal
logic*](http://plato.stanford.edu/entries/logic-temporal). These
notations make it possible to write succinct temporal specifications,
and also us to do some proofs in a fully automated way using [model
checking](http://www.loria.fr/~merz/papers/mc-tutorial.pdf).

For reasons we will discuss shortly, IVy takes a different approach.
Temporal specifications in IVy are defined using special objects
called *monitors*. A monitor is an object that synchronizes its
actions with calls and returns across an interface. This allows the
monitor to record information about the history of the interface in
its local state, and to assert facts that should be true about
inteface events based on the history of previous events.

As an example, here is a definition of an interface for a rediculously
simple network service:
 
    #lang ivy1.5
    type packet

    object intf = {
        action send(x:packet)
        action recv(x:packet)
    }

The actions in an interface object don't have definitions. These will
be filled in by other objects that implement the different roles in
the interface. We don't know yet what these objects actually do, but
we can write a service specification that tells us something about the
temporal behavior at the interface:

    object spec = {
        relation sent(X:packet)
        init ~sent(X)

        before intf.send {
            sent(x) := true
        }

        before intf.recv {
            assert sent(x)
        }
    }

Object `spec` is a monitor. It has one local state component `sent`
that records the set of packets that have been sent so far. This
information is recorded by injecting an action before every call to
`intf.send`. This is done using a new declaration `before`. Notice
that the injected action can refer to the parameters of `intf.send`
and it can update the monitor state.  In addition, the monitor injects
an assertion before every call to `intf.recv`. This assertion states
that the received packet `x` has previously been sent.

In effect, our service specification describes a channel that can
re-order and duplicate packets, but cannot corrupt packets. If any
corrupted packet is received, the assertion will fail.

Now let's consider some possible implementations of this very simple
specification. Here is the most trivial one:

    object protocol = {
        implement intf.send {
            call intf.recv(x)
        }
    }

Object `protocol` provides the implementation of action `intf.send`
using a new declaration `implement`. This declaration provides the
missing body of the action `intf.send`. This simply calls `intf.recv`
on the sent packet `x`. The assertion in monitor `spec` is always
true, since before calling `intf.send`, the packet `x` is added to the
relation `sent`. That is, our implementation trivially satisfies the
specification "receive only sent packets".

To verify our implementation, we need to put it in a suitable
environment. The following statements tell us that the environment
will implement `intf.recv` and will call `intf.send`:

    import intf.recv
    export intf.send

Now, saving this text in the file `trivnet.ivy`, we can check that our
"protocol" satisfies its service specification like this:

    $ ivy_check trivnet.ivy
    trying ext:intf.send...
    OK

We don't even need an inductive invariant in this case, because the
assertion is true when `intf.send` is executed in any context. 

To get a better idea of what is happening with `before` and
`implements`, we can print out the program that results from inserting
the monitor actions and interface implementations:

    $ ivy_show trivnet.ivy

    type packet
    relation spec.sent(V0:packet)

    init [spec] ~spec.sent(X)

    action intf.send(x:packet) = {
        spec.sent(x) := true;
        call intf.recv(x)
    }
    action intf.recv(x:packet) = {
        assert spec.sent(x)
    }

Notice that the `before` actions of `spec` have been inserted at the
beginning of these actions, and the `implement` action of `protocol`
has been used as the body of `intf.send`.

Of course, we might consider a (slightly) less trivial implementation,
such as this one that implements the service specification with a
one-place buffer:

    object protocol = {
        individual full : bool
        individual contents : packet
        init ~full

        implement intf.send {
            full := true;
            contents := x
        }

        action async = {
            if full {
                full := false;
                call intf.recv(contents)
            }
        }
    }

This implementation has an action `async` that needs to be called by the
environment, so we add:

    export protocol.async

To verify this implementation, we also need one invariant conjecture:

    conjecture protocol.full -> spec.sent(protocol.contents)

That is, to show that when `async` executes, the received packet has
been sent, we need to know that the packet in the buffer has been
sent. The reader might want to try to produce this invariant using the
[interactive invariant generation
techniques](/examples/client_server_example.html) supported by IVy.

# Assume-Guarantee reasoning in IVy

In the previous example, we saw that a service specification is a kind
of abstraction. It hides details of the underlying imlementation,
telling us only what we need to know to use the service. Abstractions
are crucial in reasoning about complex systems. They allow us to
develop one component of a system without thinking about the details
of the implementation of other components. For example, when
developing a network application based on TCP, we don't have to read
RFC 675. We just rely on the simple service guarantee that TCP
provides (reliable, in-order delivery). The service specification
allows us to think about our application in *isolation* from the
network protocol stack.

IVy provides a mechanism to do just this when proving correctness of
system components. That is, we can isolate a single object in our
system and prove its correctness using only the service specifications
of its interfaces.

As an example, let's build a system of two components that plays a
highly simplified game of ping-pong. Here is the interface definition:

    #lang ivy1.5

    object intf = {
        action ping
        action pong
    }

Here is the interface specification:

    type side_t = {left,right}

    object spec = {
        individual side : side_t
        init side = left

        before intf.ping {
            assert side = left;
            side := right
        }

        before intf.pong {
            assert side = right;
            side := left
        }
    }

The specification has a single state component `side` that keeps track
of whether the ball is on the left- or right-hand side of the
table. When the ball is on the left, a `ping` action is allowed,
sending the ball to the right-hand side.  When the ball is on the
right, a `pong` is allowed, sending the ball to the left again.  A
failure to alternate `ping` and `pong` would cause one of the
assertions to fail.

Now let's implement the left-hand player:

    object left_player = {
        individual ball : bool
        init ball

        action async = {
            if ball {
                call intf.ping;
                ball := false
            }
        }

        implement intf.pong {
            ball := true
        }

        conjecture ball -> spec.side = left
    }

The player has a Boolean `ball` that indicates the ball is in the
player's court. We assume the left player serves, so `ball` is
initially true. Asynchronously, if the left player has the ball, she
can call `ping` to send it to the right, setting `ball` to false.  The
left player implements `ping` by setting `ball` to true (for the
moment, ignore the invariant conjecture).

The right-hand player is similar:

    object right_player = {
        individual ball : bool
        init ~ball

        action async = {
            if ball {
                call intf.pong;
                ball := false
            }
        }

        implement intf.ping {
            ball := true
        }

        conjecture ball -> spec.side = right
    }

Let's export the `async` actions to the environment, so the players
will do something:

    export left_player.async
    export right_player.async

At this point we could easily enough verify the assertions using the
given invariant conjectures. Instead, however, we will separate the
reasoning about the left and right players. We add these two declarations:

    isolate iso_l = left_player with spec
    isolate iso_r = right_player with spec

The first says to isolate the left player using the interface
specification `spec`.  The second says to do the same thing with the
right player. This reduces the proof to two separate proofs problems
called "isolates". We can see what the first isolate looks like as
follows:

    $ ivy_show isolate=iso_l pingpong.ivy

    type side_t = {left,right}
    individual spec.side : side_t
    relation left_player.ball

    init [spec] spec.side = left
    init [left_player] left_player.ball

    conjecture [left_player] left_player.ball -> spec.side = left

    action ext:left_player.async = {
        if left_player.ball {
            call intf.ping;
            left_player.ball := false
        }
    }

    action intf.ping = {
        assert spec.side = left;
        spec.side := right
    }

    action ext:intf.pong = {
        assume spec.side = right;
        spec.side := left;
        left_player.ball := true
    }

Several interesting things have happened here. First, notice the the
action `intf.ping`. We see that the code inserted by `spec` is
present, but the implementation provided by `right_player` is missing.
In effect, the right player has been abstracted away: we see neither
its state nor its actions.  Further, notice that the action `pong` has
been exported to the environment. It contains the monitor code from
`spec` and also the left player's implementation of `pong`. There is a
crucial change, however: the `assert` in the specification of `pong`
has changed to `assume`!

This is an example of assume-guarantee reasoning. The left player
provides a guarantee that it calls `ping` only when the ball is on the
left. However, it *assumes* that the right player only calls `ping`
when the ball is on the right. This is a very common situation in protocols. 
Each participant in the protocol guarantees correctness of its outputs,
but only so long as its inputs are correct.

Finally, notice that the isolate contains only left player's invariant
conjecture. Using this invariant, we can prove the correctness of `ping`:

    $ ivy_check isolate=iso_l pingpong.ivy
    Checking isolate iso_l...
    trying ext:intf.pong...
    trying ext:left_player.async...
    OK

Now let's look at the other isolate:

    type side_t = {left,right}
    individual spec.side : side_t
    relation right_player.ball

    init [spec] spec.side = left
    init [right_player] ~right_player.ball

    conjecture [right_player] right_player.ball -> spec.side = right

    action ext:right_player.async = {
        if right_player.ball {
            {
                call intf.pong;
                right_player.ball := false
            }
        }
    }
    action intf.pong = {
        assert spec.side = right;
        spec.side := left
    }
    action ext:intf.ping = {
        assume spec.side = left;
        spec.side := right;
        right_player.ball := true
    }

This is similar, but now `pong` is verified and `ping` is assumed to be correct.
The state and actions of the laft player are compeltely abstracted away. 





















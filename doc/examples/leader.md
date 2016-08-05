---
layout: page
title: Parameterized systems
---

Many systems are designed to include an arbitray number of similar or
identical components. A good example of such a system is the Internet,
which is designed to accomdate a large number of hosts, all
communicating using the same set of protocols. Another example would
be peer-to-peer protocols such as
[Chord](https://en.wikipedia.org/wiki/Chord_(peer-to-peer)).

We call these *parameterized systems* where the parameter in question
is the number of protocol participants. Ivy allows you to model an
implement parameterized protocol in a particular style. A
*parameterized* object is one in which every component has an initial
parameter of the same type. Here is an example of an object parameterized on type `t`:

    type t

    object foo = {

        function bit(S:t) : bool
	init ~bit(S)

	action set_bit(self:t) = {
	    bit(self) := true
	}
    }

Notice that both the state component `bit` and the action `set_bit`
have a first parameter of type `t`. The parameter of `set_bit` is
suggestively called `self`. This parameter is used in any references
to state components within the action. Thus, object `foo` really acts
like a collection of independent objects or processes, one for each
element of type `t`. The type `t` acts like a reference to one of
these objects.

IVy provides a shorthand for parameterized objects. We can equivalently
write the object `foo` as follows:

    type t

    object foo(self:t) = {

        individual bit : bool
	init ~bit

	action set_bit = {
	    bit := true
	}
    }

Ivy adds the parameter `self` to each state component of `foo`, and
each reference to a component. That is, `self` becomes an implicit
parameter, much as it does in an object-oriented programming language
(except for Python, where the `self` parameter is explicit). It makes
no difference to IVy whether you use implicit or explicit
parameters. You can reason about IVy programs in the same way using
either style.

As we will see later, IVY has special support for parameterized
objects.  For example, you can compile them and run them in separate
process spaces or on different hosts. In addition, when proving
assertions that relate to only one process, you can ignore the
parameter. This can be a good trick for staying within a decidable
fragment.

### Leader election ring

As an example of a parameterized protocol, lets look at the very
simple leader election protocol, introduced in [this paper](...) in
1974.

In this protocol we have a collection of distributed processes
organized in a ring. Each process can send messages to its right
neighbor in the ring and receive message from left neighbor. A process
has a unique `id` drawn from some totally ordered set (say, the
integers). The purpose of the protocol is to discover which process
has the highest `id` value. This process is elected as the "leader".

This protocol itself is trivially simple. Each process transmits its
own `id` value. When it receives a value, it retransmits the value,
but only it is is *greater than* the procees' own `id` value. If a
process receives its own `id`, this value must have travelled all the
way around the ring, so the process knows its `id` is greater than all
others and it declares itself leader.

We'll start with a service specification for this protocol:

    object serv = {

	function pid(X:node.t) : id.t          # map each node to an id

	axiom pid(X) = pid(Y) -> X=Y           # id's are unique

	action elect(v:node.t)                 # called when v is elected leader

	object spec = {
	    before elect {
		assert pid(v) >= pid(X)        # only the max pid can be elected
	    }
	}
    }

This object is parameterized on an abstract datatype `node` that we
will define shortly. Type `node.t` represents a reference to a process
in our system. The servicee specification contains a function `pid` that
maps each node to its unique `id` value. The fact that the `id` values
are unique is guaranteed by the axiom.

The specification has one action `elect` which is called whan a given
node is elected leader. Its specification says that only the node with
the maximum `id` value can be elected.

Now that we know what the protocol is supposed to do, let's define the
protocol itself.  First, we use the explicit parameter style:

    object app = {

	action async(me:node.t) = {
	    call trans.send(node.get_next(me),serv.pid(me))
	}

	implement trans.recv(me:node.t,v:id.t) {
	    if v = serv.pid(me) {       # Found a leader!
		call serv.elect(me)
	    }
	    else if v > serv.pid(me)  { # pass message to next node
		call trans.send(node.get_next(me),v)
	    }
	}

    }

Our protocol implementation referes to two interfaces: the `serv`
interface we just defined, and a network transport interface `trans`
defined below. It also refers to the abstract datatype `node` that we
will also define shortly.

The protocol provides an action `async` that, when called, transmits
the node's `id` to the next process in the ring, defined by the the
action `node.get_next` (here, we used `me` instead of `self` to save
two characters).

The protocol also implements an action of the transport interface
`trans.recv`.  This is called when the process receives a message with
an `id` value `v`. If the value is equal to the process' own `id`, the
process knows it is leader and calls `serv.elect`. Otherwise, if the
received value is greater, it calls `trans.send` to send the value on
to the next node.

Notice that when giving the implementation, we explicitly gave the
parameters of `trans.recv` rather than inheriting them from the
interface specification.  This can avoid confusion and also allows us
to give whatever local names we want to the parameters.

Here is the same object described in the implicit style:

    object app(me:node.t) = {

	action async = {
	    call trans.send(node.get_next(me),serv.pid(me))
	}

	implement trans.recv(v:id.t) {
	    if v = serv.pid(me) {       # Found a leader!
		call serv.elect(me)
	    }
	    else if v > serv.pid(me)  { # pass message to next node
		call trans.send(node.get_next(me),v)
	    }
	}

    }


There is not much difference. Notice that we dropped the parameter
`me` from the action definition. However, references to other objects
still have to have the explicit parameter `me`. The implicit style
mainly shows an advantage when the parameterized object has many state
components.

With our protocol implemented, let's look at the interfaces that it's
built on, starting with the type 'id` values:

    module totally_ordered(t) = {
	relation (X:t < Y:t)
	property [transitivity] X:t < Y & Y < Z -> X < Z
	property [antisymmetry] ~(X:t < Y & Y < X)
	property [totality] X:t < Y | X = Y | Y < X
    }

    module total_order = {
	type t
	instantiate totally_ordered(t)   # t is totally ordered
    }

    instance id : total_order

Notice that we defined a couple of modules that we can re-use later.
The first gives the axioms of a total order. The second defines a
datatype that obeys these axions. We then define our abstract type
`id` to be an instance of `total_order`. Later, we will implement
`id.t` with fixed-width integers.

Now let's look at the type of node references, which is a bit more
interesting:

    module ring_topology = {
	type t

	individual head:t  # ring head
	individual tail:t  # ring tail

	instantiate totally_ordered(t)
	axiom head <= X              # head is minimal
	axiom X <= tail              # tail is maximal

	action get_next(x:t) returns (y:t)

	object spec = {
	    after get_next {
		assert (x = tail & y = head) | (x < y & ~ (x < Z & Z < y))
	    }
	}
    }

    instance node : ring_topology

We start by defining a generic module for types that are organized in a
ring topology.  We use a totally ordered type `t` for the ring
elements. Type `t` has mimimum and maximum elements called `head` and
`tail`. The `get_next` action takes an element `x` and returns the
next element `y` in the ring. The specification says that this is
either the head, if `x` is the tail, or it is some element that is
greater than `x` with no elements in between. This is one way of
specifying a ring topology. Later we will see a different way that can
make the proofs a little simpler. We can implement either version with
fixed-width integers.
 
Finally, we need the service specification for the network transport
layer. It's quite simple:

object trans = {

    relation sent(V:id.t, N:node.t)
    init ~sent(V, N)
    
    action send(dst:node.t, v:id.t)
    action recv(dst:node.t, v:id.t)

    object spec = {
	before send {
	    sent(v,dst) := true
	}
	before recv {
	    assert sent(v,dst)
	}
    }
}

The relation `sent` tells us which values have been sent to which
nodes.  Initially, nothing has been sent. The interface provides two
actions `send` and `recv` which are called, respectively, when a value
is sent or received. The `dst` parameter gives the destination node of
the message.

The specification says that a values is marked as sent when `send`
occurs and a value must be marked sent before it can be received.
This describes a network service that can duplicate or re-order
messages, but cannot corrupt messages.

## Verifying the leader election protocol

Now let's try to verify that our leader election protcol `app` guarantees
its service specification `serv` , assuming the specifications of `trans`,
`node` and `id`. Here is the isolate declaration:

isolate iso_p = app with node,id,trans,serv

We are trying to prove that, when any node calls `serv.elect`, it in
fact has the highest `id`. That is, the `before` specification of
`serv.elect` is a guarantee of `proto` when it calls `serv.elect`.

To get a sense of what we're proving, let's have a look at the
isolate:

    $ ivy_show isolate=iso_app leader_election_ring.ivy

    ... various declarations ...

    action trans.send(dst:node.t,v:id.t) = {
	trans.sent(v,dst) := true
    }

    action ext:trans.recv(dst:node.t,v:id.t) = {
	assume trans.sent(v,dst);
	if v = serv.pid(dst) {
	    call serv.elect(dst)
	}
	else {
	    if v > serv.pid(dst) {
		local loc[0] {
		    call loc[0] := node.get_next(dst);
		    call trans.send(loc[0], v)
		}
	    }
	}
    }

    action serv.elect(v:node.t) = {
	assert serv.pid(v) >= serv.pid(X)
    }

    action ext:app.send(me:node.t) = {
	local loc[0] {
	    call loc[0] := node.get_next(me);
	    call trans.send(loc[0], serv.pid(me))
	}
    }

    action node.get_next(x:node.t) returns(y:node.t) = {
	assume ((x < y & ~(Z:node.t < y & x < Z)) | (x = node.tail & y = node.head))
    }

Notice that the assertion in `serv.elect` is preserved as a guarantee. However,
the other assertions have become assumptions.

Obviously, we will need an inductive invariant at this point. We will
try to discover one using IVy's [CTI
method](client_server_example.html).  We start IVy using this command:

    $ ivy ui=cti isolate=iso_app leader_election_ring.ivy













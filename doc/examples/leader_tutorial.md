---
layout: page
title: Designing and implementing a protocol in Ivy
---

In this tutorial, we'll learn how to take a distributed protocol from
an abstract model to working implementation in Ivy. The example we
will use is a simple ring-based leader election protocol introduced in [this paper](http://dl.acm.org/citation.cfm?id=359108) in
1979.  This is an example of a *parameterized systems*, because the
protocol can have an arbitrary number of similar participants. We will
see how parameterized protocols are modeled and implemented in Ivy.

In the leader election protocol, we have a collection of distributed
processes organized in a ring. Each process can send messages to its
right neighbor in the ring and receive message from left neighbor. A
process has a unique `id` drawn from some totally ordered set (say,
the integers). The purpose of the protocol is to discover which
process has the highest `id` value. This process is elected as the
"leader".

The protocol itself is trivially simple. Each process transmits its
own `id` value. When it receives a value, it retransmits the value,
but only if it is *greater than* the process' own `id` value. If a
process receives its own `id`, this value must have traveled all the
way around the ring, so the process knows its `id` is greater than all
others and it declares itself leader.

### The service specification

When designing a system in Ivy, we start with a *service
specification*. The service specification describes the inerface of
the system, and tells us what properties the interface should satisfy.
In Ivy, a unit of verification is called an *isolate* (because it is
verified in isolation). An isolate consistes of an *interface*,
consisting of exported procedures and functions, a *specification*,
describing the externally observable properties of the interface, and
an *implementation* the provides executable bodies for interface functions
and procedures.

Here is how the interface and specification of the leader election
service are described in Ivy:

    isolate leader = {

        action tick(self:node)                 # called when a timer expires
        action elect(self:node)                 # called when v is elected leader

        specification {
            before elect {
                ensure forall X. self.pid >= X.pid    # only the max pid can be elected
            }
        }
    }

Procedures in Ivy are called *actions*. Unlike funcitons, actions may
have side effects. The interface of our isolate `leader` consists of
two actions: `tick` is called by the environment when a timer expires
and implemented by `leader`, while `elect` is called by the isolate
when a node is elected leader, and implemented by the
environment. There is no explicit declaration in Ivy as to which
isolate implements a given interface action. Ivy only requires that
each action have at most one implementation.

Notice that each action has a parameter `self` of type `node`. This
parameter acts like a process identifier. It tells us the *location*
in which the action occurs. This is how Ivy represents a
parameterized, distributed system -- an action has a location
determiend by its first parameter.

The `specification` section tells us what is assumed and what
guaranteed by isolate `leader`. In this case, the specification says
only that before calling `elect`, the implementation guarantees that
its `pid` is the maximum among all processes. The guarantee is given
by an `ensure` statement. This is like an `assert` statement in other
languages, which gives a formula that must be true when the statement
executes. The difference is the `ensure` defines an assertion that is
a *guarantee* for the isolate. It is the responsibility of the
implementation of `leader` to make this assertion true, regardless of
what the environment does.

We will pospostpone the definitions the datatype `node` and the
function `pid` that are used in this specification.

### An abstract model of leader election

After specifying the interface of our system, our next task is to
model the protocol abstractly. An abstract model, by hiding details of
the implementation, allows us to focus on the essence of the proof.
Once we have verified an abstract model, we can use the correctness of
the abstract model as a lemma in the proof of various implementations.

An abstract model of a protocol usually as a variety of actions
corresponding to different various steps in the protocol. It has state
variables that typical describe in some abstract way the information
that has been transmitted between parties in the protocol. In the case
of the leader election ring, we have two abstract actions: `send(n,p)`
corresponds node `n` sending pid `p` to the next node in the ring, while
`elect(n)` corresponds to a node `n` declaring
itself leader. We have one state variable called `sent`. This is a
binary relation between pids and nodes, such that `send(P,N)` is true
when pid `P` has been sent to node `N`. When possible, we represent
the abstract state of protocols with relations rather than functions
(i.e., maps) in order to keep our proof obligations within the
decidable EPR fragment.

Here is the representation of the abstract protocol model in Ivy:

    isolate abstract_model = {
        action send(n:node,p:id)
        action elect(n:node)

        specification {
            var sent(V:id,N:node) : bool

            after init {
                sent(V,N) := false;
            }

            before send {
                require p = n.pid & sent(p,n) & p > n.pid;
                sent(n.pid,n.get_next) := true;
            }

            before elect {
                require sent(n.pid,n);
                ensure forall N:node. N.pid <= n.pid;
            }
        }
    } with node,id

Notice that the specification section has a state variable
`sent`. Specification state of an isolate is visible to its
environment, and is often used to help specify properties. On the
other hand, implementation state of an isolate is hidden from its
environment. The variable `sent` is initialized in an `after init`
block.  In the assignment `sent(V,N) := false`, the capitalized
symbols `V` and `N` are placeholders. This represents a simultaneous
update of `sent(V,N)` top false for all values of `V`, `N` (thus
initially, no pids have been sent).

Before an `send(n,p)` event can occur, we require that either `p` is
the pid of node `n`, or that `p` has been sent to `n` and is higher
than the pid of `n`. This is represented by a `require` statement.
The `require` statement is another form of assertion that states a
condtion that is n *assumption* for the isolate. It is the
responsibility of the *environment* to make sure this assertion is
true. Before an `elect(n)` event occurs, we require that node `n` has
been sent its own pid (meaning that this pid must have made a complete
circuit, and hence is as high as than any other pid in the ring).
 
We have one additional specification for `elect`: we ensure that in
fact the pid of node `n` is maximal in the ring. Finally, notice
the declaration `node,id` at the end of the isolate. This tells Ivy
that the correctness of this isolate depends on the specifications of
isolates `node` and `id`. These isolates are abstract datatypes that we
will examine shortly.

### Proving the abstract model

Before continuing, we should prove that our abstract mode is correct
(meaning that the `ensure` condition always holds, assuming that the
environment satisfies the `require` conditions).
We do this by providing an *inductive
invariant*. An inductive invariant is a formula about the state that has
the following key properties:

- *initiation*: It is true in all initial states.

- *consecution*: If it is true in a state, then after executing any
action, the formula remains true.

An inductive invariant for an isolate is guaranteed to hold at all times 
between executions of the interface actions.
An inductive invariant is relatively easy to prove, since
we only have to verify the initiation and consecution properties, a task
which Ivy can usually perform automatically. Often, though, the
invariant properties we really want to prove are not inductive and we
therefore require some cleverness to *strengthen* the desired
invariant to make it inductive.

Ivy makes this step easier by providing tools to visualize the
failures of inductive proofs and suggest possible refinements to the
proof. We start by na\"ively trying to verify the abstract model using
this command:

    $ ivy_check isolate=abstract_model leader.ivy
    
Ivy uses the Z3 theorem prover to try to verify the program
assertions, given the invariants.  Since we have given no invariants,
it effective has to verify that the `ensure` condition holds when the
action `elect` is occurs in any state (and given the specifications of
the datatypes `node` and `id`). This is not the case, so a
counterexample execution is produced (we know a counterexample can be
produced because we are using only the EPR logic, which has the finite
model property).

In the counterexample, we see a graphical representation of a state
with two nodes, in which the node having the smaller pid is receiving
its own pid. Clearly, this state should not be possible. Ivy can help us
to construct a more general statement from this counterexample:

    invariant ~(N.pid < M.pid & sent(N.pid,N))
    
The capital letters in this formula are free variables. THey are
implicitly universally quantifier, so this statment applies to all
nodes `M` and `N`.  It says that it should never be the case that a
node receives its own pid and another node has a greater pid. We add
this invariant to the isolate and try again.

This time, Ivy show us a counterexample to induction with three nodes
in the ring. The nodes occur in the order `0`, `1`, `2`.  Node `2` is
receiving the pid of node `0`, but the pid of node `1` is higher.
This leads to a state in which `0` is receiving its own pid
incorrectly, violating our stated invariant. Clearly, this situation is not
possible, since the pid of `0` cannot bypass node `1` to reach node `2`. Ivy
again helps us to generalize this statement, leading to the following conjectured
invariant:

    invariant ~(L < M & M < N & L.pid < M.pid & sent(L.pid,N))

This says that it is never the case that three nodes occur in the order `L < M < N`,
such that the pid of `L` is less than the pid of `M` and the pid of `L` has reached `N`.
After two more similar counterexamples and strengthenings we reach an inductive invariant
which can be stated as follows:

    invariant ~(N.pid < M.pid & sent(N.pid,N))
    invariant ~(L < M & M < N & L.pid < M.pid & sent(L.pid,N))
    invariant ~(L < M & M < N & M.pid < N.pid & sent(M.pid,L))
    invariant ~(L < M & M < N & n.pid < L.pid & sent(N.pid,M))

At this point, the abstract model is verified and Ivy says `OK`. This
mode of constructing an inductive invariants iteratively by
considering counterexamples is typical. In this process, it is
advantageous to restrict oneself to a decidable logical fragment such
as EPR, so that one can reliable generate true
counterexamples. Otherwise, consideral effort can be wasted in
determing why the theorem prover failed to prove an invariant.
We will next consider *why* the formulas to be proved in this case are
actually in EPR.

### Abstract datatypes

In important trick for keeping proof obligations in a decidable
fragment is to use *asbtract datatype*. Consider in our case the types
`node` and `pid`. If these are represented by integers (or in the case
of `node`, the integers modulo a constant) the above invariant is
certainly correct. However, this would take us outside EPR, since the
`<` sign would be *interpreted* as the arithmetic less-than
relation. This would take us not only outside of EPR, but outside of
the richer fragment FAU suppeort by Z3.

It turns out, however, that we don't need to know that the `node` and
`id` types are integers to do the proof. This is an unnecesarily
strong assumption. Instead, we only need some simple properties of
these types that *are* expressible in EPR.

For example, we do need the fact that both types are totally ordered
(without these facts, Ivy will give a counterexample). We can write down the
total order proerties as follows:

    module totally_ordered(t) = {
        property [transitivity] X:t < Y & Y < Z -> X < Z
        property [antisymmetry] ~(X:t < Y & Y < X)
        property [totality] X:t < Y | X = Y | Y < X
    }

A `module` in Ivy is a kind of template. This template can be
instantiated for any type `t` and states that the `<` relation on type
`t` is totally ordered.  This is not an assumption: the stated
properties must be *proved* for each such type.

As an example, the `id` abstract datatype is declared as follow:

    isolate id = {
        type this
        specification {
            instantiate total_order_properties(this)
        }

        implementation {
            interpret this -> bv[64]
        }
    }

The isolate `id` exports a type as part of its interface. The name of
this type is also `id`, which we declare using the special notation
`type this`. The specification *instantiates* the total order
properties for type `id`. This means that the environment can rely on
these properties.  The *implementation* section tells us that the tpye
`id` is actually represented by bit vectors of length 64. The notation
`bv[64]` stands for the *theory* of 64-bit vectors, which is built
into Z3, and includes interpretations of (unsigned) arithmetic
operators and inequalities. If we included this theory in the
specification of `id`, Ivy would try to use it in verifying our
abstract model. However, since we hide it in the implementation, the
proof of the abstract model uses only the total order properties in
the specification section.

The `id` datatype requires verification. Ivy can accomplish this automatically using
thsi command:

    $ ivy_check isolate=id leader.ivy
    
Ivy uses the built-in bit vector theory of Z3 to prove the total order properties.
This is easy, because it requires no reasoning about quantifiers over long bit vectors,
as all the quantifiers in the propertis become Skolem symbols.

The `node` datatype is a little more complex. This is because we need
a `next` operator gives the next node in the ring. 

    isolate node = {
        type this
        action get_next(x:this) returns (y:this)

        specification {

            instantiate total_order_properties(this)   

            after get_next {
                ensure (y <= X & X <= x) | (x < y & ~ (x < Z & Z < y))
            }
        }

        implementation {
            instantiate iterable
            implement get_next {
                y := 0 if x = max else x.next;
            }
        }
    }

The `node` isolate provides a action `get_next` that returns the next
node in the ring. This specified by an `ensure` statement that must
hold when the action returns. This says that either there are no
values between the input `x` and the output `y`, or `x` is the maximum
value of the type and `y` is the minimum (in other words, the ring
wraps around from the last element to the first).

In the implementation of `node`, we could use a fixed datatype (for
example, a particalar integer subrange or bit vector length). However,
we want our system to be *parameterized* so that we can instantiate
and run it for any size ring. To accomplish this, we use a built-in
module called `iterable`. It provides a finite sequence of values
whose length is determined by a run-time parameter. It defines a
symbol `max` that gives the last element of the sequence and an action
`next` that gives the next element in the sequence if there is
one. With these operations, we can implement the ring `get_next`
operation in a way that Z3 can prove its correctness.

Notice what we have accomplished here: we have used modularity to
hide the theories `bv[64]` and `iterable`. In this way we have eliminated
arithmetic reasoning from the verificatoon of our abstract model.
This is important because mixing arithmetic with quantifiers could
make the theorem prover behave unreliably. It also makes the 
abstract model more generic. That is, we know that we can substitute
for `node` and `id` any datatypes that satisfy their specifications.

A final element that we require is the map from nodes to process ids.
The map could be chose randomly. However, we will make it a run-time
parameter. We can declare it like this:

    isolate node = { ...
        parameter pid(N:this) : id
    }

### Implementing the protocol

Now it is time to implement the service specification. To make things
interesting, we will add a small optimization to the
implementation. That is, rather than having a node pass on every id it
receives, it will instead accumulate the highest pid seen and
periodically pass this along.

To implement the protocol, we will need a transport service that sends
messages on an actual network. The Ivy standard library provides some
simple services for this purpose. We will use one called `udp_simple`
that implements an unreliable datagram service using UDP. The service 
specification of `udp_smple` looks like this:

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
                ensure sent(v,dst)
            }
        }
    }

It takes a type of process identifer `addr` and a type of packet `pkt`
and provides actions for sending and receiving packets. Notice that
the first parameter of each action defines the *location* where the
event occurs (so it is the destination for a receive event and the
source for a send event). The specification records only which packets
have been sent to which destinations, and ensures only that a packet
received at a destination must have been sent to that destination.  Of
course, the fact that the actual operating system and network
implementing the `upd_simple` can't be proved (apart form the fact the
the OS is hard to verify, we can prove nothing about the physical
configuration of the hardware). We can *test* that the actual system
conforms to this specification, but formally it remains an assumption.

We create an instance of the `udp_simple` service for our leader
election protocol like this:

    instantiate net : udp_simple(node,id)
    
That is, our endpoints are nodes and our messages are pids. We also
use a timer service to call us periodically. Here is its interface:

    module timeout_sec = {
        action timeout
    }

Using these system services, here is the implementation of `leader`:

isolate leader = {

    action tick(self:node)                 # called when a timer expires
    action elect(v:node)                 # called when v is elected leader

    specification {
	before elect {
	    ensure v.pid >= node.pid(X)    # only the max pid can be elected
	}
    }

    implementation {
        implement tick(self:node) {
            call abstract_protocol.send(self);              # ghost
	    call trans.send(self.get_next,self.pid);
        }
        
        implement trans.recv(self:node,v:id) {
            if v = self.pid {  # Found a leader
                call abstract_protocol.elect(self);
                call elect(self);
            }
	    else if v > self.pid  { # pass message to next node
                call abstract_protocol.pass(self,v);
	        call trans.send(self.get_next,v);
            }
        }
    }

    private {
        invariant trans.sent(V,N) -> abstract_protocol.sent(V,N)
    }
} with node, id, trans, abstract_protocol




These two objects are parameterized on an abstract datatype `node`
that we will define shortly. Type `node.t` represents a reference to a
process in our system. The `asgn` object defines an assignment of `id`
values to nodes, represented by the function `pid`.  The fact that the
`id` values are unique is guaranteed by the axiom `injectivity`.




where the parameter in question
is the number of protocol participants. Ivy allows you to model an
implement parameterized protocol in a particular style. A
*parameterized* object is one in which every component has an initial
parameter of the same type. Here is an example of an object parameterized on type `t`:





comake an abstract model of a
simple protocol and prove a property of it using an *inductive
invariant*. This is usually the first step in designing and
implementing a protocol in Ivy. 

An invariant of a system is a formula about the system's state that is
always true.  Invariants are the simplest class of properties that we
specify about systems. An *inductive* invariant is a formula or a set
of formulas that has the following key properties:

- *initiation*: It is true in all initial states of the program.

- *consecution*: If it is true in a state, then after executing any
exported action, the formula remains true.

Every inductive invariant is an invariant, but not every invariant is
inductive. An inductive invariant is relatively easy to prove, since
we only have to verify the initiation and consecution properties, a task
which Ivy can usually perform automatically. Often, though, the
invariant properties we really want to prove are not inductive and we
therefore require some cleverness to *strengthen* the desired
invariant to make it inductive.

As we will see, Ivy makes this step easier by providing tools to
visualize the failures of inductive proofs and suggest possible
refinements to the proof.

# An abstract protocol model

The following Ivy program is a very abstract model of a semaphore
protocol.  We have a collection of clients and a collection of
servers. Each server has a semaphore which can be held by at most one
client at a time.



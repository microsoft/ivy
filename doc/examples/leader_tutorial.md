---
layout: page
title: Designing and implementing a protocol in Ivy
---

In this tutorial, we'll learn how to take a distributed protocol from
an abstract model to working implementation in Ivy. The example we
will use is a simple ring-based leader election protocol introduced in
[this paper](http://dl.acm.org/citation.cfm?id=359108) in
1979.  The Ivy source code is in the file `leader_tutorial.ivy`.
This is an example of a *parameterized system*, because the
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
specification*. The service specification describes the interface of
the system, and tells us what properties the interface should satisfy.
In Ivy, a unit of verification is called an *isolate* (because it is
verified in isolation). An isolate consists of an *interface*,
containing exported types, procedures and functions, a
*specification*, describing the externally observable properties of
the interface, and an *implementation* that provides executable bodies
for interface functions and procedures, as well as variables and theories
that are hidden from the isolate's environment. 

Here is how the interface and specification of the leader election
service are described in Ivy:

    isolate leader = {

        action elect(self:node)

        specification {
            before elect {
                ensure pid(self) >= pid(X)
            }
        }
    }

Procedures in Ivy are called *actions*. Unlike functions, actions may
have side effects. The external interface of our isolate `leader` consists of
one action, which is a callback: `elect` is called by the isolate
when a node is elected leader, and implemented by the
environment. There is no explicit declaration in Ivy as to which
isolate implements a given interface action. Ivy only requires that
each action have at most one implementation.

The `elect` action has parameter `self` of type `node`. This
parameter acts like a process identifier. It tells us the *location*
in which the action occurs. This is how Ivy represents a
parameterized, distributed system -- an action has a location
determined by its first parameter.

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

We will postpone the definitions the datatype `node` and the
function `pid` that are used in this specification.

### An abstract model of leader election

After specifying the interface of our system, our next task is to
model the protocol abstractly. An abstract model, by hiding details of
the implementation, allows us to focus on the essence of the proof.
Once we have verified an abstract model, we can use the correctness of
the abstract model as a lemma in the proof of various implementations.

An abstract model of a protocol usually has a variety of actions
corresponding to various steps in the protocol. It has state
variables that typical describe in some abstract way the information
that has been transmitted between parties in the protocol. In the case
of the leader election ring, we have two abstract actions: `send(n,p)`
corresponds node `n` sending pid `p` to the next node in the ring, while
`elect(n)` corresponds to a node `n` declaring
itself leader. We have one state variable called `sent`. This is a
binary relation between pids and nodes, such that `sent(P,N)` is true
when pid `P` has been sent to node `N`. When possible, we represent
the abstract state of protocols with relations rather than functions
(i.e., maps) in order to keep our proof obligations within the
decidable EPR fragment.

Here is the representation of the abstract protocol model in Ivy:

    isolate abstract_model = {
        action send(n:node,p:id)
        action elect(n:node)

        specification {
            relation sent(V:id,N:node)

            after init {
                sent(V,N) := false;
            }

            before send {
                require sent(p,n) & p > pid(n) | p = pid(n);
                sent(p,n.get_next) := true;
            }

            before elect {
                require sent(pid(n),n);
                ensure forall N. pid(N) <= pid(n);
            }
        }
    } with node, id, pid_injective

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
condition that is n *assumption* for the isolate. It is the
responsibility of the *environment* to make sure this assertion is
true. Before an `elect(n)` event occurs, we require that node `n` has
been sent its own pid (meaning that this pid must have made a complete
circuit, and hence is as high as than any other pid in the ring).
 
We have one additional specification for `elect`: we ensure that in
fact the pid of node `n` is maximal in the ring. Finally, notice the
declaration `with node,id,pid_injective` at the end of the
isolate. This tells Ivy that the correctness of this isolate depends
on the specifications of isolates `node` and `id`. These isolates are
abstract datatypes that we will examine shortly. We also use an axiom
`pid_injective` (which we will examine later) which states that the
pids of the nodes are distinct. Without this fact, the protocol
doesn't work, since a node could receive its own pid without that
value having made a full tour of the ring.

### Proving the abstract model

Before continuing, we should prove that our abstract model is correct
(meaning that the `ensure` condition always holds, assuming that the
environment satisfies the `require` conditions).  We do this by
providing an *inductive invariant*. An inductive invariant is a
formula about the state that has the following key properties:

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
proof. We start by naively trying to verify the abstract model using
this command:

    $ ivy_check isolate=abstract_model trace=true leader_tutorial_no_proof.ivy
    
Ivy uses the Z3 theorem prover to try to verify the program
assertions, given the invariants.  Since we have given no invariants,
it effectively has to verify that the `ensure` condition holds when the
action `elect` is occurs in any state (and given the specifications of
the datatypes `node` and `id`). This is not the case, so a
counterexample execution is produced (we know a counterexample can be
produced because we are using only the EPR logic, which has the finite
model property).

The counterexample trace starts in a state with two nodes, in which
the node having the smaller pid is receiving its own pid. Clearly,
this state should not be possible. We can rule out this state (and others like it)
be dding the following invariant to the isolate:

    invariant ~(N.pid < M.pid & sent(N.pid,N))
    
The capital letters in this formula are free variables. They are
implicitly universally quantifier, so this statement applies to all
nodes `M` and `N`.  It says that it should never be the case that a
node receives its own pid and another node has a greater pid. In fact,
Ivy can help us to construct this invariant from the counterexample (see 
[this tutorial](http://microsoft.github.io/ivy/examples/leader.html)).

We add this invariant to the isolate and try again.  This time, Ivy
show us a counterexample to induction with three nodes in the
ring. The nodes occur in the order `0`, `1`, `2`.  Node `2` is
receiving the pid of node `0`, but the pid of node `1` is higher.
This leads to a state in which `0` is receiving its own pid
incorrectly, violating our stated invariant. Clearly, this situation
is not possible, since the pid of `0` cannot bypass node `1` to reach
node `2`. This leads to the following conjectured invariant (which
again Ivy can help us construct):

    invariant ~(L < M & M < N & L.pid < M.pid & sent(L.pid,N))

This says that it is never the case that three nodes occur in the order `L < M < N`,
such that the pid of `L` is less than the pid of `M` and the pid of `L` has reached `N`.
After two more similar counterexamples and strengthenings we reach an inductive invariant
which can be stated as follows:

    private {
        invariant ~(pid(N) < pid(P) & sent(pid(N),N))
        invariant ~(L < M & M < N & pid(L) < pid(M) & sent(pid(L),N))
        invariant ~(L < M & M < N & pid(M) < pid(N) & sent(pid(M),L))
        invariant ~(L < M & M < N & pid(N) < pid(L) & sent(pid(N),M))
    }
    
We put the invariants inside a private section, so that they are
hidden from other isolates.

At this point, the abstract model is verified and Ivy says `OK`. This
mode of constructing an inductive invariants iteratively by
considering counterexamples is typical. In this process, it is
advantageous to restrict oneself to a decidable logical fragment such
as EPR, so that one can reliable generate true
counterexamples. Otherwise, considerable effort can be wasted in
determining why the theorem prover failed to prove an invariant.
We will next consider *why* the formulas to be proved in this case are
actually in EPR.

### Abstract datatypes

An important trick for keeping proof obligations in a decidable
fragment is to use *abstract datatype*. Consider in our case the types
`node` and `pid`. If these are represented by integers (or in the case
of `node`, the integers modulo a constant) the above invariant is
certainly correct. However, this would take us outside EPR, since the
`<` sign would be *interpreted* as the arithmetic less-than
relation. This would take us not only outside of EPR, but outside of
the richer fragment FAU support by Z3.

It turns out, however, that we don't need to know that the `node` and
`id` types are integers to do the proof. This is an unnecessarily
strong assumption. Instead, we only need some simple properties of
these types that *are* expressible in EPR.

For example, we do need the fact that both types are totally ordered
(without these facts, Ivy will give a counterexample). We can write down the
total order properties as follows:

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
            instantiate totally_ordered(this)
        }

        implementation {
            interpret this -> bv[32]
        }
    }

The isolate `id` exports a type as part of its interface. The name of
this type is also `id`, which we declare using the special notation
`type this`. The specification *instantiates* the total order
properties for type `id`. This means that the environment can rely on
these properties.  The *implementation* section tells us that the type
`id` is actually represented by bit vectors of length 32. The notation
`bv[32]` stands for the *theory* of 32-bit vectors, which is built
into Z3, and includes interpretations of (unsigned) arithmetic
operators and inequalities. If we included this theory in the
specification of `id`, Ivy would try to use it in verifying our
abstract model. However, since we hide it in the implementation, the
proof of the abstract model uses only the total order properties in
the specification section.

The `id` datatype requires verification. Ivy can accomplish this automatically using
this command:

    $ ivy_check isolate=id leader.ivy
    
Ivy uses the built-in bit vector theory of Z3 to prove the total order properties.
This is easy, because it requires no reasoning about quantifiers over long bit vectors,
as all the quantifiers in the properties become Skolem symbols.

The `node` datatype is a little more complex. This is because we need
a `next` operator gives the next node in the ring. In the
implementation of `node`, we could use a fixed datatype (for example,
a particular integer subrange or bit vector length). However, we want
our system to be *parameterized* so that we can instantiate and run it
for any size ring. To accomplish this, we use a built-in module called
`iterable`. It provides a finite sequence of values whose length is
determined by a run-time parameter. It defines a symbol `max` that
gives the last element of the sequence and an action `next` that gives
the next element in the sequence if there is one.

    instance node : iterable

We can then refine this built-in type by giving it additional traits:

    object node = { ...
        action get_next(x:this) returns (y:this)

        specification {
            after get_next {
                ensure (y <= X & X <= x) | (x < y & ~ (x < Z & Z < y))
            }
        }

        implementation {
            implement get_next {
                y := 0 if x = node.max else x.next;
            }
        }
    }

The `node` isolate provides an action `get_next` that returns the next
node in the ring. This specified by an `ensure` statement that must
hold when the action returns. This says that either there are no
values between the input `x` and the output `y`, or `x` is the maximum
value of the type and `y` is the minimum (in other words, the ring
wraps around from the last element to the first). In the
implementation of `get_next`, we return 0 for `max` and the next value
otherwise. The properties of `iterable` are enough for Z3 to prove the
`ensure` condition of `get_next` (in fact, this proof uses only EPR).

Notice what we have accomplished here: we have used modularity to
hide the theories `bv[32]` and `iterable`. In this way we have eliminated
arithmetic reasoning from the verification of our abstract model.
This is important because mixing arithmetic with quantifiers could
make the theorem prover behave unreliably. It also makes the 
abstract model more generic. That is, we know that we can substitute
for `node` and `id` any datatypes that satisfy their specifications.

A final element that we require is the map from nodes to process ids.
The map could be chosen randomly. However, we will make it a run-time
parameter. We can declare it like this:

    parameter pid(N:this) : id

    axiom [pid_injective] pid(N) = pid(M) -> N = M

Since the pids will be provided by the user at run time, there is no
way us to prove that all the pids are distinct. Instead we take it as
an *axiom*. We use this axiom when proving the abstract model.

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
specification of `udp_simple` looks like this:

    module udp_simple(addr,pkt) = {

        import action recv(dst:addr,v:pkt)
        export action send(src:addr,dst:addr,v:pkt)

        specification {
            var sent(V:pkt, N:addr) : bool
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

It takes a type of process identifier `addr` and a type of packet `pkt`
and provides actions for sending and receiving packets. Notice that
the first parameter of each action defines the *location* where the
event occurs (it is the destination for a receive event and the
source for a send event). The specification records only which packets
have been sent to which destinations, and ensures only that a packet
received at a destination must have been sent to that destination.  Of
course, the fact that the actual operating system and network
implement the `upd_simple` specification can't be proved (apart form the fact the
the OS is hard to verify, we can prove nothing about the physical
configuration of the hardware). We can *test* that the actual system
conforms to this specification, but formally it remains an assumption.

We also use a system timer service to call us periodically. Here is its
interface:

    module timeout_sec = {
        action timeout
    }

This interface doesn't actually specify anything formally about the timer service.
The service calls action `timeout` once per second, but Ivy doesn't provide a way
to specify real time properties and our protocol doesn't depend on them.

Using these system services, here is the implementation of `leader`:

    isolate leader = { ...

        implementation {

            instantiate net : udp_simple2(node,id)

            instantiate timer(N:node) : timeout_sec

            var highest(N:node) : id

            after init {
                highest(N) := pid(N);
            }

            implement timer.timeout(self:node) {
                call abstract_model.send(self,highest(self));
                call net.send(self,self.get_next,highest(self));
            }

            implement net.recv(self:node,v:id) {
                if v = pid(self) { 
                    call abstract_model.elect(self);
                    call elect(self);
                }
                else if v > highest(self)  { 
                    highest(self) := v;
                }
            }
        }

    } with node, id, abstract_model

Our implementation of `leader` contains an instance `net` of `udp_simple`,
with `node` as the address type and `id` as the packet type. It also
contains a parameterized collection of instances of the `timeout_sec`
service. That is, there is one instance of `timeout_sec` for each node.

The state of the node is capture by one state variable, `highest`,
representing the highest pid seen so far by the node. Notice that this
variable is also parameterized, since there is one instance of it per node.
Initially, we set the value of `highest(N)` to be the pid of node `N`.
This is another example of a parameterized assignment. In this case, the
assigned value depends on the parameter `N`. 

Now we implement two actions. The first is `timer.timeout`. When a
timeout occurs, we send the highest pid we have seen to the next node
in the ring.  We also create a corresponding abstract model event by
calling its `send` action.  When this occurs, we execute the `require`
statement of `send` in the abstract model, which means we must verify
that node `n` is either sending its own pid, or a higher pid that has
been sent to it in the past. IN other words, the `require` condition is an
*assumption* for the `abstract_model` isolate, but a *guarantee* for
the `leader` isolate.  Assuming the condition holds the abstract model's
specification state is updated to reflect the send action. 

When a network receive event occurs, the action `net.recv` is
called. Because of the `require` statement in the specification of
`udp_simple`, the caller of this action guarantees that the received
message has been sent in the past to node `n`. If node `n` receives
its own pid, it has the maximum pid.  It therefore calls the abstract
model `elect` action. This action has a `require` condition that in
fact the pid of `n` has been sent to `n` in the abstract model.  The
implementation must guarantee this condition. If this holds, then the
abstract model ensures that in fact the pid of node `n` is
maximal. Thus, in the next step when we call the `elect` action of
`leader`, we know that its precondition is satisfied.  In effect, we
have used `abstract_model` as a lemma in the proof of `leader`. If we
satisfy its `require` conditions, we can rely on its `ensure`
conditions. This is very similar in concept to the use of functions
and procedures as lemmas in languages such as Dafny and F*. The
difference here is that we are using a stateful interface as a lemma.

In the `with` clause of `leader`, we specify `abstract_model`, since
we use the specification of `abstract_model` to prove `leader`. Notice
that we don't specify the axiom `pid_injective`, because it isn't
needed for the proof. This axiom has been effectively hidden by the
abstract model, and replaced by its `ensure` condition. This kind of hiding can
useful to keep our proof obligations in the prover's decidable fragment (though
this is not needed here).

To finish the program, we add this declaration:

    import leader.elect
    
This says that the `elect` action of the `leader` isolate will be
implemented by the run-time environment. 

### Proof of the implementation

No we have to do the proof. That is, we have to prove that in fact
`leader` guarantees the requirements of the abstract mode actions it
calls, and that, given the assurances made by the abstract model, it
satisfies its own specification.

We can ask Ivy to do the verification like this:

    $ ivy_check isolate=leader leader.ivy
    
Ivy will show us a counterexample to induction. In the counterexample,
we may see a state in which node `n` in `leader` sends its `highest`
pid, but this pid has never been sent in the abstract model. We need
to specify an inductive invariant to show that the two models stay in
sync. We need to say that the `highest` value of each node has been
sent to that node in abstract model, or is its own pid. We also have
to say that every message sent in `net` has also been sent in the
abstract model.  Finally, we have to say that the `highest` value of
`n` is at least as large as its own pid. Each of these invariants can
be derived by considering counterexamples to induction. Here is our invariant
for leader:

    invariant highest(N) = pid(N) | abstract_model.sent(highest(N),N)
    invariant net.sent(V,N) -> abstract_model.sent(V,N)
    invariant highest(N) >= pid(N)

Notice that we do not have to concern ourselves here with the
invariants that were used to prove correctness of `elect`. This is
guaranteed to us by `abstract_model`. The invariant we used as a joint
invariant of `leader` and `abstract_model`. We can also think of it as
a *refinement relation* since it gives a correspondence between states
of the two isolates that proves that every action of `leader` corresponds to
an appropriate action of `abstract_model`. In general, the invariants of an isolate
refer to its own state and the *specification* state of the isolates it depends on, but not the implementation state, which is hidden.

### Abstracting a distributed implementation

We wrote `leader` as a sequential reactive program (reactive meaning
it only acts in reaction to events in its environment). Runs of this
sequential program can be thought of as concurrent runs in which each
action call occurs in a location (i.e., a separate process space) that
is determined by its first parameter. This illusion is maintained so
long as each action refers only to state that is stored in its own
location.  For example, the implementation of `net.recv` may refer to
`highest(n)`, where `n` is its location, but not to any other element
of `highest`. If this condition holds, we say the parameterized
program is *non-interfering*. From a non-interfering program, the Ivy compiler
can construct an executable corresponding to a single location `n`. This program is called
an `extract`. We specify it like this:

    extract code(n:node) = leader(n), pid(n), node, id

The extract is parameterized on a node `n`. It consists of the `leader` isolate
for parameter `n`, the value of the `pid` map for `n`, as well as the node and
id isolates (which are not parameterized, and which therefore cannot have state). 

When we extract code, the specification sections of the isolates are
erased.  The specification state variables and code (including
assertions) are not present in the extract. Ivy verifies that this
erasure is sound, in the sense that the erased code has no effects
that are visible to the remaining code (including non-termination).
This means that the observable behavior of the program is not affected
by erasure of the specifications. In particular, since out abstract
model is a pure specification, it is not extracted. The calls from
`leader` to `abstract_model` are "ghost" code, having no effect.

We still need to know, however, that the distributed program is in
some sense equivalent to the sequential program that we verified.  Ivy
guarantees that the distributed version is serializable, in the sense
the every concurrent execution is observably equivalent to a
sequential execution, in which each action completes atomically. The
proof of this uses Lipton's theory of left- and right-movers (in
particular, each incoming call to the program is a right-mover, while
each outgoing call is a left-mover). The validity of this argument
(which is made "on paper") depends on the fixed specifications of the
run-time services.

We compile the code with this command:

    $ ivyc leader.ivy
    
This produces a binary executable file called `leader` (under
Unix-like operating systems).

### Running the leader election protocol

We can now run the protocol for a chosen ring size. The `leader` binary
takes three parameters on the command line: `node.size` (the size
parameter of the `node` type) `pid` (the pid value for the node) and
`n` (the node identifier, in the range `[0,node.size)`. The order of these
parameters on the command line is determined by their order of declaration
in the program.

For a ring of size three, we can create three terminals named `A`, `B`, `C`
and execute the following commands:

    A: $ ./leader 3 1 0
    B: $ ./leader 3 3 1
    C: $ ./leader 3 0 2

The UDP port numbers for these process are chosen by a default scheme -- for a real
system we would have to provide the IP addresses of all of the processes.
Notice that process `B` should be the leader, since it has the highest pid. In fact,
after three seconds, we see this output on terminal `B`:

    < leader.elect
    < leader.elect
    < leader.elect
    ...

The compiler gave `leader.elect` a default implementation, which is simply to
print a log message.  We can also compile the program as library and provide
our own implementation of `leader.elect` in C++.

### Conclusion

We have seen how to use Ivy to implement a distributed protocol. There are three
main components: a service specification, an abstract model and an implementation.
The abstract model is not absolutely necessary, but it can simplify the proof process,
by allowing us to disregard implementation details. The abstract model state is usually
expressed using only relations, so we can do the proof in the decidable fragment EPR.
To achieve this, we also hide the full theories of the datatypes inside isolates,
using only the abstract properties of these types that are needed for by the protocol.
The implementation is then specified and proved using the abstract mode as a lemma, and
using system services provided by the Ivy run-time. The abstract model can also be used
theories from the implementation.

The resulting proved parameterized sequential program can then be extracted to an
executable distributed program with an arbitrary number of processes, provided some
non-interference conditions are met. 


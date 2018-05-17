---
layout: page
title: Model Checking
---

Constructing an inductive invariant manually is an effective proof
technique, but it can be both challenging and time consuming. In some
cases, we can apply the technique of [Model
Checking](https://en.wikipedia.org/wiki/Model_checking) to
automatically construct a proof, or to reduce the burden of manually
constructing invariants. When using model checking, we simply state
the property of the program that we want to hold, and the model
checker determines whether the program satisfies the property or not.
If not, it provides a behavioral trace that shows why the property
does not hold.

The catch is that model checkers only work reliably for finite-state
systems. In practice, that means that each IVy type must be
interpreted as some finite set, for example, as a finite sub-range of
the integers, or as a fixed-width bit vector. 

Checking finite instances of protocols
======================================

Take our simple client-server example from the section
[Invariants](client_server_example.html).

    type client
    type server

    relation link(X:client, Y:server)
    relation semaphore(X:server)

    after init {
        semaphore(W) := true;
        link(X,Y) := false
    }       

    action connect(x:client,y:server) = {
      require semaphore(y);
      link(x,y) := true;
      semaphore(y) := false
    }

    action disconnect(x:client,y:server) = {
      require link(x,y);
      link(x,y) := false;
      semaphore(y) := true
    }

    export connect
    export disconnect

    invariant link(X,Y) & link(Z,Y) -> X = Z

To prove the invariant property, we needed an auxiliary invariant.
With model checking, we don't need to proving an auxiliary invariant,
but we have to make the types finite. Let's add the following declarations to
the example:

    interpret client -> {0..2}
    interpret server -> {0..1}
    
    attribute method = mc

The first two declarations tell IVy to interpret `client` and `server` as finite
sub-ranges of the integers. We have exactly three clients and two servers. The last
declaration tells IVy to prove the invariant using model checking. Here's what IVY has to say:

    $ ivy_check client_server_example_mv.ivy 

    Isolate this:

    ********************************************************************************

    client_server_example_mv.ivy: line 26: Model checking invariant

    Instantiating quantifiers (see ivy_mc.log for instantiations)...
    Expanding schemata...
    Instantiating axioms...

    Model checker output:
    --------------------------------------------------------------------------------
    ABC command line: "read_aiger /tmp/tmpwC0AcP.aig; pdr; write_aiger_cex  /tmp/tmpwC0AcP.out".

    Invariant F[1] : 4 clauses with 5 flops (out of 11) (cex = 0, ave = 4.00)
    Verification of invariant with 4 clauses was successful.  Time =     0.00 sec
    Property proved.  Time =     0.02 sec
    There is no current CEX.
    --------------------------------------------------------------------------------

    PASS

    OK

IVy converted the program verification problem into a circuit
verification problem and gave it to a hardware model checker called
[ABC](https://people.eecs.berkeley.edu/~alanmi/abc/abc.htm). ABC
searched the full state space of the program and determined that our
claimed invariant always holds. For now ignore the messages about
quantifiers, schemata and axioms.  We'll see the relevance of those
later.


Suppose we made a mistake, and forgot the requirement the that
sempahore has to be up when connecting a client (the `require`
statement in action `connect`). Here's what we would get:

    $ ivy_check client_server_example_mv.ivy 

    Isolate this:

    ********************************************************************************

    client_server_example_mv.ivy: line 27: Model checking invariant

    Instantiating quantifiers (see ivy_mc.log for instantiations)...
    Expanding schemata...
    Instantiating axioms...

    Model checker output:
    --------------------------------------------------------------------------------
    ABC command line: "read_aiger /tmp/tmpnyvbNU.aig; pdr; write_aiger_cex  /tmp/tmpnyvbNU.out".

    Output 0 of miter "/tmp/tmpnyvbNU" was asserted in frame 4.  Time =     0.02 sec
    --------------------------------------------------------------------------------

    FAIL

    Counterexample trace follows...
    ********************************************************************************

    path:
        client_server_example_mv.ivy: line 10: semaphore(W) := true
            semaphore(0) = true
            semaphore(1) = true
        client_server_example_mv.ivy: line 11: link(X,Y) := false
    state:
        semaphore(0) = true
        semaphore(1) = true
        link(0,0) = false
        link(1,0) = false
        link(2,0) = false
        link(0,1) = false
        link(1,1) = false
        link(2,1) = false

    path:
            fml:y = 0:server
            fml:x = 0:client
        client_server_example_mv.ivy: line 17: link(fml:x,fml:y) := true
            link(0,0) = true
        client_server_example_mv.ivy: line 18: semaphore(fml:y) := false
    state:
        semaphore(0) = false
        semaphore(1) = true
        link(0,0) = true
        link(1,0) = false
        link(2,0) = false
        link(0,1) = false
        link(1,1) = false
        link(2,1) = false

    path:
            fml:y = 1:server
            fml:x = 0:client
        client_server_example_mv.ivy: line 17: link(fml:x,fml:y) := true
            link(0,1) = true
        client_server_example_mv.ivy: line 18: semaphore(fml:y) := false
    state:
        semaphore(0) = false
        semaphore(1) = false
        link(0,0) = true
        link(1,0) = false
        link(2,0) = false
        link(0,1) = true
        link(1,1) = false
        link(2,1) = false

    path:
            fml:y = 0:server
            fml:x = 1:client
        client_server_example_mv.ivy: line 17: link(fml:x,fml:y) := true
            link(1,0) = true
        client_server_example_mv.ivy: line 18: semaphore(fml:y) := false
    state:
        semaphore(0) = false
        semaphore(1) = false
        link(0,0) = true
        link(1,0) = true
        link(2,0) = false
        link(0,1) = true
        link(1,1) = false
        link(2,1) = false

    ********************************************************************************

IVy printed out a trace of execution of the program that violates the
invariant. The trace alternates *paths* and *states*. A path is an
execution path through some action (the first action being the
intializer). It shows the sequence of statements executed and any
changes to the program variables (including local variables). A state
shows that values of the program variables between actions. Notice
that in the final state, clients 0 and 1 are both linked to server 0,
violating the invariant.  The semaphore is down, but thise didn't
prevent client 1 from being connected in the fourth action, because we
forgot the requirement that the server's semaphore be up.

Of course, we can't conclude from this that the program is correct for
any number of clients or servers. We've only checked a particular
case. Still, if we can check reasonable large instances, we have
pretty good confidence that the invariant holds, and we can then go
about strengthening the invariant so it is inductive for any number fo
clients and servers (that is, without the `interpret` declarations),

Model checking parameterized protocols with abstraction
=======================================================

Another way that model checking can help us is by verifying a finite
*abstraction* of the program. Abstraction means limiting the reasoning
that we can perform. For example, we might pick two representative clients
and one representaticve server



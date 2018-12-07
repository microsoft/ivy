---
layout: page
title: Hello, world!
---

Having specified and verified a protocol or two, it's natural to want
to try actually running a verified protocol. Ivy programs can be
compiled into the C++ language and executed in various ways.

## Generating a REPL

The simplest way to try out an Ivy program is to generate a
read-eval-print loop (REPL). We'll start with the closest thing we can
write to the "Hello, world!" program in Ivy. Ivy programs are
*reactive*, meaning that they only do something when called upon by
their environment.  This means we can't actually write a program that
spontaneously prints a message. Here is an approximation:

    #lang ivy1.7

    action world

    action hello = {
        call world
    }

    export hello
    import world
    
This program provides an action `hello` that calls action `world`
provided by the environment. Let's try compiling and running this program:

    $ ivy_to_cpp target=repl helloworld.ivy
    $ ls helloworld.*
    helloworld.cpp  helloworld.h  helloworld.ivy

The command `ivy_to_cpp` generated header and implementation files `helloworld.h` and
`helloworld.cpp`. We can compile them to produce an executable file like this:

    $ c++ -o helloworld helloworld.cpp

Now let's run the program:

    $ ./helloworld
    >

The prompt `>` tells us we're in the REPL. We can now call an exported action:

    > hello
    world

When we call `hello` the program calls `world`. 

# Input and output

That was exciting. To make things more interesting, let's try computing a value.
Here's a simple program modeling a bank account:

    #lang ivy1.7

    type money

    object account = {

        individual balance : money
        after init {
            balance := 0
        }

        action deposit(x:money) = {
            balance := balance + x
        }

        action withdraw(x:money) = {
            balance := balance - x
        }

        action get_balance returns(x:money) = {
            x := balance
        }
    }

    export account.deposit
    export account.withdraw
    export account.get_balance

Let's try to generate a REPL for this program:

    $ ivy_to_cpp target=repl account.ivy
    error: cannot compile "+" because type money is uninterpreted
   
IVy has a point here. We can formally verify programs that use
abstract types like `money`, but it's hard to actually execute them.
We need to make `money` an interpreted type so IVy will know how to add two 
values of this type. For example, we can use 16-bit binary numbers to
represent `money`, using this declaration:

    intrepret money -> bv[16]

Now we try compiling again:

    $ ivy_to_cpp target=repl account.ivy
    $ g++ -o account account.cpp

We can run a few transactions using the REPL:

    $ ./account
    > account.get_balance
    0
    > account.deposit(5)
    > account.get_balance
    5
    > account.withdraw(2)
    > account.get_balance
    3
    > account.withdraw(4)
    > account.get_balance
    65535
    > 

That last one is a bit surprising. Perhaps we expected the answer
`-1`, but the REPL doesn't know that we intended `balance` to
represent a 16-bit signed number, so it printed the value as
unsigned. In any event, we don't really want the account to be
overdrawn. For that matter, we don't want the balance to overflow.
Let's add a specification to `account` to prevent this:

    object spec = {
        before deposit {
            assert balance + x >= balance
        }
        before withdraw {
            assert x <= balance
        }
    }

Notice we wrote the pre-condition for `deposit` in a way that doesn't
depend type `money` having a maximum value. This way, we could also
interpet `money` with unbounded integers (that is "bignums").

Let's give it a try:

    $ ivy_to_cpp target=repl account2.ivy
    $ g++ -o account2 account2.cpp
    $ ./account2
    > account.withdraw(4)

    account2.ivy: line 29: assertion failed
    $

What happened here was that a specification was violated by the
environment (namely us). 

We've seen how to call an exported action from the REPL. What happens
if the IVy program calls an imported action? Here, we define an imported action `ask` that returns an amount, and an exported action `ask_and_check_balance` that calls `ask` to get an amount and checks whether that amount can be safely withdrawn:

    import action ask returns (x:money)

    export action ask_and_check_balance returns(ok:bool) = {
        ok := ask <= account.get_balance
    }

Here is an example run:

    > account.deposit(5)
    > ask_and_check_balance
    ask
    ? 4
    true
    > ask_and_check_balance
    ask
    ? 6
    false
    > 

When Ivy calls `ask`, the REPL prompts us for a return value with `?`.

## Running a protocol

Now let's try running the [leader election ring protocol](leader.html).

# Implementing the abstract datatypes

Recall that we used two abstract datatypes for this protocol: `node`
and `id`.  To keep things simple, we'll implement both of these types
with one-bit binary numbers. That means we'll have exactly two nodes
and two id's. Here are the implementations:

    object node_impl = {
        interpret node.t -> bv[1]

        implement node.get_next {
            y := x + 1 
       }
    }

    object id_impl = {
        interpret id.t -> bv[1]
    }

Before going on, it would be a good idea to verify that these are
correct implementations. To do this, we add two isolates:

    isolate iso_node = node with node_impl
    isolate iso_id = id with id_impl

That is, we want to verify the specification of `node` (including its
properties) with its implementation `node_impl` and similarly to
verify `id` with `id_impl`. In the case of `node`, we are verifying
not only that one-bit integers satisfy the total order axioms, but
also that adding one gives the next node in the ring (this is because
1 + 1 = 0 mod 2). Let's check:

    $ivy_check isolate=iso_node leader_election_ring_repl.ivy
    Checking isolate iso_node...
    trying ext:node.get_next...
    OK
    $ivy_check isolate=iso_id leader_election_ring_repl.ivy
    Checking isolate iso_id...
    OK

# Playing the environment

Now that we have concrete datatypes, we should be able to execute the
program. We compile the program and run the REPL like this:

    $ ivy_to_cpp target=repl leader_election_ring_repl.ivy
    $ g++ -o leader_election_ring_repl leader_election_ring_repl.cpp 
    $ ./leader_election_ring_repl
    >

Being reactive, the program is waiting for us to do something. Recall the
protocol object `app` has an action `async` that causes a node to transmit its id:

    action async(me:node.t) = {
        call trans.send(node.get_next(me),serv.pid(me))
    }

Let's call it. Since `node.t` is represented by one-bit integers, we
can choose node 0 or node 1:

    > app.async(0)
    trans.send(1,1)
    >

The response was for node 0 to call the environment to send its id 1
to node 1 (the id's were chosen arbitrary by IVy in a way that
satisfies our axioms). Now the program is waiting again for us to do
something. The network is part of the environment, and the environment
is us, so let's deliver the packet:

    > trans.recv(1,1)
    trans.send(0,1)

As a response, node 1 passed the id along to node 0. We could, for
example, deliver this message:

    > trans.recv(0,1)
    serv.elect(0)
    > 

Node 0 sees its own id and elects itself leader, as it should.

# Extracting the implementation

 What happens if we, as the network, deliver a message that hasn't
been sent yet:

    > trans.recv(0,0)
    leader_election_ring_repl.ivy: line 99: assertion failed
    $

This shows that the specification monitors in the program are
active. If an assertion fails, the program exits. This is good for
testing, but we wouldn't want the monitors to be executed in
production, since this could be a significant overhead. We can remove
the specifications from our program by declaring a special kind of
isolate called an *extract*. This is just an isolate in which nothing
is actually verified:

    extract iso_impl = app, node_impl, id_impl

In the extract, we include just the implementation objects, not the
specification objects `serv`, `node` and `id`. We can compile and run
this extract, using the command-line option `isolate=iso_impl`:

    $ ivy_to_cpp target=repl isolate=iso_impl leader_election_ring_repl.ivy
    leader_election_ring_repl.ivy: line 90: error: relevant axiom not enforced

Looks like we forgot something. Here is the line in question:

    axiom [injectivity] pid(X) = pid(Y) -> X = Y

We made an assumption about the id assignment but didn't include it in
the extract. IVy is telling us that the properties we proved might not
be true in the extract because of this. To fix this, we include `asgn` in the extract:

   extract iso_impl = app, node_impl, id_impl, asgn

Let's try again:

    $ ivy_to_cpp target=repl isolate=iso_impl leader_election_ring_repl.ivy
    $ g++ -o leader_election_ring_repl leader_election_ring_repl.cpp 
    $ ./leader_election_ring_repl
    >

So far, so good. Let's try some actions:

    > app.async(0)
    trans.send(1,1)
    > trans.recv(1,1)
    trans.send(0,1)
    > trans.recv(0,1)
    serv.elect(0)

That looks fine.

    > trans.recv(1,0)
    serv.elect(1)

Oops! We incorrectly delivered a message and it caused the service
specification to be violated. This is expected, since we removed the
specification monitors. This is the nature of assume-guarantee
reasoning: after the assumptions fail, the guarantees no longer hold.

Just as an experiment, let's try making a few more mistakes. Suppose we left
the implementation of the `node` type out of the extract:

    extract iso_impl = app, id_impl, asgn

Here's what happens:

    ivy_to_cpp target=repl isolate=iso_impl leader_election_ring_repl.ivy
    leader_election_ring_repl.ivy: error: No implementation for action node.get_next

IVy can't compile the extract because it's missing an action
implementation.  On the other hand, suppose we left the implementation
of the `id` type out of the extract:

    extract iso_impl = app, node_impl, asgn

Here's what happens:

    ivy_to_cpp target=repl isolate=iso_impl leader_election_ring_repl.ivy
    leader_election_ring_repl.ivy: line 11: error: property id.transitivity depends on abstracted object id_impl

IVy is unhappy because it can't prove that the stated properties of
`id.t` hold in the extract. This is because the proof depends on `id_impl`, which we left out.
When we generate code for an extract, IVY makes sure that that
guarantees of the extract hold, provided that the assumptions hold.

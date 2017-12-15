---
layout: page
title: Abstract Datatypes
---

A simple and effective way to reduce the complexity of reasoning about
a system is to use abstract datatypes. An abstract datatype uses a
service specification to hide the implementation of the type and
provide only properties of the type that we require. 

When programming, we often use types provided by a programming
language, such as integers or lists, without much concern for
whether we actually *require* the properties of these types for our
application. For example, we might use the integer type when all we
require is a totally ordered range of values, or a list type when all
we need is a representation of a set.

Abstract datatypes can provide just the properties we need for a given
application. For example, suppose we need a datatype to represent
clock values in a protocol. The protocol doesn't care about the
quantitative values of the clocks. It only needs to be able to compare
the values. Here is a possible specification of this type in IVy:

    #lang ivy1.7

    object clock = {
        type t
        relation (X:t < Y:t)
        
        object spec = {
            property [transitivity] X:t < Y & Y < Z -> X < Z
            property [antisymmetry] ~(X:t < Y & Y < X)
        }
    }

We begin with the interface. Our datatype `clock` provides a type
`clock.t` equipped with a binary relation `<`. The we give the
specification of this interface. The specification is a sub-object
containing two properties. The spec says that the type `clock.t`
respects the axioms of a partial order. We can rely on the declared
properties of `clock.t` in proving correctness of our protocol.

Of course, our new datatype isn't very useful, since it provides no
actual operations. Suppose, for example, that our protocol requires an
operation `incr` that can add some amount to a clock value. We don't
care how much is added, so long as the clock value increases. Let's
add this operation to the interface and specify it:

    object clock = {
        type t
        relation (X:t < Y:t)
        action incr(inp:t) returns (out:t)

        object spec = {
            property [transitivity] X:t < Y & Y < Z -> X < Z
            property [antisymmetry] ~(X:t < Y & Y < X)

            after incr {
                assert inp < out
            }
        }
    }

We've added an action `incr` that takes a clock value and returns a
clock value. In addition, we've added a monitor to object `spec`.  It
requires that the output value `y` be greater than the input value
`x`. Notice the new keyword `after`. It specifies that a given action
be inserted *after* the execution of action `incr`. We need an `after`
specification to make statements about the output values of actions.

# Using an abstract datatype

As an example of using an abstract datatype, let's make our [ping-pong
game](/examples/specification.html) a little more interesting by
attaching a clock value to the ball. Here is the new interface definition:

    object intf = {
        action ping(x:clock.t)
        action pong(x:clock.t)
    }

To the specification, we add the requirement that the ball's clock value
must always increase:

    type side_t = {left,right}

    object spec = {
        individual side : side_t
        individual time : clock.t
        after init {
            side := left;
            time = 0
        }

        before intf.ping {
            assert side = left & time < x;
            side := right;
            time := x
        }

        before intf.pong {
            assert side = right & time < x;
            side := left;
            time := x
        }
    }

Now, using our abstract datatype `clock`, we can implement the left player like this:

    object left_player = {
        individual ball : bool
        individual time : clock.t
        after init {
            ball := true;
            time := 0
        }

        action hit = {
            if ball {
                call intf.ping(clock.incr(time));
                ball := false
            }
        }

        implement intf.pong {
            ball := true;
            time := x
        }

        conjecture ball -> (spec.side = left & spec.time <= time)
    }

Notice that when we send the ball using `intf.ping`, we increment the
clock value using our `incr` operation. The right player is similar:

    object right_player = {
        individual ball : bool
        individual time : clock.t
        after init {
            ball := false
        }

        action hit = {
            if ball {
                call intf.pong(clock.incr(time));
                ball := false
            }
        }

        implement intf.ping {
            ball := true;
            time := x
        }

        conjecture ball -> (spec.side = right & spec.time <= time)
    }

As before, we export some actions to the environment, and set up our
assume-guarantee proof:

    export left_player.hit
    export right_player.hit

    isolate iso_l = left_player with spec, clock
    isolate iso_r = right_player with spec, clock

Notice that in our isolates, we use the `clock` datatype. Without the
specification of `clock`, we couldn't verify the interface
specifications in `spec`. Now let's try to use IVy to verify this program:

    $ ivy_check coverage=false pingpongclock.ivy
    ...
    OK

The command line option `coverage=false` tells IVy that we know some
assertions are not checked (that is, the ones in `clock`). What we
have proved is that the protocol only depends on the specifications we
provided for `clock`: that it is a partial order and that `incr` is
increasing.

As an experiment, see what happens when you remove the `transitivity`
property from `clock` (hint: use the command line option
`diagnose=true` to see the counterexample) . What happens when you
remove `antisymmetry`?

# Implementing an abstract datatype

To make a program we can actually run, we need to provide an
implementation of the abstract datatype `clock`. We will do this using
IVy's built-in type `int` that represents the integers. Here is
the implementation:

    object clock = {
        ...

        object impl = {
            interpret clock.t -> int

            implement incr {
                out := in + 1
            }
        }
    }

The `interpret` declaration tells IVy that the type `clock.t` should
be interpreted as the integers. This also gives an interpretation to
certain symbols in the signature of the integer theory, for example
`+`, `<`, `0` and `1`. With this interpretation, we can write an
implementation of `clock.incr` that simply adds one to its argument.

Now let's apply assume-guarantee reasoning to our abstract datatype:

    isolate iso_ci = clock

First, let's see what we're actually verifying:

    $ ivy_show isolate=iso_ci pingpongclock.ivy

    type clock.t
    type side_t = {left,right}
    relation (V0:clock.t < V1:clock.t)

    property [clock.transitivity] (X:clock.t < Y:clock.t & Y:clock.t < Z:clock.t) -> X:clock.t < Z:clock.t
    property [clock.antisymmetry] ~(X:clock.t < Y:clock.t & Y:clock.t < X:clock.t)
    interp clock.t -> int

    action ext:clock.incr(inp:clock.t) returns(out:clock.t) = {
        out := inp + 1;
        assert inp < out
    }

Notice that the `after` specification for `clock.incr` has been
inserted at the *end* of the implemention and is a *guarantee* for
object `clock`. In general, `after` specifications for actions are
guarantees for the objects that define them.

Now let's verify this isolate using IVy:

    $ ivy_check isolate=iso_ci pingpongclock.ivy

    Isolate iso_ci:

    The following properties are to be checked:
        pingpongclock.ivy: line 7: clock.transitivity ... PASS
        pingpongclock.ivy: line 8: clock.antisymmetry ... PASS

    ...

    The following program assertions are treated as guarantees:
        in action clock.incr when called from the environment:
            pingpongclock.ivy: line 14: guarantee ... PASS

    ...
    OK

IVy used the built-in theory of integer arithmetic of the Z3 theorem
prover to prove the assertion, and also to prove the two properties of
clocks.  As an experiment, try taking out the `interpret` declaration
to see what happens.

Now that we have a full implementation, we can verify
the full program:

    $ ivy_check pingpongclock.ivy
    ...
    OK
    
# Is this useful?

Specifying and verifying an abstract datatype might seem to be a lot
of work just to avoid making unnecesary assumptions about the
integers. However, it is worth observing the effect of this approach
on the proof. When verifying the protocol, IVy didn't have to make use
of the integer theory. It only used the properties that we provided.
This will be a significant advantage when doing proofs about systems
of many processes, or other systems that require quantifiers in the
proofs. When we mix quantifiers, relations and integers, the
verification problems become undecidable. This makes the theorem
prover unreliable. Abstract datatypes give us a way to segregate
theory reasoning into isolates that use do not require quantifiers, or
generally speaking fall into decidable fragments.  In this way, we
obtain more reliable performance from the prover, and also make sure
that the prover can generate correct counterexamples when we make a
mistake.


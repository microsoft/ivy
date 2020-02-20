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
the values. Here is a possible specification of this type in Ivy:

    #lang ivy1.7

    isolate clock = {
        type this
        
        specification {
            property [transitivity] X:this < Y & Y < Z -> X < Z
            property [antisymmetry] ~(X:this < Y & Y < X)
        }
    }

We begin with the interface. Our isolate `clock` provides a type
`clock` (referred to as `this` inside the isolate).  Then we give the
specification. The specification contains two properties. These proeprties say that
the type `clock`
respects the axioms of a partial order. We can rely on the declared
properties of `clock` in proving correctness of our protocol.

Of course, our new datatype isn't very useful, since it provides no
actual operations. Suppose, for example, that our protocol requires an
operation `incr` that can add some amount to a clock value. We don't
care how much is added, so long as the clock value increases. Let's
add this operation to the interface and specify it:

    isolate clock = {
        type this
        action incr(inp:this) returns (out:this)

        specification {
            property [transitivity] X:this < Y & Y < Z -> X < Z
            property [antisymmetry] ~(X:this < Y & Y < X)

            after incr {
                ensure inp < out
            }
        }
    }

We've added an action `incr` that takes a clock value and returns a
clock value. In addition, we've added a monitor to object `spec`.  It
requires that the output value `y` be greater than the input value
`x`. Notice the new keyword `after`. It specifies that the given code
be inserted *after* the execution of action `incr`. We need an `after`
specification to make statements about the output values of actions.

# Using an abstract datatype

As an example of using an abstract datatype, let's make our [ping-pong
game](/examples/specification.html) a little more interesting by
attaching a clock value to the ball. Here is the new interface specification:

    isolate intf = {

        action ping(x:clock)
        action pong(x:clock)

        specification {

            type side_t = {left,right}
            individual side : side_t
            individual time : clock

            after init {
                side := left;
                time := 0
            }

            before ping {
                require side = left & time < x;
                side := right;
                time := x
            }

            before pong {
                require side = right & time < x;
                side := left;
                time := x
            }
        }
    }


We have added a requirement that the ball's clock value must always
increase.  Now, using our abstract datatype `clock`, we can implement
the left player like this:

    isolate left_player = {

        implementation {
            individual ball : bool
            individual time : clock
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
        }

        private {
            invariant ball -> (intf.side = intf.left & intf.time <= time)
        }
    }
    with intf, clock


Notice that when we send the ball using `intf.ping`, we increment the
clock value using our `incr` operation. The right player is similar:

    isolate right_player = {

        implementation {
            individual ball : bool
            individual time : clock
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
        }

        private {
            invariant ball -> (intf.side = intf.right & intf.time <= time)
        }
    }
    with intf, clock


As before, we export some actions to the environment, and set up our
assume-guarantee proof:

    export left_player.hit
    export right_player.hit

Notice that in our isolates, we use the `clock` datatype. Without the
specification of `clock`, we couldn't verify the interface
specifications in `spec`. Now let's try to use Ivy to verify this program:

    $ ivy_check isolate=left_player pingpongclock.ivy
    ...
    OK
    $ ivy_check isolate=right_player pingpongclock.ivy
    ...
    OK

What we have proved is that the protocol only depends on the
specifications we provided for `clock`: that it is a partial order and
that `incr` is increasing.

As an experiment, see what happens when you remove the `transitivity`
property from `clock` (hint: use the command line option
`diagnose=true` to see the counterexample) . What happens when you
remove `antisymmetry`?

# Implementing an abstract datatype

To make a program we can actually run, we need to provide an
implementation of the abstract datatype `clock`. We will do this using
Ivy's built-in theory `int` that represents the integers. Here is
the implementation:

    isolate clock = {
        ...

        implementation {
            interpret clock -> int

            implement incr {
                out := inp + 1
            }
        }
    }

The `interpret` declaration tells Ivy that the type `clock` should
be interpreted as the integers. This also gives an interpretation to
certain symbols in the signature of the integer theory, for example
`+`, `<`, `0` and `1`. With this interpretation, we can write an
implementation of `clock.incr` that simply adds one to its argument.

Now let's verify this isolate using Ivy:

    $ ivy_check isolate=clock pingpongclock.ivy

    Isolate clock:

    The following properties are to be checked:
        pingpongclock.ivy: line 7: clock.transitivity ... PASS
        pingpongclock.ivy: line 8: clock.antisymmetry ... PASS

    ...

    The following program assertions are treated as guarantees:
        in action clock.incr when called from the environment:
            pingpongclock.ivy: line 14: guarantee ... PASS

    ...
    OK

Ivy used the built-in theory of integer arithmetic of the Z3 theorem
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
on the proof. When verifying the protocol, Ivy didn't have to make use
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


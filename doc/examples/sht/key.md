---
layout: page
title: Keys
---

The [abstract data type for keys](key.ivy) is quite simple:

    include order

    object key = {

        type t
        instance props : totally_ordered_with_zero(t)
        instance iter : order_iterator(this)

        object impl = {
            interpret t -> bv[16]
        }
        isolate iso = iter with impl
    }


That is, keys are totally ordered with a least element called `0`. They could
be, for example, ASCII strings ordered lexicographically, in which case
the zero element would be the empty string. Just for a test, though, we will
use 16-bit numbers. 

Keys are also equipped with an iterator type. An iterator type gives
us an `end` value that is greater than all other values. This is often
needed in loops and also gives us a way to describe a range of keys as
a semi-open interval `[l,u)` where `l` and `u` are iterator values.

For reference, here is the specification of order iterators, from the
standard library:

    module order_iterator(range) = {
        type t = struct {
            is_end : bool,
            val : range.t
        }

        instantiate totally_ordered(range.t)

        definition (X < Y) = ~is_end(X) & is_end(Y) 
                          | ~is_end(X) & ~is_end(Y) & val(X) < val(Y)

        function done(X,Y) = is_end(Y) | X < val(Y)
        function between(X,V,Y) = ~done(V,X) & done(V,Y)

        action create(x:range.t) returns (y:t)
        action end returns (y:t)

        object spec = {
            after create {
                assert ~is_end(y);
                assert val(y) = x
            }
            after end {
                assert is_end(y);
                assert val(y) = 0
            }
        }
        ...
    }

Iterators provides several useful executable predicates. There is an
order relation `<` such that `end` is greater than all values.  There
is a predicate `done(X,Y)` that tells us when value `X` is less than
iterator `Y`. Finally, there is a predicate `between(X,V,Y)` that
tells us when value `V` is in the interval `[X,Y)`. These predicates
are useful in writing invariants of loops.

Notice that iterators require that the range type be totally ordered.
We have to prove this, which is why the `key` object contains this
line:

        isolate iso = iter with impl

This says to use the interpration of type `key.t` to prove the
properties required by `key.iter`. 


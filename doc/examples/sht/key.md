---
layout: page
title: Keys
---

The abstract data type of keys is quite simple:

    include order

    object key = {

	type t
	instance props : totally_ordered_with_zero(t)
	instance iter : order_iterator(t)

	object impl = {
	    interpret t -> bv[16]
	}
    }


That is keys are totally ordered with aleast element called `0`. They could
be, for example, ASCII strings ordered lexicographically, in which case
the zero element would be the empty string. Just for a test, though, we will
use 16-bit numbers. 

Keys are also equipped with an iterator type. An iterator tpye gives
us an `end` value that is greater than all other values. This is often
needed in loops and also gives us a way to describe a range of keys as
a semi-open interval `[l,u)` where `l` and `u` are iterator values.

For reference, here is a partial specification of iterators, from the
standard library:

    module order_iterator(range) = {
	type t = struct {
	    iter_end : bool,
	    iter_val : range
	}

	function done(X,Y) = iter_end(Y) | X < iter_val(Y)

	action begin(x:range) returns (y:t)
	action end returns (y:t)
	action next(x:t) returns (y:t)
	action val(x:t) returns (y:range)

	object spec = {
	    after begin {
		iter_end(y) := false;
		iter_val(y) := x
	    }
	    after end {
		iter_end(y) := true;
		iter_val(y) := 0
	    }
	    before next {
		assert ~iter_end(x)
	    }
	    after next {
		assert X <= iter_val(x) & iter_end(y)
		       | ~(iter_val(x) < Y & Y < iter_val(y))
			 & iter_val(x) < iter_val(y) & ~iter_end(y)
	    }
	    before val {
		assert ~iter_end(x)
	    }
	    after val {
		y := iter_val(x)
	    }
	}
    }

Notice the function `done` that tells us wheter a given value has been
passed by the iterator. This is useful in expressing invariants of
loops.



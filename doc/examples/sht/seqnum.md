---
layout: page
title: Sequence Numbers
---

Our transport service needs a type of sequence numbers for packets to
provide reliable in-order delivery. In principle the [sequence number
type](seqnum.ivy) should be an unbounded sequence, since we can't put
an upper bound on the number of packets that can be sent. In practice,
though, 64-bit sequnce numbers will be more than enough for the
expected lifetime of the universe. We're going to cheat a bit here and
just *assume* that the sequence numbers don't overflow:

    include order

    module sequence_numbers = {

	type t
	action next(seq:t) returns (res:t)

	object spec = {
	    instantiate totally_ordered(t)

	    after next {
		assume exists X. seq < X;
		assert seq < res & (X < res -> X <= seq)
	    }
	}

	object impl = {
	    interpret t->bv[64]
	    implement next {
		res := seq + 1
	    }
	}

	isolate iso_props = spec,impl
    }

Notice the `assume` statement in the specification of `next`, saying
that there exists a number greater than `seq`. Really this ought to be
a pre-condition of `next`, but we will just leave it as a dangling
assumption. 
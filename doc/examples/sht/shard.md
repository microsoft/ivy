---
layout: page
title: Shards
---

A shard is a concrete representation of the values of a range of keys
in the directory. The protocol uses shards to send directory data
between servers. Shards have to be a concrete datatype because we send
them over the network.

The definition of [shards](shard.ivy) starts like this:

    include order


    module table_shard(key,data) = {

	type range
	instance props : totally_ordered_with_zero(range)
	instance iter : order_iterator(range)

	type t = struct {
	    lo : key.iter.t,
	    hi : key.iter.t,
	    first(Y:range) : key,
	    second(Y:range) : data
	}


We have a type `range` that is used to iterate over the key/value
pairs in the shard. A shard is a `struct` that contains `lo` and `hi`
iterators representing an interval over keys, and to maps `first` and
`second` over the `range` type. The `first` map contains keys while
the `second` map contains values.

We could also have used an array type to represent the data. This
would allow us to have shards of arbitarary size, although we might as
a result run into network limitations on packet size.

Shards are encoded so that if a key does not occur in `first` then
its value is implicitly the background value `0`. This means the 
interval `[lo,hi)` can be much larger than the number of keys actually
represented in the shard.

Here is the representation function for shards:

	relation at(S:t,X:key,Y:range)
	function value(S:t,X:key):data
	relation valid(S:t)

	object repr = {
	    definition at(S,X,Y) = (first(S,Y) = X & second(S,Y) ~= 0)
	    definition value(S:t,x:key) = some Y. at(S,x,Y) in second(S,Y) else 0
	    definition valid(s:t) = forall X,Y,Z. at(s,X,Y) & at(s,X,Z) -> Y = Z
	}

We start by defining an auxiliary relation `at` that says in shard
`S`, key `X` occurs at position `Y`.  The function `value` returns
some data associated with a key if the key occurs anywhere in the
shards else `0`. Notice that `value` is not fully specified in case
the key occurs at two distinct positions. However, the `valid`
predicate tells us that this cannot occur in a valid shard.

Notice also the `valid` and `value` are [macros](../values.html). In
`value`, for example, universally quantifying over `x` would result in
a quantifier alternation, defining an implicit function from `key` `x`
to `range` value `Y`. Since we already have a function `first` from
`key` to `ranges` this would create a function cycle, taking us
outside the decidable range.

In cases when we actually need the definition of `value`, we'll see
that it's sufficient to unfold it explicitly. This is typical of
representation functions.



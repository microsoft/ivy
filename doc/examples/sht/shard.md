---
layout: page
title: Shards
---

A shard is a concrete representation of the values of a range of keys
in the directory. The protocol uses shards to send directory data
between servers. Shards have to be a concrete datatype because we send
them over the network.

Here is the beginning of the definition of [shards](shard.ivy):

    include order
    include collections

    module table_shard(key,data) = {

        type pair = struct {
            p_key : key.t,
            p_value : data
        }

        instance index : unbounded_sequence

        instance arr : array(index.t,pair)

        type t = struct {
            lo : key.iter.t,
            hi : key.iter.t,
            pairs : arr.t
        }

        ...
    }

A shard is a `struct` with iterators `lo` and `hi` indicating the
interval of keys `[lo,hi)` covered by the shard, and an array
`pairs` of key/value pairs. 

Shards are encoded so that if a key does not occur in the array, then
its value is implicitly the background value `0`. This means the
interval `[lo,hi)` can be much larger than the number of keys actually
represented in the shard.

Here is the representation function for shards:

        function key_at(S,I) = p_key(arr.value(pairs(S),I))
        function value_at(S,I) = p_value(arr.value(pairs(S),I))
        function at(S,X,I) = (0 <= I & I < arr.end(pairs(S)) & key_at(S,I) = X)

        function value(S:t,x:key.t) = some Y. at(S,x,Y) in value_at(S,Y) else 0
        function valid(s:t) = forall X,Y,Z. at(s,X,Y) & at(s,X,Z) -> Y = Z

    }

We start by defining some useful auxiliary functions.  The function
`key_at(S,I)` tells us the key in position `I` of the array.
Correspondingly, `value_at` tells us the value in that position.
The predicate `at(S,X,I)` tells us if key `X` occurrs in position `I`.
It is false if `I` is not within th array bounds.

The representation function `value` returns some data associated with
a key if the key occurs anywhere in the shard, otherwise it returns
the background value `0`. This gives the key/value map associated with
the shard. Notice that `value` is not fully specified in case the key
occurs at two distinct positions with different values. However, the
`valid` predicate tells us that this cannot occur in a valid shard.

Notice also that `valid` and `value` are [macros](../values.html). In
`value`, for example, universally quantifying over `x` would result in
a quantifier alternation, defining an implicit function from key `x`
to index `Y`. Since the `pairs` already maps from indices to keys,
this would create a function cycle, taking us outside the decidable
range and causing IVy to complain.

In cases when we actually need the definition of `value`, we'll see
that it's sufficient to unfold it explicitly. This is typical of
representation functions. We usually make them macros, since their
definitions are used only in the low-level code that manipulates the
representation directly.



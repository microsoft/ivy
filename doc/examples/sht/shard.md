---
layout: page
title: Shards
---

A shard is a concrete representation of the values of a range of keys
`[lo,hi)` in the directory. The protocol uses shards to send directory
data between servers. Shards have to be a POD datatype because we send
them over the network. Shards are encoded so that if a key does not
occur in the array, then its value is implicitly the background value
`0`. This means the interval `[lo,hi)` can be much larger than the
number of keys actually represented in the shard.

We implement a shard as a struct containing the bounds `lo` and `hi`,
represented by key iterators, and an array of key/value pair that maps
each key in the range `[lo,hi)` that is present in the hash table to
its value. 

To represent the key/value array, we use the `keyvalue` module from
the standard library. The specification of `keyvalue` provides a
relation `key_at(A,I,K)` indicating that in array *A*, index *I*
contains key *K*. There is also a function `value_at(A,I)` that yields
the value at index *I*. Specifying the keys with a relation rather
than a function is very helpful in this application, because it let's
use write a property like "every key *K* with property *p* is present
in the array" without creating a function cycle. It's worth having a look
at the module `keyval` in `collections.ivy`, since it uses
a very typical approach to specifying a containter type.


Meanwhile, here is the definition of [shards](shard.ivy):

    include order
    include collections

    module table_shard(key,data) = {

        instance index : unbounded_sequence
        instance kvt : keyval(index,key.t,data)

        type t = struct {
            lo : key.iter.t,
            hi : key.iter.t,
            kv : kvt.t
        }

        relation key_at(S:t,I:index.t,X:key.t) = kv(S).key_at(I,X)
        function value_at(S:t,I:index.t) = kv(S).value_at(I)

        function value(S:t,X:key.t) = some Y. key_at(S,Y,X) in value_at(S,Y) else 0
        function valid(s:t) = forall X,Y,Z. key_at(s,Y,X) & key_at(s,Z,X) -> Y = Z

    }

For convenience, we define `key_at` and `value_at` as shorthands for
the corresponding members of `keyval`.

The representation function `value` returns some data associated with
a key if the key occurs anywhere in the shard, otherwise it returns
the background value `0`. This gives the key/value map associated with
the shard. The `some` quantifier in the definition of `value`
introduces an implicit function from keys to their positions in the
array. This is not a problem, however, since there is no function in
the interface from positions back to keys.

The `valid` predicate tells us that a given key does not accur twice
in the array. In particular, in a valid shard, the `value` function is
uniquely defined. The predicate `valid` is an object invariant that
users of `table_shard` will have to carry around.




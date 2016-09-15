---
layout: page
title: Tables
---

The [abstract data type of hash tables](table.ivy) provides the
server's internal representation of the directory. It provides the
usual `get` and `set` operations, but also actions that extract a
range of key as a shard, and incorporate a shard into the table. Here
is the interface of `hash_table`:

    include collections

    module hash_table(key,value,shard) = {

        action set(k:key.t, v:value)
        action get(k:key.t) returns (v:value)
        action extract_(lo:key.iter.t,hi:key.iter.t) returns(res:shard.t)
        action incorporate(s:shard.t)

        function hash(X:key.t) : value

        object spec = {
            init hash(X) = 0

            before set {
                hash(k) := v
            }

            after get {
                assert v = hash(k)
            }

            after extract_ {
                assert shard.lo(res) = lo;
                assert shard.hi(res) = hi;
                assert key.iter.between(lo,X,hi)-> shard.value(res,X) = hash(X)
            }

            before incorporate(s:shard.t) {
                assert shard.valid(s);
                hash(K) := shard.value(s,K) 
                           if key.iter.between(shard.lo(s),K,shard.hi(s))
                           else hash(K)
            }
        }

The interface maintains an abstract map `hash` that represents the
contents of the table. Initially, all keys map to the background value
`0`. The `set` and `get` actions have the usual semantics.  The
`extract_` action returns a shard with lower bound `lo` and upper
bound `hi`, such that keys in the interval `[lo,hi)` match the
abstract table `hash`. Notice the use of the representation function
`shard.value` and also the use of `between` to test whether a key `X`
is in the interval `[lo,hi)`. As an aside, `extract_` has an underscore
since it conflicts with an IVy keyword.

The `incorporate` action set all the keys in the interval `[lo,hi)` to
match the hard `s`. Because of the way `shard.value` is defined, this
means that keys not present in the shard's array are set to `0`.

# Implementation

The implementation of `hash_table` actually uses an ordered map rather
than a hash table. This is because we need to be able to efficiently
iterate over an interval of keys to extract a shard. Ordered maps are
provided by the `ordered_map` module in `collections`. Here is the
relevant part of the interface:

    module ordered_map(key,value) = {

        action set(nkey:key.t,v:value)
        action get(k:key.t) returns (v:value)
        action erase(lo:key.iter.t,hi:key.iter.t)
        action lub(it:key.iter.t) returns (res:key.iter.t)
        action next(it:key.iter.t) returns (res:key.iter.t)

        relation contains(K:key.t)
        relation maps(K:key.t,V:value)
        ...

The `set` and `get` actions are as usual. The `erase` action removes
an interval `[lo,hi)` of keys. The `lub` action returns an iterator to
the least `key` in the set greater than or equal to `it`, or `end` if
there is none. The `next` action is similar but returns the least key
greater than `it`. These operations are implemented in the standard library
using the `map` template in the C++ standard template library. This
makes `set`, `get`, `lub` and `next` *O*(log *n*), while erase is
*O*(*m* + log *n*), where *m* is the number of keys in the interval.

The module provides two abstract predicates, `contains` and `maps`.
The `contains` predicate indicates whether a key is in the map, while
`maps(K,V)` indicates that key `K` maps to value `V`. The `maps`
relation is injective, but not total. That is, a key maps to zero or
one values.

## Get and set

The ordered map representing the table is called `tab`. We just
call the actions of `tab` to implement `get` and `set`:

    object impl = {
        
        instance tab : ordered_map(key,value)

        implement set {
            call tab.set(k,v)
        }

        implement get {
            v := tab.get(k)
        }
        ...

## Extract

To implement `extract_`, we iterate over the interval `[lo,hi)` in the map,
recording the key/value pairs in a shard:

        implement extract_ {
            shard.pairs(res) := shard.arr.empty;
            local idx : key.iter.t, pos : shard.index.t {
                idx := tab.lub(lo);
                while idx < hi
                    invariant lo <= idx
                    invariant shard.value(res,X) = hash(X) if key.iter.between(lo,X,idx) else 0  
                    invariant shard.valid(res)
                {
                    local pair : shard.pair, k:key.t {
                        k := key.iter.val(idx);
                        shard.p_key(pair) := k;
                        shard.p_value(pair) := tab.get(k);
                        shard.pairs(res) := shard.arr.append(shard.pairs(res),pair);
                        idx := tab.next(idx)
                    }
                };                
                shard.lo(res) := lo;
                shard.hi(res) := hi
            }
        }

We start be setting the shard's array to an empty array. We set our
iterator `idx` to point to the least key (if any) greater than or
equal to `lo`. Then, while `idx` is less than `hi`, we append the
key/value pair pointed to by `idx` to the array and move `idx` to the
next `key` in the map. Finally, we set the `lo` and `hi` fields of the
shard.

The while loop is decorated with several invariants that allow IVy to
prove the post-condition of `extract_`. The first is obvious. We don't
state that `idx <= hi` since this may be false when we enter the loop
(if no keys are in the interval). Then we say that the contents of the
shard match the map up to `idx`. Finally, we need to state the
representation invariant of `shard`. That is, we need to maintain the
invariant that no key occurs twice in the shard.

## Incorporate

This operation is more or less the reverse of `extract`. We loop over
the key/value pairs in a shard, inserting them in the map. First,
though, we must erase any keys in the interval [lo,hi), since the
specification requires that keys not present in the shard be removed:

        implement incorporate(s:shard.t) {
            local lo:key.iter.t, hi:key.iter.t, pairs:shard.arr.t {
                lo := shard.lo(s);
                hi := shard.hi(s);
                pairs := shard.pairs(s);
                call tab.erase(lo,hi);
                local idx : key.iter.t, pos : shard.index.t {
                    pos := 0;
                    while pos < shard.arr.end(pairs)
                       ...
                    {
                        local pair:shard.pair {
                            pair := shard.arr.get(pairs,pos);
                            if key.iter.between(lo,shard.p_key(pair),hi) & shard.p_value(pair) ~= 0{
                                call tab.set(shard.p_key(pair),shard.p_value(pair))
                            }
                        };                        
                        pos := shard.index.next(pos)
                    }
                }
            }
        }        

Notice that in the loop, we use `between` to test whether each key is
actually in the shard's interval. As an alternative, we could have
stated in the shard representation invariant that no keys are outside
the interval.

Also notice that we left out the invariants of the loop. Here they are:

    invariant 0 <= pos & pos <= shard.arr.end(pairs)

    invariant key.iter.between(lo,X,hi) & shard.value(s,X) = 0 -> ~tab.contains(X)
    invariant key.iter.between(lo,X,hi) & Y < pos & shard.at(s,X,Y) & shard.value(s,X) ~= 0
                     -> tab.contains(X) & tab.maps(X,shard.value(s,X))
    invariant ~key.iter.between(lo,X,hi) -> spec.tab_invar(X,Y)

    invariant tab.maps(X,Y) & tab.maps(X,Z) -> Y = Z

Yikes. Let's take them in groups. The first standard: the loop index
`pos` ranges from `0` up to the end of the array. The next three state
the correct contents of the map `tab` at iteration `pos`. Basically,
for keys in the shard's interval `[lo,hi)` the map should match the
content of the shard up to position `pos`.  This is stated by the
second and third invariant. There is the subtlety that zero values are
not added to the map. The fourth invariant says that keys outside
`[lo,hi)` should match the abstract map `hash`. This is stated using
the predicate `tab_invar(X,Y)`, which states that the two maps match
for key `X` and value `Y`:

    function tab_invar(X,Y) =
      (tab.contains(X) & tab.maps(X,Y) -> hash(X) = Y)
      & (~tab.contains(X) -> hash(X) = 0)
      & (tab.contains(X) -> tab.maps(X,hash(X)))

Finally, the last invariant is just injectivity of the map. This is
really an object invariant of `tab`, but we have to state it here
since `tab` is modified by the loop. Some day, IVy will have explicit
object invariants and this won't be needed.

To prove our implementation is correct, we need one invariant conjecture:

    conjecture shard.value(S,X)=Z -> spec.tab_invar(X,Y)

This says that the concrete map `tab` matches the abstract map `hash`.
But where does the condition `shard.value(S,X)=Z` come from? This
doesn't change the meaning of the conjecture. It was just added
because to prove the conjecture we needed to unfold the definition of
the representation function `shard.value` for the key `X`. This tricks
IVy into doing that.

# Verifying the table implementation

Before using `hash_table` in our protocol, it's a good idea to try
verifying it and maybe even testing it a bit so we're fairly confident
the specification is what we want.

Here's a [simple program](table_test.ivy) to do the test:

    include shard
    include table
    include key

    type value

    instance shard : table_shard(key,value)
    instance tab : hash_table(key,value,shard)

    export tab.set
    export tab.get
    export tab.extract_
    export tab.incorporate

    isolate iso_tab = tab with shard,key
    isolate iso_key = key

    extract iso_impl = tab,shard,key

First, we need the types `key`, `shard` and `value`. We use an
uninterpreted type for `value` and our existing modules for `key` and
`shard`. We create a table object `tab` and export its actions. Then
we prove `tab` using the shard and key types. We also have to
prove `key` since it has properties to discharge.

Let's try verifiying:

    $ ivy_check table_test.ivy
    Checking isolate iso_key...
    Checking isolate iso_tab...
    trying ext:tab.extract_...
    checking consecution...
    trying ext:tab.get...
    checking consecution...
    trying ext:tab.incorporate...
    checking consecution...
    trying ext:tab.set...
    checking consecution...
    Checking isolate key.iso...
    trying ext:key.iter.end...
    checking consecution...
    Checking isolate shard.iso_index...
    trying ext:shard.index.next...
    checking consecution...
    OK

Life is good. Of course it didn't work out that way the first
time. The bugs in the implementations, specifications and invariants
have to be work our by examining counterexamples. It is a useful
exercise to try removing some invariants to see the counterexamples.
Also, try changing the conjecture to simply:

    conjecture spec.tab_invar(X,Y)

to see what happens (hint: to visualize `shard.value(S,K) = V`, you
need to project onto a shard `S`).

# Testing

Let's try running a few manual tests:


    $ make table_test
    ivy_to_cpp target=repl isolate=iso_impl table_test.ivy
    g++ -g -o table_test table_test.cpp
    $ ./table_test
    > tab.set(13,42)
    > tab.get(13)
    42
    > tab.get(14)
    0
    > tab.extract_({is_end:false,val:11},{is_end:false,val:15})
    {lo:{is_end:0,val:11},hi:{is_end:0,val:15},pairs:[{p_key:13,p_value:42}]}
    > tab.set(17,666)
    > tab.extract_({is_end:false,val:11},{is_end:false,val:19})
    {lo:{is_end:0,val:11},hi:{is_end:0,val:19},pairs:[{p_key:13,p_value:42},{p_key:17,p_value:666}]}
    > tab.extract_({is_end:false,val:11},{is_end:false,val:14})
    {lo:{is_end:0,val:11},hi:{is_end:0,val:14},pairs:[{p_key:13,p_value:42}]}
    > tab.extract_({is_end:false,val:11},{is_end:false,val:13})
    {lo:{is_end:0,val:11},hi:{is_end:0,val:13},pairs:[]}
    ...

This exercise useful before implementing on top of `hash_table`, since
we aren't sure at this point if the specification is right. 



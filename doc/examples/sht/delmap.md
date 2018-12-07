---
layout: page
title: Delegation Map
---

Our server needs to keep track of ranges of keys that are delegated to
other servers. We will call this the *delegation map*. In the
abstract, the [delegation map](delmap.ivy) is just a map from keys to
server id's. Here's its specification as an abstract datatype:

    module delegation_map(key,id) = {

        action set(lo:key.iter.t,hi:key.iter.t,dst:id)
        action get(k:key.t) returns (val:id)

        # The delegation map is a relation, since as a function it might
        # not be stratified.

        relation map(K:key.t, X:id)
        after init {
            map(K,X) := X = 0
        }

        object spec = {
            before set {
                map(K,X) := (X = dst) & key.iter.between(lo,K,hi)
                            | map(K,X) & ~key.iter.between(lo,K,hi)
            }
            after get {
                assert map(k,val)
            }
        }

        conjecture map(K,V) & map(K,W) -> V = W
        ...

The delegation map provides an action `set` that maps a range of keys
`[lo,hi)` to a given id `dst`. Notice that `lo` and `hi` are key
iterators, so `hi` can be `end`, meaning all keys from `lo` up are
mapped. The `get` action returns the destination `id` for a given 'key'.

The abstract state is a relation `map` between keys and id's. Initially,
all keys map to the default server with if `0`. By making `map` a relation
rather than a function, we avoid creating a function cycles in case the client
of the delegation map has a finction from id's to keys. 

THe specification of `set` says that all keys between `lo` and `hi`
are mapped to `dst` and all other keys keep their value. The `get`
action just returns an `id` associated to a given `key`. Of course, we
won't be able to actually prove this post-condition unless `map` is
actually total (has at least one id for each key). As it turns out,
though, we never have to explicitly state this.

Finally, `delegation_map` provides an invariant that `map` is
injective.  This is an object invariant that is implied by the spec,
but we have to provide it as a conjecture to be proved, since IVy
doesn't have object invariants yet.

# Implementation

We implement the delegation map with an `ordered_map` from keys to
id's. If `k1,k2` is a successive pair of keys in thhis map, all the
keys in the range `[k1,k2)` are delegated to the id valu8e assicated
with `k1`. This gives us an efficient way to represent a map over a
large range of keys.

Here is the implementation:

        object impl = {

            instance imap : ordered_map(key,id)

            after init {
                call imap.set(0,0)
            }

            implement set(lo:key.iter.t,hi:key.iter.t,dst:id)  {
                if lo < hi {
                    if ~key.iter.is_end(hi) {
                        local nid:id {
                            nid := imap.get(key.iter.val(imap.glb(hi)));
                            call imap.set(key.iter.val(hi),nid)
                        }
                    };
                    call imap.erase(lo,hi);
                    call imap.set(key.iter.val(lo),dst)
                }
            }

            implement get(k:key.t) returns (val:id)  {
                val := imap.get(key.iter.val(imap.glb(key.iter.create(k))))
            }
        ...
         }

The implmentation map is called `imap`.  Notice the use of `after
init` to set value of key `0` to `0`. Since `0` is the minimal key,
this means that initially all keys are delegated to the default server
`0`, as in the abstract state.

The implmenation of `get` is quite simple. We call `imap` to get the
greates lower bound (`glb`) of the requested key. This is as iterator
to the greates key in the map that is less than or equal to `k`. This
action has a precondition that there exists some key in the map less
than or equal to key. This is needed because there is no iterator
value reprenenting "before the begining". Fortunately, this
precondition is met becuase key `0` is always in the map. We return
the `id` associated the the `glb`.

The `set` action is a little more complicated. First, we have to check
that the given interval actually contains some keys (`lo < hi`). If
so, we will set the value of `lo` to point to `dst`. We must also
clear out all the keys in the range `[lo,hi)` so that the whole ranges
is covered by `lo`. In addition though, we must be careful no to disturb the 
values above `hi`. This means that if `hi` is not `end`, we have to map
`hi` to its current value, which we obtain by calling `get`. 

# Proof

To prove the the implementation of `get` satisfies its postcondition,
we need to know that if the glb if key `L` is `K`, then key `K` has
the correct value for `L` according to the abstract map. To state this invariant
directly would invold a quantifier alternation, since the definition of 
`glb` as a function would look something like this:

    definition glb(L) = some K. K <= L & contains(K) 
                                & ~exists M. K < M & M <= L & contains(M)

Fortunately, the `ordered_map` module has an alternative specification
in terms of a relation `gap` on iterators. The predicate `gap(X,Y)` is
true when there are no keys in the map in the open interval `(X,Y)`.
Both specifications are equivalent in terms of the input and output of
actions, but they are useful for different purposes.

The `gap` specification allows us to state our invariant as follows:

    conjecture imap.maps(key.iter.val(I),V) & imap.gap(I,J)
                                  & key.iter.between(I,K,J) -> map(K,V)

That is, if a key `K` lies in the gap between `I` and `J`, and `I`
maps to `V`, then in the abstract map `I` maps to `V`. We need one more 
invariant to make sure all keys are mapped:

    conjecture imap.contains(0)

Because the map always contains key `0`, all keys have a `glb`. With
these two invariants, IVy can prove that the implementation satisfies
its specification.  

## Reasoning with alternate specifications

We'll do that shortly. First, though, we should understand the limitations
of reasoning with different specifications of the same interface. Here is
how IVy defines `gap`:

    function gap(k:key.iter.t, m:key.iter.t) =
              forall L. ~(key.iter.ahead(L,k) & key.iter.done(L,m) & contains(L))

This definition gives the relation between the `contains`
specification state and the `gap` specification state. It should be
fairly easy to convince yourself that the keys in the map (*i.e.*,
`contains`) can in turn be derived from the gaps, apart from the
annoying exception of `0`. The difficulty is that the relation between
`contains` and `gaps` can only be expressed with a quantifier
alternation.

The upshot if this is that, as long we we write our invariant *only*
using the `gaps` specification or *only* using the `contains`
specification, IVy can decide reliably whether our invariant is
inductive. If we try mixing the two, we might get a counterexample in
which `gaps` and `contains` are inconsistent. There is a small proviso
to this, however: we can always write `contains(0)` since this is
independent of `gaps`.

Using alternate specifications can be a very useful tactic for keeping
the proof of invariants within a decidable fragment. It is sometimes a
bit tricky to come up with an alternate encoding that on the one hand
can be specified in the logic and on the other hand is useful for
writing invariants. Some examples are provided in the standard
libarary, however, that are generically useful.

## Checking the proof

Let's test the `delegation_map` module by instantiating it:

    #lang ivy1.6

    include key
    include delmap

    type id

    instance dmap : delegation_map(key,id)

    export dmap.set
    export dmap.get

    object impl = {
        interpret id -> bv[1]
    }

    isolate iso_dmap = dmap with key
    extract iso_impl = dmap, key, impl

We need our `key` module. In addition, we need a type of process id's. 

    $ ivy_check diagnose=true delmap_test.ivy 
    Checking isolate iso_dmap...
    trying ext:dmap.get...
    checking consecution...
    trying ext:dmap.set...
    checking consecution...
    Checking isolate key.iso...
    trying ext:key.iter.create...
    checking consecution...
    trying ext:key.iter.end...
    checking consecution...
    OK

As an excersize, you might try changin or removing some lines in the
implementation to see what breaks, or try compiling this module to a
REPL and running it.






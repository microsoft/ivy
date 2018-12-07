---
layout: page
title: Concrete data
---

Abstract dataypes allow us to hide the representation of data behind
interfaces. To pass information across interfaces, however, we still
need a sufficiently rich class of concrete datatypes whose
representation is not hidden. This is particularly relevant when
communicating across a network. In this case, we can't efficiently
pass a reference to an abstract object -- we have to represent the
contents of the object in a concrete way.

To facilitate exchange of data across interfaces, Ivy provides a set of
standard concrete datatypes. 

# Structs

A `struct` is an aggregate of named components. Structs are declared like this:

    type point = struct {
        x : coord,
        y : coord
    }

This defines a type `point` whose elements are structures consisting
of members `x` and `y` of type `coord`. Two *destructor* functions `x`
and `y` are defined that respectively extract the *x* and *y*
coordinates of the point. Thus, if `p` is a point, then `x(p)` is the
*x* coordinate of `p` and `y(p)` is the *y* coordinate.

The members of a structure can be assigned. For example, to assign `0` to
the *x* coordinate of point `p`, we would write:

    x(p) := 0

This mutates not the destructor function `x`, which is immutable, but
rather the value of `p`. The value of `y(p)` remains unchanged by this
assignment.

Members of a struct can also be functions and relations. For example:

    type point = struct {
        coords(X:dimension) : nat
    }

Our points now have one coordinate value for each dimension defined by
some arbitrary type `dimension`. Suppose we declare:

    type dimension = {x,y,z}

We could then refer to the `x` coordinate of a point `p` as
`coord(p,x)`, and we could assign `0` to it like this:

    coord(p,x) := 0

This would be written in many programming languages as something like
`p.coord[x] = 0`. The type `dimension` need not be an enumerated type,
however. It could be an uninterpreted type, or an interpreted type
(for example, an integer type) or even another structure type.

Structs can also contain structs. For example:

    type line = {
        begin : point,
        end : point
    }

To set the *x* coordinate of the begin point of a line `l`, we could write:

    coord(begin(l),x) := 0

This mutates `l` and not the immutable destructor functions `coord`
and `begin`.

# Arrays

An array type represents a map from an interval `[0,end)` of some type
(the index type) to some other type (that value type). Usually the
index type is interpreted as `int`.

Here is an example of a simple program that tabulates the function
`f(X) = X * X` from `0` to `max-1`:

    #lang ivy1.7

    include collections

    type t

    instance arr : array(t,t)

    action tabulate(max : t) returns (res:arr.t) {
        local i:index {
            i := 0;
            res := arr.create(max,0);
            while i < max {
                res := arr.set(res,i,i*i);
                i := i + 1
            }
        }
    }

The `array` module provides an action `create` that returns an array
mapping values in the range `[0,end)` to some given value (in the
example, `0`). The `set` action takes a array, an index and a
value. It sets the value of the array at the given index to the value
and returns the resulting array. Keep in mind, because of IVy's
call-by-value convention, an action can't have a side effect on its
input parameters. The `set` action returns a *copy* of its input
array with one value changed.

This program seems inefficient, since it copies the array each time it
modifies one element. In fact it isn't. The compiler recognizes that
the array can be modified "in place". Lets run this program to see
what we get.  First, we have to give a concrete interpretation for
type `t` and define an extract:

    interpret t -> int
    export tabulate
    extract iso_impl = tabulate, arr

Compile and run:

    $ make array1
    ivy_to_cpp target=repl isolate=iso_impl array1.ivy
    g++ -g -o array1 array1.cpp
    $ ./array1
    > tabulate(4)
    [0,1,4,9]

Here is a part of the interface definition for array types, from the
`collections` module in the standard library:

    module array(domain,range) = {

        type t

        action create(s:domain,y:range) returns (a:t)
        action set(a:t,x:domain,y:range) returns (a:t)
        action get(a:t,x:domain) returns (y:range) 
        action size(a:t) returns (s:domain)
        action resize(a:t,s:domain,v:range) returns (a:t)

        function end(A:t) : domain
        function value(A:t,X:domain) : range

        object spec = {
            before create {
                assert 0 <= s
            }
            after create {
                assert end(a) = s & value(a,X) = y
            }
            before set {
                assert 0 <= x & x < end(a)
            }                        
            after set {
                assert value(a,X) = y if X = x else value(old a,X)
            }
            before get {
                assert 0 <= x & x < end(a)
            }
            after get {
                assert value(a,x) = y
            }
            after size {
                assert s = end(a)
            }
            after resize {
                assert end(a) = s;
                assert 0 <= X & X < end(old a) -> value(a,X) = value(old a,X);
                assert end(old a) <= X & X < s -> value(a,X) = v
            }
            ...
        }
        ...
    }

In addition to `create` and `set`, array types provide an action `get`
to get the value at a given index, `size` to get the `end` index, and `resize`
to change the end index. The `resize` action takes an addition parameter
that gives the value of the new elements in case the size is increased.

Notice that in the `set` method, both the input and the output
parameter are called `a`. This indicates to the compiler that we
intend to modify the array `a` in place if possible. When writing the
`after` specification for `set`, we need a way to refer to the input
value of `a`. For this, we use `old a`. We can refer to the original
value of any component that is mutated by an action using `old`. You
can also see the use of `old` in the specification of `resize`. The
expression `old x` always referes to the value of symbol `x` at the
time the action was called.

In the next section, we'll see a more interesting application of
arrays.


# Representation functions

Often, we use concrete dataypes as representations of abstract values.
This gives us an efficient way of passing these values across
interfaces.

As an example, consider using an array as a representation of a
set. Here is the start of a module that accomplishes that:

    #lang ivy1.7
    module set(elem) = {

        type this
        alias t = this

        relation contains(X:t,Y:elem)
        action emptyset returns(s:t)
        action add(s:t,e:elem) returns (s:t)
        ...    

Notice something new here: `type this`.  This declares a type with the
same name as the object we are declaring (which won't be known until
we instantiate this module). For convenience, we create an alias `t`
for this type. This interface of our abstact set type contains a
relation and two actions.

The relation `contains` acts as a *representation function*.  This
tells us what abstract set a given value of type `set` represents.
The representation function allows us write specifications using the
abstract value that is represented. This means we can can pass around
values of type `set` as if they were actually abstract sets instead of
arrays.

Now let's specify the semantics of our two set operations in terms of
the `contains` relation.

    module set(elem) = {
        ...

        object spec = {
            after emptyset {
                assert ~contains(s,X)
            }
            after add {
                assert contains(s,X) <-> (contains(old s,X) | X = e)
            }
        }

The action `emptyset` returns a representation of the empty set, while
`add` returns set `s` with element `e` added. Notice that the set
parameter of `add` is both input and output. This indiciates to the
compiler that we wish to avoid copying if possible. In most cases,
this will allowed the compiled code of `add` to modify the set in
place.

Let's have a hack at implementing these operations. The implementation
usually provides a concrete data representation, a definition for each
function or relation in the interface, and code for each
action. Typically it instantiates some modules to provide the concrete
representation. Here's one way we could implement `set`:

    include collections
    include order

    module set(index,elem) = {
        ...

        instance index : unbounded_sequence
        instance arr : array(index.t,elem)
        destructor repr(X:t) : arr
        
        definition contains(X:t,y:elem) = exists Z. 0 <= Z & Z < repr(X).end & repr(X).value(Z) = y
        
	implement emptyset {
	    repr(s) := arr.create(0,0)
	}
	
	implement add {
	    if ~contains(s,e) {
                repr(s) := arr.resize(repr(s),index.next(arr.end(repr(s))),e)
	    }
        }

    isolate iso = this
    }

This implementation uses an unbounded array as a representation.
The concrete type is usually provide by giving the abstract type a
*private destructor*, in this case the function `repr` from type `t` to
the array type. Giving the destructor in this way is equivalent to
writing:

    type t = struct {
        repr : arr
    }

except the that field `repr`, being a component of the implementation,
is not visible to users of `set` (it's similar to a private member in
C++). We use the function `repr` to access the internal representation
of a set.

Next, we give the definition of `contains` in terms of `repr`. This
definition is also private. We say that `contains(x,y)` is `true`
if a given `elem` *y* can be found somewhere in the array representing
set `x`. 

The implementation of `emptyset` returns an empty array. To add an
element to a set, we test whether the element is already present.  If
not, we resize the array to make it one value larger, where the added
value is `e`, the new element.

Finally, we create an isolate containing our object so it will be
verified separately.

Notice that in the implementation of `add`, we evaluate the predicate
`contains`.  IVy recognizes that `contains` is executable because the
quantifier in the definition of `contains` is bounded. This means it
can compile the quantifier into a loop from `0` to `arr.end(X)`. If
you try to compile an unbounded quantifier into executable code, IVy
will complain.

Also notice that instead of `arr.end(s) + 1`, we wrote
`index.next(arr.end(s))`.  That is, we are treating `index` as an
abstract datatype, assuming only that it provides an order `<` and an
action `next`. From a software engineering point of view, this is
probably useless abstraction. However, from a verification point of
view, it is useful -- it allows us to verify `set` without using the
theory or arithmetic.

The implementation is moderately efficient. That is, if the caller
of `add` writes:

   s := set.add(s,e)

the compiler will recognize that the array `s` can be modified in
place. On the other hand, evaluating `contains` will still be linear
time in the array size, since it loops over the array. This approach
is only practical for small sets.

To try out our sets, we instantiate a set type:

    type elem
    instance s : set(elem)

We export our two actions:

    export s.emptyset
    export s.add

Then we verify:

    $ivy_check arrayset.ivy
    ivy_check arrayset.ivy 
    Checking isolate s.impl.index.iso...
    trying ext:s.impl.index.next...
    checking consecution...
    Checking isolate s.iso...
    trying ext:s.add...
    checking consecution...
    trying ext:s.emptyset...
    checking consecution...
    OK

Notice that even though the object `index` was instantiated from the
standard library, IVy still verified it. Generally speaking, even
trusted modules have properties that need to be verified when
instantiated in a particular environment.

# Representation invariants

Now let's try adding an action to our `set` module that removes an element:

     module set(index,elem) = {
         ...
         action remove(s:t,e:elem) returns (s:t)

         object spec = {
             ...
             after remove {
                 assert contains(s,X) <-> (contains(old s,X) & X ~= e);
             }
        }

        object impl = {
            ...
            implement remove {
                if some (i:index.t) 0 <= i & i < repr(s).end & repr(s).value(i) = e {
                    var last := repr(s).end.prev;
                    repr(s) := repr(s).set(i,repr(s).get(last));
                    repr(s) := repr(s).resize(last,0)
                }
            }
        }
    }

This implementation of `remove` scans the array for some index `i` whose value is `e`.
If such an `i` exists, the value `e` is removed by replacing it with the last value
in the array and then resizing the array to make it one element smaller. 

Unfortunately, this implementation doesn't work: if the input array
contains two copies of the element `e`, one copy will remain. One
solution to this problem is to use a *representation invariant*. This
is a predicate a predicate that must be true of a value for it to be a
valid representation. The representation invariant is assumed to be
true of input values and must hold of output values.

In the case of our sets, the representation invariant is that no value
occurs twice in the array. It is part of the interface, and like `contains`, its definition
is private:

        relation valid(X:t)


We have to specify our interface to make the appropriate assumptions and guarantees:

    object spec = {
        after emptyset {
            assert ~contains(s,X)
        }
        before add {
            assert valid(s)
        }
        after add {
            assert contains(s,X) <-> (contains(old s,X) | X = e);
            assert valid(s)
        }
        before remove {
            assert valid(s)
        }
        after remove {
            assert contains(s,X) <-> (contains(old s,X) & X ~= e);
            assert valid(s)
        }
    }

We give the definition of `valid` in the implementation:

    object impl = {
        ...
        definition valid(X:t) =
            forall Y,Z. (0 <= Y & Y < repr(X).end & 0 <= Z & Z < repr(X).end
                          & repr(X).value(Y) = repr(X).value(Z) -> Y = Z)
    }

Now we can verify that our implementation of `remove` works (try
verifying [arrayset2.ivy](arrayset2.ivy)). There is a disadvantage to
this approach, however. Users of our `set` module now have to keep
track of the invariant that set values are valid. This could lead to many
"boilerplate" invariant conjectures. One day, IVy will solve this problem
using predicate subtypes. 

# Array and loops

For now, it might be best to just implement `remove` in a way that doesn't
rely on a representation invariant. We can do this using a `while` loop.
Here is the implementation we have in mind:

    action remove(s:t,e:elem) returns (res:t)

    object impl = {
        ...

        implement remove {
            local i:index.t, end:index.t {
                i := 0;
                res := emptyset;
                end := arr.end(s);
                while i < end
                {
                    local f:elem {
                        f := arr.get(s,i);
                        if  f ~= e {
                            res := add(res,f)
                        }
                    };
                    i := index.next(i)
                }
            }
        }
    }

That is, we scan the input array `s`. When we encounter a value not
equal to the output set `res`. This is easy enough to write, but Ivy
can't prove it correct because of the loop. We're going to need an
inductive invariant.

Before diving in to the proof, let's consider the general schema of
inductive proofs of loops. We think of the loop as computing an
approximation to a desired function that approaches the correct result
with each iteration. We'll call this function `step(i)`, where `i` is
the loop index. Suppose we want our loop to compute the "or" of the
bits in an array `a`, that is:

     function or = exists X. 0 <= X & X < arr.end(a) & arr.value(a,X)

 Then our step function would be:

     function step(i) = exists X. 0 <= X & X < i & arr.value(a,X)

That is, our approximation is the "or" of all the bits up to (but not
including) the index `i`.

Now we need to give an *inductive* characterization of `step`. That
is, we need to know how to compute the value of `step` at the next
iteration. It looks like this:

    property 0 <= I & index.succ(I,J) -> step(J) = (step(I) | arr.value(a,I))

That is, to compute approximation for the successor of index `I`, we
"or" `step(I)` with the bit in the array at index `I`. Ivy can prove
this property from the definition of `step`. It just unfolds the definition
of `step` for `I` and `J` and uses its EPR decision procedure.
Notice we use the successor relation `succ` provided by the index type
to represent the fact that `J` is next after `I`. This is because we
can't call the action `next` in a property of function definition.

Now we need to know that when we get to the and of the array, we have
the desired result. Here is how we write this condition:

    property I = arr.end(a) -> step(I) = or
        
Again, Ivy can easily prove this from the definitions of `step` and
`or`. If you squint at these two properties a bit, you'll see that
they are very close to a logic program for computing `or` (in fact,
we could easily recast them in the form of [Horn
clauses](https://en.wikipedia.org/wiki/Horn_clause)). A logic
programming system could execute them directly to compute our result.
We have have in mind, however, to do the computation using a loop:

    i := 0;
    res := false;
    while i < arr.end(a)
        invariant 0 <= i & i <= arr.end(a)
        invariant res = step(i)
    {
        res := res | arr.value(a,i);
        i := index.next(i)
    } 
    assert res = or


Notice the two invariants decorating the loop. IVy can prove that that
they are inductive and that the assertion is true. This can be done
using only our two properties, without reference to the actual
definition definition of `step`. This is the general approach for
writing a loop in IVy: first characterize the loop inductively, then
write the loop with two invariants as above.

Now let's get back to the `remove` method. We start with the step
function:

    function remove_step (s:t,e:elem,i:index.t,y:elem)
            = (exists Z. 0 <= Z & Z < i & arr.value(s,Z) = y) & y ~= e

This is an approximation of the representation function
`contains`. Here, `s` is the input set, `e` is the element to remove,
`i` is the loop index and `y` is an element to test for
membership. The function yields true if `y` is not the removed element
`e` and if it occurs before index `i` in the input set. In other
words, this function gives us the output set accumulated up to index
`i`.

Now we need an inductive charaterization. Basically, we add an element
of the array to the output set if it is not the removed element:

    property I >= 0 & index.succ(I,J) ->
        (remove_step(X,E,J,Y) <-> (remove_step(X,E,I,Y) | arr.value(X,I) = Y & Y ~= E))

The exit condition tells us when we have completed the computation:

    property I = arr.end(X) ->
        (remove_step(X,E,I,Y) <-> (contains(X,Y) & Y~=E))

That is, when we reach the end of the array, we have accumulated all
the elements of the input set except `e`.

Now here's the `remove` action, decorated with invariants:

    implement remove {
        local i:index.t, end:index.t {
            i := 0;
            res := arr.create(0,0);
            end := arr.end(s);
            while i < end
                invariant 0 <= i & i <= end
                invariant contains(res,Y) = remove_step(s,e,i,Y)
            {
                local f:elem {
                    f := arr.get(s,i);
                    if  f ~= e {
                        res := add(res,f)
                    }
                };
                i := index.next(i)
            }
        }
    }

Notice that the invariant is universally quantified on `Y`, the test
element. The invariant says that our loop computes exactly what our
inductive characterization computes. Ivy can easily verify that [this
version](arrayset3.ivy) of `remove` satisfies its specification.

Of course, this might seem like a lot of work for around ten lines of
code. This style of proof has a big advantage, though, from the point
of view of automating the proof. That is, the places in the Horn
clauses where definitions need to be unfolded are clear. We don't need
fragile quantifier instantiation heuristics to make the proof go
through.

In general, though, it's best to avoid this kind of painstaking
construction of loops by using higher-level operations on containers.



















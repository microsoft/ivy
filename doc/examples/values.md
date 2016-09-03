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

An array types represents a map from an interval `[0,end)` of some
type domain type to some range type. Usually the domain type is
interpreted as `int`.

Here is an example of a simple program that tabulates the function
`f(X) = X * X` from `0` to `max-1`:

    #lang ivy1.6

    include collections

    type t

    instance arr : array(t,t)

    action tabulate(max : t) returns (res:arr) {
        local i:index {
	    i := 0;
	    res := arr.create(max,0);
	    while i < max {
	        res := arr.set(res,i,i*i);
	    }
        }
    }

The `array` module provides an action `create` that produces an array
mapping values in the range `[0,end)` to some given value. The `set`
action takes a array, an index and a value. It sets the value of the
array at the given index to the value and returns the resulting array.

This program seems inefficient, since it copies the array each time
it modifies one element. In fact it isn't, since the compiler recognizes that
the array can be modified "in place". Lets run this program to see what we get.
First, we have to give a concrete interpretation for type `t` and define an extract:

    interpret t -> int
    export tabulate
    extract iso_impl = tabulate, arr

Compile and run:

    $ ivy_to_cpp target=repl isolate=iso_impl tabulate.ivy
    $ g++ -o tabulate tabulate.cpp
    $ ./tabulate
    > tabulate(4)
    [0,1,4,9]

Here is the interface definition for array types,
from the `collections` module in the standard library:

module array(domain,range) = {

    type t

    action create(s:domain,y:range) returns (a:t)
    action set(a:t,x:domain,y:range) returns (a:t)
    action get(a:t,x:domain) returns (y:range) 
    action size(a:t) returns (s:domain)
    action resize(a:t,s:domain) returns (a:t)
    
    function end(A:t) : domain
    function value(A:t,X:domain) : range

    object spec = {
	before create {
	    assert 0 <= s
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
	    assert 0 <= X & X < end(old a) -> value(a,X) = value(old a,X)
	}
    }

In addition to `create` and `set`, array types provide an action `get`
to get the value at a given index, `size` to get the `end` index, and `resize`
to change the end index. The `resize` action takes an addition parameter
that gives the value of the new elements in case the size is increased.

In the specification we can see the use of the `old` keyword.  Notice
that in the `set` method, both the input and the output parameter are
called `a`. This indicates to the compiler that we intend to modify
the array `a` in place. When writing the `after` specification for
`set`, we need a way to refer to the input value of `a`. For this, we
use `old a`. In fact, we can refer to the original value of any
component that's mutated by an action using `old`. YOu can also see
the use of `old` in the specification of `resize`.

In the next section, we'll see a more interesting application of
arrays.


# Representation functions

Often, we use concrete dataypes as representations of abstract objects.
This gives us an efficient way of passing these objects across interfaces.

As an example, consider using an array as a representation of a
set. Here is a module that accomplishes that:

     module set(index,elem) = {
    
        instantiate array(index.t,elem)

	function value(X:t,Y:elem) = exists Z. 0 <= Z & Z < end(X) & value(X,Z) = Y
    }

Our set representation comes with a type `t` representing a set of
values of type `elem`.  The type `t` is created by instantiating
`array`.  This also gives us some actions for manipulating the
representation.

Our set type also comes equipped with a *representation
function*.  This tells us what abstract set a given value of type
`set.t` represents. In particular, it returns true if a given `elem`
*Y* can be found somewhere in the array. The representation function allows us
write specifications using the abstract value that is
represented. This means we can can pass around values of type `set.t`
as if they were actually abstract sets instead of concrete structures.

Let's start to build some operations on concrete sets:

    object set = {

      ...

	 action emptyset returns(s:t)
	 action add(s:t,e:elem) returns (s:t)

	 object spec = {
	     after emptyset {
		 assert ~value(s,X)
	     }
	     after add {
		 assert value(s2,X) <-> (value(s1,X) | X = e)
	     }
	 }
    }

Here we've specified two operations on sets, using the representation
funciton. The action `emptyset` returns a representation of the empty
set, while `add` returns set `s1` with element `e` added. Notice that
the set parameter of `add` is both input and output. This indiciates
to the compiler that we wish to avoid copying if possible.

Let's have a hack at implementing these operations:

    object set = {

      ...


	object impl = {

	    implement emptyset {
		s := create(0,0)
	    }

	    implement add {
	        if ~value(s,e) {
		    resize(s,index.next(s),e)
		}
            }
	}
    }

The implementation of `emptyset` returns an empty array. To add an
element to a set, we test whether the element is already present. To
do this, notice that we can use the representation function `value`.
If the not, we resize the array, adding one element equal to `e`.

This implementation is moderately efficient. That is, if the caller
of `add` writes:

   s := set.add(s,e)

the compiler will recognize that the array `s` can be modified in
place. On the other hand, evaluating `value(s,e)` will still be linear
time in the array size because of the existential quantifier in the
definition of `value`.


Of course, we'll need an actual range type to index our array.  For
now, let's grab a specification of a suitable abstract type from the
standard library:

    include order
    
    instance range : unbounded_sequence

This gives us a discrete totally ordered set with a least element `0` and
actions `prev` and `next`. 

Let's try to verify what we have so far. We export our two actions:

    export set.emptyset
    export set.add

Then we verify:

    $ivy_check concrete_set.ivy





















---
layout: page
title: "Deduction example: array reversal"
---

This is an example of using tactics in Ivy to keep verification conditions
decidable.

We will define relationally what it means for one array to be the
reverse of another, then prove that reversing an array twice gives
the original array. Then we will give some executable
implementations of array reversal, prove their correctness, and show
that computing the reversal twice gives the same array back.

This can be contrasted to a more traditional approach of defining
list reversal as a recursive functionally, proving its properties
and then directly computing the functional definition. Using arrays
is more efficient, since it can be done in place with no memory
allocation and good cache behavior, while the recursive list version
requires *O*(*n*) allocations and random memory accesses. The list
version has the advantage that a step is saved in the proof, since
the recursive function definition of reversal can be directly
executed, while the relational one cannot. Still, there is only one
use of induction in either approach, since the needed properties of
the relational definition can be proved with just linear arithmetic.

References
----------

We will need the `order` and `collections` libraries for arrays, and
the `deduction` library for deduction rules of first-order logic.

```
include order
include collections
include deduction

```

Reversal permutations
---------------------

An array `A` is the reverse of array `B` if they have the same length,
and if the value of array `A` at every index `I` is equal to the value of
array `B` at index `N - 1 - I` where `N` is the length of the arrays.

This definition problematic, however, because it uses quantified
arithmetic.  That is, we have a universal quantifier over the index
`I` and we also perform arithmetic on `I`. To avoid this, we will
define reversal abstractly in a way that hides the arithmetic and
still allows us to infer that traversing the reversed array yields
the same sequence of values as traversing the original array
backward.

To express such a definition, we start with the more primitive
notion of reversing a range of numbers, which we will then lift to
reversal of arrays. We construct an unbounded sequence `idx` and a
relation `rev` describing a permutation on the range `[0,U)`. That
is, `rev(U,X,Y)` holds when `X + Y + 1 = U `.


```
instance idx : unbounded_sequence
relation rev(U : idx, X : idx, Y : idx)

```
The definitoin of `rev` and its associated properties are given the
following isolate. This isolate hides the definition of `rev` but
gives us some useful properties that will allow us to reason about
array reversal.

```
isolate rev_theory = {

    specification {

```
The specification gives us the following properties of `rev`.

- The first and last numbers in the range are related [1].
- If `X` and `Y` are related, then `X+1` and `Y-1` are related [2].
- The relation is symmetric [3].

These properties are expressed using the successor relation of the
sequence in order to hide the underlying arithmetic.

```
        property idx.succ(Y,U) <-> rev(U,0,Y)  # [1]
        property rev(U,X,Y) & idx.succ(X,X1) & idx.succ(Y1,Y) -> rev(U,X1,Y1)  # [2]
        property rev(U,X,Y) -> rev(U,Y,X)  # [3]

```
In addition, we need to specify that `rev` is a permutation over `[0,U)`.
First, we specify that it is a function from `[0,U)` to `[0,U)`, that is, 
its domain and range are `[0,U)` and it is functional.

```
        property rev(U,X,Y) & rev(U,X,Z) -> Y = Z  
        property rev(U,X,Y) -> X < U & Y < U

```
We need one further property, however, to guarantee the
relation is a permutation. We need to know that every number
in the range `[0,U)` is related to *some* number in that
range (in other words, reversal is a bijection). We don't
want to state this as a property, however, since it contains
an unstratified quantifier alternation (in effect, a
function from `idx` to `idx`). Instead, we state the
property as a theorem. The difference is that this property
will not be used by default. Rather, we will use it
explicitly and specialize it to particular values of `X`, so
that the unstratified quantifier alternation is eliminated.

```
        theorem [into] {
            property 0 <= X & X < U -> exists Y. rev(U,X,Y)
        }

```
The proof of this theorem requires the definition of `rev`
given below. If we try to prove it directly with Z3, however, we
get following error message:

    # error: The verification condition is not in logic epr.
    #
    # Note: the following interpreted functions occur over variables:
    #   relation <=(V0:idx,V1:idx)
    #   function +(V0:idx,V1:idx) : idx
    #   function -(V0:idx,V1:idx) : idx
    #   relation <(V0:idx,V1:idx)
    #   relation =(V0:idx,V1:idx)

The problem here is that, after expanding the definition of `rev`,
we have arithmetic applied to universally quantified variables,
which puts us outside the decidable fragment. To avoid, this, we
will apply some tactics.

```
        proof
            apply introImp;
            apply introE with witness = U - X - 1

```
The first step is to apply the "implication introduction" rule,
which is defined in the deduction library. This is a standard rule
of the natural deduction system which says, to prove `p -> q`,
you need to prove `q` from the assumtion of `p`. This converts
the proof goal `0 <= X & X < U -> exists Y. rev(U,X,Y)` to:

    # {
    #     property 0 <= X & X < U
    #     #----------------------
    #     exists Y. rev(U,X,Y)
    # }

To prove the existentially quantified goal, we apply the "existential
introduction" rule, giving a witness for `Y`. In this case, the `Y`
that corresponds to `X` under reversal is `U - X -1` (we can get this
by solving for `Y` in the definition of `rev` below. This gives us the
following goal:

    {
        property 0 <= X & X < U
        #-----------------------
        property rev(U,X,U - X - 1)
    }

With the quantifier removed, expanding the definition of
`rev` no longer gives us arithmetic over quantified
variables. This means we can leave the rest of the proof to
the default tactic using Z3.  The general approach is to do
just enough tactical reasoning to eliminate the offending
quantifiers or unstratified functions and then let Z3 do the
rest of the work.

Finally, here is one more property of reversal permutations
that might be useful (though we won't use it here). This says
that reversals indeed go backward. It's provable from the
above properties by induction, but we can get it here for free
using the integer theory.

```
        property X < Y & rev(U,X,X1) & rev(U,Y,X1) -> Y1 < X1


    } # end specification section

```
The definition of `rev` is given in the implementation section so that
the arithmetic will be hidden from users of this isolate.

```
    implementation {
        definition rev(U,X,Y) = (X + Y + 1 = U)
    }

```
We say `with idx.impl` to expose the definition of `idx.succ`, which is needed to
prove the above properties.

```
} with idx.impl

```

Array reversal
--------------

Now that we have proved some properties of reversal permutations we
will use this notion to define reversal of an array. First, we
create a type `t` for the elements of the array, and create an array
type indexed by type `idx`.

```
type t
instance arr : array(idx,t)

```
The relation `arr_rev` is true of a pair of arrays when one is the
revere of the other.  This means that the have the same length and
elements that correspond according to `rev` have equal
values. Notice that there is a  quantifier alternation here, but it
is benign, since it is from `arr` and `idx` to `t`.

```
relation arr_rev(A1:arr,A2:arr)

definition [def_arr_rev] 
    arr_rev(A1:arr,A2:arr) =
        arr.end(A1) = arr.end(A2) & forall X,Y. rev(arr.end(A1),X,Y) -> arr.value(A1,X) = arr.value(A2,Y)

```
From the symmetry of `rev`, Z3 can prove that `arr_rev` is also symmetric:

```
property [arr_rev_symm] arr_rev(A1,A2) -> arr_rev(A2,A1)

```
Now we would like to show that reversing an array twice gives the
original array. By symmetry, this is the same as saying the two
arrays `B` and `C` that are reversals of the same array `A` are
equal. We will prove this in two different ways.

The first way is to start with a lemma. We'll do this in an isolate
so we won't give unwanted help to the second proof below.

```
isolate double_reverse1 = {

```
Our lemma says that corresponding elements of `A` and `B` are equal.

```
    property arr_rev(A,B) & arr_rev(A,C) & 0 <= X & X < arr.end(B) -> arr.value(B,X) = arr.value(C,X)

```
To show this, we need theorem `into`, which tells us that every
index in `B` and `C` corresponds to *some* index in `A`. Since
the elements of `B` and `C` are both equal by definition to this
element of `A`, so by transitivity they are equal to each
other. We use the `assume` tactic to bring in theorem `into` as
an assumption in our proof goal, plugging in the specific value
of `U` that we need.

```
    proof
        assume rev_theory.into with U = arr.end(B)

```
Here is the resulting proof goal:

    #     {
    #        property 0 <= X & X < arr.end(B) -> exists Y. rev(arr.end(B),X,Y)
    #        property (arr_rev(A,B) & arr_rev(A,C) & 0:idx <= X & X < arr.end(B)) 
    #                     -> arr.value(B,X) = arr.value(C,X)
    #     }

We can allow the default tactic to prove this. In this proof,
`X` is a constant, so there is no unstratified quantifier
alternation.  Notice that we cleverly stated our lemma using the
same free variable `X` that was used in the statement of theorem
`into`. If we had used, say, `Z` instead, we would have had to
say `with X = Z` to get the needed instance of `into`.

Now with our lemma, we can prove that `B` and `C` are equal:

```
    property arr_rev(A,B) & arr_rev(A,C) -> B = C

```
To prove this, we need the "extensionality" property of
arrays. That is, we need to know that two arrays with equal
elements are equal. This property isn't exposed by default
because it has a quantifier alternation.  We bring it in
explicitly with the `assume` tactic. Since the statement of this
property uses array variables `X` and `Y` (see collections.ivy)
we need to do some substitution.

```
    proof
        assume arr.spec.extensionality with X = B, Y = C

```
Here is the proof goal we get:

   {
       {
           property arr.end(B) = arr.end(C)
                    & forall I. (0:idx <= I & I < arr.end(B)) -> arr.value(B,I) = arr.value(C,I))
           property B:arr = C
       }
       property (arr_rev(A,B) & arr_rev(A,C)) -> B = C
   }

Our lemma says the corresponding elments of `B` and `C` are
equal, so by extensionality, `B` and `C` are equal. Theres a
quantifier alternation from `arr` to `idx` in the extensionality
property, but it doesn't break stratification, so the default
tactic can handle this goal.

Since this isolate needs all of the previously establish theory, we
say `with this`, which means "use the properties exposed in the global
scope". Notice, though that we do not use any arithmetic, since the
definition of `rev` is hidden by isolate `rev_theory`.

```
} with this

```
Now we will prove the same property a second time, but using more
tactics and less Z3.

```
isolate double_reverse2 = {
    property arr_rev(A,B) & arr_rev(A,C) -> B = C

```
The proof begins by applying "implication introduction" to move
`arr_rev(A,B) & arr_rev(A,C)` into the assumptions [1]. Then we can
apply array extensionality, since its conclusion `X=Y` matches our
conclusion `B = C`. Ivy finds this match automatically, so we don't
need a `with` claues [2]. 

```
    proof
        apply introImp;  # [1]
        apply arr.spec.extensionality;  # [2]

```
We now have the following proof goal:

   theorem [arr.spec.prop64] {
       property [prop183] (arr_rev(A,B) & arr_rev(A,C))
       property arr.end(B) = arr.end(C)
                & forall I. (0:idx <= I & I < arr.end(B)) -> arr.value(B,I) = arr.value(C,I)
   }

That is, we need to prove a conjunction of two facts: the array lengths are equal and
the array contents are equal. We apply the "and introduction" rule to break this into
two separate goals [3], and then we use `defergoal` to defer the first case, since the
default tactic can handle it [4]. 

```
        apply introAnd;  # [3]
        defergoal;   # [4]

```
Now we need to hand the universal quantifier. We apply the "forall introduction" rule,
which require us to prove the quantified fact for a generic `x` [5]. This particular index
`x` in `B` and `C` corresponds to some index in `A`, which we can establish by assuming 
the `into` theorem for `x` [6].

```
        apply introA;  # [5]
        assume rev_theory.into with U = arr.end(B), X = x #  [6]

```
This leaves us with the following goals (the second being the one we deferred):

   {
       property arr_rev(A,B) & arr_rev(A,C)
       individual x : idx
       property (0:idx <= x & x < arr.end(B)) -> exists Y. rev(arr.end(B),x,Y)
       property (0:idx <= x & x < arr.end(B)) -> arr.value(B,x) = arr.value(C,x)
   }

   {
       property [prop183] (arr_rev(A,B) & arr_rev(A,C))
       property arr.end(B) = arr.end(C)
   }

The default tactic can handle these, since there are no
unstratified quantifier alternations.

```
} with this

```

Implementing array reversal
---------------------------

Now that we have proved our key property of array reversal, let's try implementing array
reversal and see if we can prove that reversing twice gives the same array back.


```
isolate my_rev = {

```
The interface of our array reversal isolate has just one action
`rev` that returns the reverse of the array.

```
    action reverse(x:arr) returns (y:arr)

```
The specification says that the output is the reverse of the input.

```
    specification {
        after reverse {
            ensure arr_rev(old x,y);
        }
    }

```
The implementation just copies the array backward. The index `xidx` starts from
the beginning of the array, while `yidx` starts from the end. Our invariant says
that xidx and yidx-1 are reverse of each other and the output array *y* contains
the reverse of the elements of the input *x* up to the lower index `xidx`. Using the
previously developed theory, Z3 can prove the invariant and also prove that it implies
the specification above on exit of the loop.

```
    implementation {
        implement reverse {
            y := x;
            var xidx := x.begin;
            var yidx := y.end;
            while xidx < x.end
            invariant x.begin <= xidx & xidx <= x.end
            invariant y.begin <= yidx & yidx <= y.end
            invariant y.end = x.end
            invariant idx.succ(Y,yidx) -> rev(x.end,xidx,Y)
            invariant yidx = 0 -> xidx = x.end 
            invariant x.begin <= I & I < xidx & rev(x.end,I,J) -> x.value(I) = y.value(J)
            {
                yidx := yidx.prev;
                y := y.set(yidx,x.get(xidx));
                xidx := xidx.next
            }
        }
    }

```
The isolate needs to uses the properties of the index type and
arrays, as will as the reversal permutation theory and the
definiton of array reversal. Probably it would have been better
to organize all of these in a single object for easy reference.

```
} with idx, arr, rev_theory, def_arr_rev

```

Implementing double array reversal
----------------------------------

Now let's implement double array reversal and use our theorem to show that
it in fact returns its argument.

```
isolate my_double_rev = {

    action reverse2(x:arr) returns (x:arr)

```
The specification of reverse2 just says that its output equals its input.

```
    specification {
        after reverse2 {
            ensure x = old x
        }
    }

```
The implementation just calls `rev` twice.

```
    implementation {
        implement reverse2 {
            x := my_rev.reverse(x);
            x := my_rev.reverse(x);
        }
    }

```
For the verification we need to use the spec of `my_rev`, the
symmetry of array reversal and the double reverse property. The
rest of the forgoing theory is unnecessary.

```
} with my_rev, arr_rev_symm, double_reverse1

```

A more efficient implemention of array reversal
---------------------------------------------

This version of array reversal reverses the array in place, by swapping elements.

```
isolate my_rev2 = {

```
The interface of our array reversal isolate has just one action
`rev` that returns the reverse of the array. Using the same
local variable for both input and output is a clue to the
compiler to perform the operation in place if possible.

```
    action reverse(x:arr) returns (x:arr)

```
The specification says that the output is the reverse of the input.

```
    specification {
        after reverse {
            ensure arr_rev(old x,x);
        }
    }

```
We swap coresponding elements until the lower index is >= the upper index.
The invariant of the loop says that the elements in the rangs `[xidx,yidx)`
are unchanged, while the elements outside this range are reversed.

```
    implementation {
        implement reverse {
            var xidx := x.begin;
            var yidx := x.end;
            while xidx < yidx
            invariant x.begin <= xidx & xidx <= x.end
            invariant x.begin <= yidx & yidx <= x.end
            invariant x.end = (old x).end
            invariant idx.succ(Y,yidx) -> rev(x.end,xidx,Y)
            invariant yidx = 0 -> xidx = x.end 
            invariant x.begin <= I & I < xidx & rev(x.end,I,J) -> x.value(I) = (old x).value(J)
            invariant xidx <= I & I < yidx -> x.value(I) = (old x).value(I)
            invariant yidx <= I & I < x.end & rev(x.end,I,J) -> x.value(I) = (old x).value(J)
            {
                yidx := yidx.prev;
                var tmp := x.get(yidx);
                x := x.set(yidx,x.get(xidx));
                x := x.set(xidx,tmp);
                xidx := xidx.next
            }
        }
    }

} with arr,idx,rev_theory,def_arr_rev

```
Finally, to actually verify the executable code, we export it to the environment.

```
export my_rev.reverse
export my_double_rev.reverse2
export my_rev2.reverse
```

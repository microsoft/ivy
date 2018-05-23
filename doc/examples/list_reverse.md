---
layout: page
title: "Deduction example: array reversal"
---

This is an example of using tactics in Ivy to keep verification conditions
decidable.

The problem we will tackle is reversal of an array. The difficulty
from the point of view of decidability is that, to specify an array
reversal procedure, we need arithmetic in some form. For example,
we might say that array `a` is the reverse of array `b` if they have
the same length `n`, and if, for all `0 <= i < n`, we have `b[i] = a[n-i-1]`. 

The difficulty with this specification is that it applies the
arithmetic operator `+` to the universally quantifier variable `n`,
which means it is not in the `almost uninterpreted` fragment.

We can see this if we try to verify the following program:

    # include collections
    # 
    # type t
    # interpret t -> int
    # type u
    # interpret u -> int
    # 
    # instance arr : array(t,u)
    # 
    # action rev(a:arr) returns(b:arr) = {
    #     var idx : t := 0;
    #     b := b.resize(a.end,0);
    #     while idx < a.end
    #     invariant a.end = b.end & 0 <= idx & idx <= a.end
    #     invariant forall I. 0 <= I & I < idx -> b.value(((a.end)-I)-1) = a.value(I)
    #     {
    # 	b := b.set((a.end) - idx - 1,a.value(idx));
    # 	idx := idx + 1;
    #     };
    #     ensure b.end = a.end & forall I. 0 <= I & I < a.end
    #         -> b.value((a.end)-I-2) = a.value(I)
    # }
    # 
    # export rev

Because the loop invariant is outside the decidable fragment, Ivy gives
this error message:

    # error: The verification condition is not in the fragment FAU.
    #
    # An interpreted symbol is applied to a universally quantified variable:
    # array_rev1.ivy: arr.end(__fml:a) - I

If we try to force Ivy to verify the program with the `complete=fo` option,
it gets stuck producing a counter-model for the `ensure` condition (notice
there is an error there!). 

To avoid the use of arithmetic in defining array reversal, we can
define *relationally* what it means for one array to be the
reverse of another. That is, we will define a relation `rev(n,i,j)` that
holds for two indices `i,j` of an array of length `n`, provide `i` is
the reverse position of `j`, that is, `i + j + 1 = n`. 

We will then prove some useful properties of `rev` in an isolate, and
also provide a procedure that, given `n` and `i`, returns the `j`
such that `rev(n,i,j)`. The proof of this isolate can be done in the
decidable fragment.  For one property, however, we will need to
apply a bit of tactical theorem proving to achieve this.

The isolate hides the theory of arithmetic, allowing us to do the
remainder of our reasoning without any theories. We will implement a
simple array reversal procedure and prove it is correct. Then we
will show that applying reversal twice to an array yields the
original array.

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

To express the definition of array reversal, we start with a more
primitive notion of reversing a range of numbers. We construct an
unbounded sequence `idx` and then define a relation `rev(U,X,Y)` describing a
permutation on the range `[0,U)`. That is, `rev(U,X,Y)` holds when
`X + Y + 1 = U `.

The definition of `rev` and its associated properties are provided
by an isolate `rt` (for "reversal theory"). This isolate hides the
definition of `rev` but gives us some useful properties that will
allow us to reason about array reversal without using arithmetic.

```
instance idx : unbounded_sequence

isolate rt = {

```
The reversal permutation as a relation

```
    relation rev(U : idx, X : idx, Y : idx)

```
An action that computes the reverse of an index position.

```
    action reverse(x:idx,u:idx) returns (y:idx)

    specification {

```
We need the following properties of the `rev` relation:

1. It is a partial function (for a given bound `U`)
2. It is monotonically decreasing over the range `[0,U)`
3. It maps `[0..)` onto `[0..U)`
4. It is symmetric

```
	property rev(U,X,Y) & rev(U,X,Y1) -> Y = Y1
	property rev(U,X,X1) & rev(U,Y,Y1) & X < Y -> Y1 < X1
	property rev(U,X,X1) -> 0 <= X1 & X1 < U
        property rev(U,X,X1) -> rev(U,X1,X)

```
The reverse procedure returns a value that is `rev` of the input.

```
	around reverse {
           require 0 <= x & x < u;
            ...
	   ensure rev(u,x,y)
	}

```
Later, when we reason about double reversal, we will need one
further property, to guarantee the relation is a
permutation. We need to know that every number in the range
`[0,U)` is related to *some* number in that range (in other
words, reversal is a bijection). We don't want to state this
as a property, however, since it contains an unstratified
quantifier alternation (in effect, a function from `idx` to
`idx`). Instead, we state the property as a theorem. The
difference is that this property will not be used by
default. Rather, we will use it explicitly and specialize it
to particular values of `X`, so that the unstratified
quantifier alternation is eliminated.

```
        theorem [into] {
            property 0 <= X & X < U -> exists Y. rev(U,X,Y)
        }

```
The proof of this theorem requires the definition of `rev`
given below. If we try to prove it directly with Z3, however, we
get following error message:

    # error: The verification condition is not in the fragment FAU.
    #
    # An interpreted symbol is applied to a universally quantified variable:
    # list_reverse2.ivy: line 217: X:idx + Y
    # list_reverse2.ivy: line 149: The quantified variable is Y:idx

In the negated VC, a property to prove occurs
negatively. Thus, the existential quantifier above becomes a
universal. When unfolding the definition of `rev` below, we
get the interpreted arithmetic operator `+` applied to the
universal variable `Y` which puts us outside the decidable
fragment. In fact, if we tried to force Ivy to check this
with `complete=fo`, we would find that Z3 produces an
inconclusive result. To avoid, this, we will apply some
tactics.

```
        proof
            apply introImp;
            apply introE with witness = U - X - 1

```
The first step is to apply the "implication introduction" rule,
which is defined in the deduction library. This is a standard rule
of the natural deduction system which says, to prove `p -> q`,
you need to prove `q` from the assumption of `p`. This converts
the proof goal `0 <= X & X < U -> exists Y. rev(U,X,Y)` to:

    # {
    #     property 0 <= X & X < U
    #     #----------------------
    #     property exists Y. rev(U,X,Y)
    # }

To prove the existentially quantified goal, we apply the "existential
introduction" rule, giving a witness for `Y`. In this case, the `Y`
that corresponds to `X` under reversal is `U - X -1` (we can get this
by solving for `Y` in the definition of `rev` below. This gives us the
following goal:

    # {
    #     property 0 <= X & X < U
    #     #-----------------------
    #     property rev(U,X,U - X - 1)
    # }

With the quantifier removed, expanding the definition of
`rev` no longer gives us arithmetic over quantified
variables. This means we can leave the rest of the proof to
the default tactic using Z3.  The general approach is to do
just enough tactical reasoning to eliminate the offending
quantifiers or unstratified functions and then let Z3 do the
rest of the work.



```
    } # end specification section

```
The definition of `rev` is given in the implementation section so that
the arithmetic will be hidden from users of this isolate.

```
    implementation {
        definition rev(U,X,Y) = (X + Y + 1 = U)
        implement reverse {
            y := u - x - 1
        }
    }

```
We say `with idx.impl` to use the implementation of `idx` using
the natural number theory, which is needed to prove the above
properties. Note it's very important *not* to say `with idx`
here, since the specification of `idx` (see order.ivy) contains
various universally quantified properties that, when mixed with
arithmetic, would put us outside the decidable fragment.

```
} with idx.impl

```

Defining array reversal
-----------------------

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
        arr.end(A1) = arr.end(A2) & 
        forall X,Y. rt.rev(arr.end(A1),X,Y) -> arr.value(A1,X) = arr.value(A2,Y)

```
From the symmetry of `rev`, Z3 can prove that `arr_rev` is also symmetric:

```
property [arr_rev_symm] arr_rev(A1,A2) -> arr_rev(A2,A1)

```

Implementing array reversal
---------------------------

Now that we have defined the notion of array reversal, let's write a procedure that
reverses an array a and prove that it returns the correct result.


```
isolate my_rev = {

```
The interface of our array reversal isolate has just one action
`reverse` that returns the reverse of the array.

```
    action reverse(a:arr) returns (b:arr)

```
The specification says that the output is the reverse of the input.

```
    specification {
        after reverse {
            ensure arr_rev(old a,b);
        }
    }

```
The implementation just copies the array backward. 

```
    implement reverse {
        var i : idx := 0;
        b := b.resize(a.end,0);
        while i < a.end
        invariant a.end = b.end & 0 <= i & i <= a.end
        invariant forall I. 0 <= I & I < i & rt.rev(a.end,I,J)
            -> b.value(J) = a.value(I)
        {
            b := b.set(rt.reverse(i,a.end),a.value(i));
            i := i.next;
        };
    }

```
The isolate needs to uses the properties of the index type and
arrays, as well as the reversal permutation theory and the
definition of array reversal. Probably it would have been better
to organize all of these in a single object for easy reference.

```
} with idx, rt, arr, def_arr_rev

```

Double array reversal
---------------------

Now we would like to show that reversing an array twice gives the
original array. By symmetry, this is the same as saying the two
arrays `B` and `C` that are reversals of the same array `A` are
equal. We will prove this in two different ways.

The first way is to start with a lemma. We'll do this in an isolate
so we won't give unwanted help to the second proof below.

```
isolate double_reverse1 = {

```
Our lemma says that corresponding elements of `B` and `C` are equal.

```
    property arr_rev(A,B) & arr_rev(A,C) & 0 <= X & X < arr.end(B)
                   -> arr.value(B,X) = arr.value(C,X)

```
To show this, we need theorem `into`, which tells us that every
index in `B` and `C` corresponds to *some* index in `A`. 
The elements of `B` and `C` are both equal by definition to this
element of `A`, so by transitivity they are equal to each
other. We use the `assume` tactic to bring in theorem `into` as
an assumption in our proof goal, plugging in the specific value
of `U` that we need.

```
    proof
        assume rt.into with U = arr.end(B)

```
Here is the resulting proof goal:

    #     {
    #        property 0 <= X & X < arr.end(B) -> exists Y. rt.rev(arr.end(B),X,Y)
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

    # {
    #     {
    #         property arr.end(B) = arr.end(C)
    #                  & forall I. (0:idx <= I & I < arr.end(B)) -> arr.value(B,I) = arr.value(C,I))
    #         property B:arr = C
    #     }
    #     property (arr_rev(A,B) & arr_rev(A,C)) -> B = C
    # }

Our lemma says the corresponding elements of `B` and `C` are
equal, so by extensionality, `B` and `C` are equal. There is a
quantifier alternation from `arr` to `idx` in the extensionality
property, but it doesn't break stratification, so the default
tactic can handle this goal.

Since this isolate needs all of the previously establish theory, we
say `with this`, which means "use the properties exposed in the global
scope". Notice, though that we do not use any arithmetic, since the
definition of `rev` is hidden by isolate `rt`.

```
} with this

```

### A different proof

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
need a `with` clause [2]. 

```
    proof
        apply introImp;  # [1]
        apply arr.spec.extensionality;  # [2]

```
We now have the following proof goal:

    # theorem [arr.spec.prop64] {
    #     property [prop183] (arr_rev(A,B) & arr_rev(A,C))
    #     property arr.end(B) = arr.end(C)
    #              & forall I. (0:idx <= I & I < arr.end(B)) -> arr.value(B,I) = arr.value(C,I)
    # }

That is, we need to prove a conjunction of two facts: the array lengths are equal and
the array contents are equal. We apply the "and introduction" rule to break this into
two separate goals [3], and then we use `defergoal` to defer the first case, since the
default tactic can handle it [4]. 

```
        apply introAnd;  # [3]
        defergoal;   # [4]

```
Now we need to hand the universal quantifier. We apply the "forall introduction" rule,
which requires us to prove the quantified fact for a generic `x` [5]. This particular index
`x` in `B` and `C` corresponds to some index in `A`, which we can establish by assuming 
the `into` theorem for `x` [6].

```
        apply introA;  # [5]
        assume rt.into with U = arr.end(B), X = x #  [6]

```
This leaves us with the following goals (the second being the one we deferred):

    # {
    #     property arr_rev(A,B) & arr_rev(A,C)
    #     individual x : idx
    #     property (0:idx <= x & x < arr.end(B)) -> exists Y. rev(arr.end(B),x,Y)
    #     property (0:idx <= x & x < arr.end(B)) -> arr.value(B,x) = arr.value(C,x)
    # }

    # {
    #     property [prop183] (arr_rev(A,B) & arr_rev(A,C))
    #     property arr.end(B) = arr.end(C)
    # }

The default tactic can handle these, since there are no
unstratified quantifier alternations.

```
} with this


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

A more efficient reversal
-------------------------

This version of array reversal reverses the array in place, by swapping elements.

```
isolate my_rev2 = {

```
The interface of our array reversal isolate has just one action
`reverse` that returns the reverse of the array, but notice the
input and output are both variable `a`, meaning the compiler
can optimize this action to modify `a` in place.

```
    action reverse(a:arr) returns (a:arr)

```
The specification says that the output is the reverse of the input.

```
    specification {
        after reverse {
            ensure arr_rev(old a,a);
        }
    }

```
We swap elements until we reach the middle of the array.
The variables `i` and `j` hold the indices that we are about to swap.
The invariant of the loop says that the elements in the range `[i,j]`
are unchanged, while the elements outside this range are reversed.

```
    implement reverse {
        if a.end > 0 {
            var i : idx := 0;
            var j := rt.reverse(i,a.end);
            while i < j
            invariant 0 <= i & i <= a.end & a.end = (old a).end & rt.rev(a.end,i,j)
            invariant forall I. (0 <= I & I < i | j < I & I < a.end) 
                                & rt.rev(a.end,I,J)-> a.value(J) = (old a).value(I)
            invariant i <= I & I <= j -> a.value(I) = (old a).value(I)
            {
                var tmp := a.value(j);
                a := a.set(j,a.value(i));
                a := a.set(i,tmp);
                i := i.next;
                j := rt.reverse(i,a.end);
            };
        }
    }

} with idx, rt, arr, def_arr_rev


```
Finally, to actually verify the executable code, we export actions
to the environment. 

```
export my_rev.reverse
export my_double_rev.reverse2
export my_rev2.reverse
```

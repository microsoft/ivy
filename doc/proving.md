---
layout: page
title: IVy as a theorem prover
---

In the development of systems, we sometimes have to reason about
mathematical functions and relations in ways that automated theorem
provers can't handle reliably. For these cases, IVy provides a
facility that allows the user to supply the necessary proofs. IVy's
approach to theorem proving is designed to make maximal use of
automated provers. We do this by localizing the proof into
"isolates". Our verification conditions in each isolate are confined
to a logical fragment or theory that an automated prover can handle
reliably.


Primitive judgments
-------------------

A logical development in IVy is a succession of statements or
*judgments*. Each judgment must be justified by a primitive axiom or
inference rule.

Type declarations
=================

On such primitive is a type declaration, like this:

```
    type t
```

This judgment can be read as "let `t` be a type". It is admissible
provided `t` is new symbol that has not been used up to this point
in the development.

Functions and individuals
=========================

We can introduce a constant like this:

```
    individual n : t

```
where `n` is new. This judgment can be read as "let `n` be a term of type
`t`" and is admissible if symbol `n` has not been used up to this point
in the development.  

Similarly, we can introduce new function and relation symbols:

```
    function f(X:t) : t
    relation r(X:t,Y:t)

```
The first judgment can be read as "for any term *X* of type *t*, let
*f*(*X*) be a term of type *t*".  The second says "for any terms
*X,Y* of type *t*, let *r*(*X*,*Y*) be a proposition" (a term of
type `bool`).

Axioms
======

An *axiom* is a proposition whose truth is admitted by fiat. For
example:

```
    axiom [symmety_r] r(X,Y) -> r(Y,X)

```
The free variables *X*,*Y* in the formula are taken as universally
quantified. The text `symmetry_r` between brackets is a name for the
axiom and is optional. The axiom is simply admitted in the current
context without proof. Axioms are dangerous, since they can
introduce inconsistencies. You should use axioms only if you are
developing a foundational theory and you know what you are doing, or
to make a temporary assumption that will later be removed.

Properties
==========

A *property* is a proposition that can be admitted as true only if
it follows logically from judgments in the current context. For
example:

```
    property [myprop] r(n,X) -> r(X,n)

```
A property requires a proof (see below). If a proof is not supplied,
IVy applies its default proof tactic `auto`.  This calls the
automated prover Z3 to attempt to prove the property from the
previously admitted judgments in the current context.

The `auto` tactic works by generating a *verification condition* to
be checked by Z3. This is a formula whose validity implies that the
property is true in the current context. In this case, the
verification condition is:

    #   (forall X,Y. r(X,Y) -> r(Y,X)) -> (r(n,X) -> r(X,n))

That is, it states that axiom `symmetry_r` implies property `myprop`. 
IVy checks that this formula is within a logical fragment that Z3 can
decide, then passes the formula to Z3. If Z3 finds that the formula is
valid, the property is admitted.


Definitions
===========

A definition is a special form of axiom that cannot introduce an
inconsistency. As an example:

```
    function g(X:t) : t

    definition g(X) = f(X) + 1

```
This can be read as "for all *X*, let *g*(*X*) equal *f*(*X*) + 1". The
definition is admissible if the symbol *g* is "fresh", meaning it
does not occur in any existing properties or definitions in the
current context.  Further *g* must not occur on the right-hand side
of the equality (that is, a recursive definition is not admissible
without proof -- see "Recursion" below).

Theory instantiations
=====================

IVy has built-in theories that can be instantated with a specific type
as their carrier. For example, the theory of integer arithmetic is
called `int`. It has the signature `{+,-,*,/,<}`, plus the integer
numerals, and provides the axioms of Peano arithmetic. To instantiate
the theory `int` using type *u* for the integers, we write:

```
    type u
    interpret u -> int

```
This declaration requires that type `u` is not previously interpreted
and that the symbols `{+,-,*,/,<}` in the signature of `int` are
fresh. Notice, though, that the symbols `{+,-,*,/,<}` are
overloaded. This means that `+` over distinct types is considered to
be a distinct symbol.  Thus, we can we can instantiate the `int`
theory over different types (and also instantiate other theories that
have these symbols in their signature).

Schemata
--------

A *schema* is a compound judgment that takes a collection of judgments
as input (the premises) and produces a judgment as output (the
conclusion). If the schema is valid, then we can provide any
type-correct values for the premises and the conclusion will follow.

Here is a simple example of a schema taken as an axiom:

```
    axiom [congruence] {
        type d
        type r
        function f(X:d) : r
        #--------------------------
        property X = Y -> f(X) = f(Y)
    }

```
The schema is contained in curly brackets and gives a list of premises
following a conclusion. In this case, it says that, given types *d* and *r* and a function *f* from
*d* to *r* and any values *X*,*Y* of type *d*,  we can infer that *X*=*Y* implies
*f*(*X*) = *f*(*Y*). The dashes separating the premises from the conclusion are
just a comment. The conclusion is always the last judgement in the schema.
Also, notice the declaration of function *f* contains a variable *X*. The scope of this
variable is only the function declaration. It has no relation to the variable *X* in the conclusion.

The keyword `axiom` tells IVy that this schema should be taken as valid
without proof. However, as we will see, the default `auto`
tactic treats a schema differently from a simple proposition. That is,
a schema is never used by default, but instead must be explicitly
instantiated.  This allows is to express and use facts that, if they
occurred in a verification condition, would take us outside the
decidable fragment.

Any judgment that has been admitted in the current context can be
*applied* in a proof. When we apply a schema, we supply values for its
premises to infer its conclusion.


```
    property [prop_n] Z = n -> Z + 1 = n + 1
    proof 
        apply congruence

```
The `proof` declaration tells IVy to apply the axiom schema `congruence` to prove the property. 
IVy tries to match the proof goal `prop_n` to the schema's conclusion by picking particular
values for premises, that is, the types *d*,*r* and function *f*. It also chooses terms for the
the free variables *X*,*Y* occurring in the schema. In this case, it
discovers the following assignment:

    # d = t
    # r = t
    # X = Z
    # Y = n
    # f(N) = N + 1

After plugging in this assignment, the conclusion of the rule exactly matches
the property to be proved, so the property is admitted.

The problem of finding an assignment such as the one above is one of
"second order matching".  It is a hard problem, and the answer is not
unique. In case IVy did not succeed in finding the above match, we
could also have written the proof more explicitly, like this:

```
    property [prop_n_2] Z = n -> Z + 1 = n + 1
    proof
        apply congruence with X=Z, Y=n, f(X) = X:t + 1

```
Each of the above equations acts as a constraint on the
assignment. That is, it must convert *X* to
*Z*, *Y* to *n* and *f*(*X*) to *X* + 1. Notice that we had to
explicitly type *X* on the right-hand side of the last equation,
since its type couldn't be inferred (and in fact it's not the same
as the type of *X* on the left-hand side, which is *d*). 

It's also possible to write constraints that do not allow for any
assignment. In this case, Ivy complains that the provided match is
inconsistent.

Proof chaining
==============

A premise of a schema can itself be a property.  When applying the
schema, we are not required to provide values for the premises that
are properties. An unsupplied premise becomes a *subgoal* which we
must then prove.

For example, consider the following axiom schema:

```
    relation man(X:t)
    relation mortal(X:t)

    axiom [mortality_of_man] {
        property [prem] man(X)
        #---------------
        property mortal(X)
    }

```
The scope of free variables such as *X* occurring in properties is
the entire schema. Thus, this schema says that, for any term *X* of
type `t`, if we can prove that `man(X)` is true, we can prove that
`mortal(X)` is true.

We take as a given that Socrates is a man, and prove he is mortal:

```
    individual socrates : t

    axiom [soc_man] man(socrates)

    property mortal(socrates)
    proof
        apply mortality_of_man

```
The axiom `mortality _of_man`, requires us supply the premise
`man(socrates)`. Since this premise isn't present in our theorem,
IVy sets it up as a proof subgoal. We didn't supply a proof of this
subgoal, so IVy uses its default tactic `auto`, which in this case
can easily prove that the axiom `man(socrates)` implies
`man(socrates)`.

If we wanted to prove this manually, however, we could continue our proof by
applying the axiom `soc_man`, like this:

```
    property mortal(socrates)
    proof
        apply mortality_of_man;
        apply soc_man

```
The prover maintains a list of proof goals, to be proved in order
from first to last.  Applying a rule, if it succeeds, removes the
first goal from the list, possibly replacing it with subgoals. At
the end of the proof, the prover applies its default tactic `auto`
to the remaining goals.

In the above proof, we start with this goal:

    # property mortal(socrates)

Applying axiom `mortality_of_man` we are left with the following subgoal:

    # property man(socrates)

Applying axiom `soc_man` then leaves us with no subgoals.

Notice that the proof works backward from conclusions to premises.

A note on matching: There may be many ways to match a given proof
goal to the conclusion of a schema. Different matches can result in
different sub-goals, which may affect whether a proof succeeds. IVy
doesn't attempt to verify that the match it finds is unique. For
this reason, when it isn't obvious there there is a single match, it
may be a good idea to give the match explicitly (though we didn't
above, as in this case there is only one possible match).

When chaining proof rules, it is helpful to be able to see the
intermediate subgoals. This can be done with the `showgoals` tactic,
like this:

```
    property mortal(socrates)
    proof
        apply mortality_of_man;
        showgoals;
        apply soc_man

```
When checking the proof, the `showgoals` tactic has the effect of
printing the current list of proof goals, leaving the goals unchanged.
A good way to develop a proof is to start with just the tactic `showgoals`, and to add tactics
before it. Running the Ivy proof checker in an Emacs compilation buffer
is a convenient way to do this. 

Theorems
========

Thus far, we have seen schemata used only as axioms. However, we can also
prove the validity of a schema as a *theorem*. For example, here is a theorem
expressing the transitivity of equality:

```
    theorem [trans] {
        type t
        property X:t = Y
        property Y:t = Z
        #--------------------------------
        property X:t = Z
    }

```
We don't need a proof for this, since the `auto` tactic can handle
it. The verification condition that IVy generates is:

    #   X = Y & Y = Z -> X = Z

Here is a theorem that lets us eliminate universal quantifiers:

```
    theorem [elimA] {
        type t
        function p(X:t) : bool
        property forall Y. p(Y)
        #--------------------------------
        property p(X)
    }

```
It says, for any predicate *p*, if `p(Y)` holds for all *Y*, then
`p(X)` holds for a particular *X*. Again, the `auto` tactic can
prove this easily. Now let's derive a consequence of these facts. A
function *f* is *idempotent* if applying it twice gives the same
result as applying it once. This theorem says that, if *f* is
idempotent, then applying *f* three times is the same as applying it
once:

```
    theorem [idem2] {
        type t
        function f(X:t) : t
        property forall X. f(f(X)) = f(X)
        #--------------------------------
        property f(f(f(X))) = f(X)
    }

```
The auto tactic can't prove this because the premise contains a
function cycle with a universally quantified variable. Here's the
error message it gives:

    # error: The verification condition is not in the fragment FAU.
    #
    # The following terms may generate an infinite sequence of instantiations:
    #   proving.ivy: line 331: f(f(X_h))

This means we'll need to apply some other tactic. Here is one possible proof:

```
    proof
        apply trans with Y = f(f(X));
        apply elimA with X = f(X);
        apply elimA with X = X

```
We think this theorem holds because `f(f(f(X)))` is equal to `f(f(X))`
(by idempotence of *f*) which in turn is equal to `f(X)` (again, by
idempotence of *f*). This means we want to apply the transitivy rule, where
the intermediate term *Y* is `f(f(x))`. Notice we have to give the value of *Y*
explicitly. Ivy isn't clever enough to guess this intermediate term for us.
This gives us the following two proof subgoals:

    # theorem [prop2] {
    #     type t
    #     function f(V0:t) : t
    #     property [prop5] forall X. f(f(X)) = f(X)
    #     #----------------------------------------
    #     property f(f(f(X))) = f(f(X))
    # }


    # theorem [prop3] {
    #     type t
    #     function f(V0:t) : t
    #     property [prop5] forall X. f(f(X)) = f(X)
    #     #----------------------------------------
    #     property f(f(X)) = f(X)
    # }

Now we see that the conclusion in both cases is an instance of the
idempotence assumption, for a particular value of *X*. This means
we can apply the `elimA` rule that we proved above. In the first case,
the value of `X` for which we are claiming idempotence is `f(X)`.
With this assignment, IVy can match `p(X)` in theorem `elimA` to `f(f(f(X))) = f(X)`.
This substituion produces a new subgoal as follows:

    # theorem [prop2] {
    #     type t
    #     function f(V0:t) : t
    #     property [prop5] forall X. f(f(f(X))) = f(f(X))
    #     #----------------------------------------
    #     property forall Y. f(f(f(Y))) = f(f(Y))
    # }

This goal is trivial, since the conclusion is exactly the same as one
of the premises, except for the names of bound variables. Ivy proves
this goal automatically and drops it from the list. This leaves the
second subgoal `prop3` above. We can also prove this using `elimA`. In
this case `X` in the `elimA` rule corresponds to `X` in our goal.
Thus, we write `apply elimA with X = X`. This might seem a little
strange, but keep in mind that the `X` on the left refers to `X` in
the `elimA` rule, while `X` on the right refers to `X` in our goal. It
just happens that we chose the same name for both variables.

Once again, the subgoal we obtain is trivial and Ivy drops it. Since
there are no more subgoals, the proof is now complete.

#### The deduction library

Facts like `trans` and `elimA` above are included in the library
`deduction`. This library contains a complete set of rules of a system
[natural deduction](https://en.wikipedia.org/wiki/Natural_deduction)
for first-order logic with equality.


Recursion
=========

Recursive definitions are permitted in IVy by instantiating a
*definitional schema*. As an example, consider the following axiom schema:

    # axiom [rec[u]] {
    #     type q
    #     function base(X:u) : q
    #     function step(X:q,Y:u) : q
    #     fresh function fun(X:u) : q
    #     #---------------------------------------------------------
    #     definition fun(X:u) = base(X) if X <= 0 else step(fun(X-1),X)
    # }

This axiom was provided as part of the integer theory when we
interpreted type *u* as `int`.  It gives a way to construct a fresh
function `fun` from two functions:

- `base` gives the value of the function for inputs less than or equal to zero.
- `step` gives the value for positive *X* in terms of *X* and the value for *X*-1

A definition schema such as this requires that the defined function
symbol be fresh. With this schema, we can define a recursive function that
adds the non-negative numbers less than or equal to *X* like this:

```
    function sum(X:u) : u

    definition [defsum] {
       sum(X:u) = 0 if X <= 0 else (X + sum(X-1))
    }
    proof
       apply rec[u]
```

Notice that we wrote the definition in curly brackets. This causes Ivy to 
treat it as an axioms schema, as opposed to a simple axiom.
We did this because the definition has a universally quantified variable
`X` under arithmetic operators, which puts it outside the decidable
fragment. Because this definition is a schema, when we want to use it,
we'll have to apply it explicitly,

In order to admit this definition, we applied the definition
schema `rec[u]`. Ivy infers the following assignment:

    # q=t, base(X) = 0, step(X,Y) = Y + X, fun(X) = sum(X)

This allows the recursive definition to be admitted, providing that
`sum` is fresh in the current context (i.e., we have not previously refered to
`sum` except to declare its type).


### Extended matching

Suppose we want to define a recursive function that takes an additional
parameter. For example, before summing, we want to divide all the
numbers by *N*. We can define such a function like this:

```
    function sumdiv(N:u,X:u) : u

    definition
        sumdiv(N,X) = 0 if X <= 0 else (X/N + sumdiv(N,X-1))
    proof
       apply rec[u]

```
In matching the recursion schema `rec[u]`, IVy will extend the
function symbols in the premises of `rec[u]` with an extra parameter *N* so that
schema becomes:

    # axiom [rec[u]] = {
    #     type q
    #     function base(N:u,X:u) : q
    #     function step(N:u,X:q,Y:u) : q
    #     fresh function fun(N:u,X:u) : q
    #     #---------------------------------------------------------
    #     definition fun(N:u,X:u) = base(N,X) if X <= 0 else step(N,fun(N,X-1),X)
    # }

The extended schema matches the definition, with the following assignment:

    # q=t, base(N,X)=0, step(N,X,Y)=Y/N+X, fun(N,X) = sum2(N,X)
    
This is somewhat as if the functions were "curried", in which case the
free symbol `fun` would match the partially applied term `sumdiv N`.
Since Ivy's logic doesn't allow for partial application of functions,
extended matching provides an alternative. Notice that, 
to match the recursion schema, a function definition must be
recursive in its *last* parameter.

Induction
=========

The `auto` tactic can't generally prove properties by induction. For
that IVy needs manual help. To prove a property by induction, we define
an invariant and prove it by instantiating an induction schema. Here is
an example of such a schema, that works for the non-negative integers:

```
    axiom [ind[u]] {
        relation p(X:u)
        {
            individual x:u
            property x <= 0 -> p(x)
        }
        {
            individual x:u
            property p(x) -> p(x+1)
        }
        #--------------------------
        property p(X)    
    }

```
Like the recursion schema `rec[u]`, the induction schema `ind[u]` is
part of the integer theory, and becomes available when we interpret
type `u` as `int`.

Suppose we want to prove that `sum(Y)` is always greater than or equal
to *Y*, that is:

```
    property sum(Y) >= Y

```
We can prove this by applying our induction schema:

```
    proof
        apply ind[u] with X = Y;
        assume sum with X = x;
        defergoal;
        assume sum with X = x + 1

```
Applying `ind[u]` produces two sub-goals, a base case and an induction step:

    # property x <= 0 -> sum(x) <= x

    # property sum(x) <= x -> sum(x+1) <= x + 1

The `auto` tactic can't prove these goals because the definition of
`sum` is a schema that must explicitly instantiated. Fortunately, it
suffices to instantiate this schema just for the specific arguments
of `sum` in our subgoals. For the base case, we need to instantiate
the definition for `X`, while for the induction step, we need
`X+1`. Notice that we referred to the definiton of `sum` by the name
`sum`.  Alternatively, we can name the definition itself and refer
to it by this name.

After instantiating the definition of `sum`, our two subgoals look like this:

    # theorem [prop5] {
    #     property [def2] sum(Y + 1) = (0 if Y + 1 <= 0 else Y + 1 + sum(Y + 1 - 1))
    #     property sum(Y) >= Y -> sum(Y + 1) >= Y + 1
    # }


    # theorem [prop4] {
    #     property [def2] sum(Y) = (0 if Y <= 0 else Y + sum(Y - 1))
    #     property Y:u <= 0 -> sum(Y) >= Y
    # }


Because these goals are quantifier-free the `auto` tactic can easily
handle them, so our proof is complete.


Naming
======

If we can prove that something exists, we can give it a name.  For
example, suppose that we can prove that, for every *X*, there exists a
*Y* such that `succ(X,Y)`. Then there exists a function that, given an
*X*, produces such a *Y*. We can define such a function called `next`
in the following way:

```
    relation succ(X:t,Y:t)
    axiom exists Y. succ(X,Y)

    property exists Y. succ(X,Y) named next(X)

```
Provided we can prove the property, and that `next` is fresh, we can
infer that, for all *X*, `succ(X,next(X))` holds. Defining a function
in this way, (that is, as a Skolem function) can be quite useful in
constructing a proof.  However, since proofs in Ivy are not generally
constructive, we have no way to *compute* the function `next`, so we
can't use it in extracted code.

Hierarchical proof development
------------------------------

As the proof context gets larger, it becomes increasingly difficult
for the automated prover to handle all of the judgements we have
admitted. This is especially true as combining facts or theories may
take us outside the automated prover's decidable fragment. For this
reason, we need some way to break the proof into manageable parts.
For this purpose, IVy provides a mechanism to structure the proof into
a collection of localized proofs called *isolates*.

Isolates
========

An isolate is a restricted proof context. An isolate can make parts of
its proof context available to other isolates and keep other parts
hidden. Moreover, isolates can contain isolates, allowing us to
structure a proof development hierarchically.

Suppose, for example, that we want to define a function *f*, but keep
the exact definition hidden, exposing only certain properties of the
function. We could write something like this:

```
    isolate t_theory = {

        implementation {
            interpret t -> int
            definition f(X) = X + 1
        }

        theorem [expanding] { 
            property f(X) > X
        }
        property [transitivity] X:t < Y & Y < Z -> X < Z        

    }

```
Any names declared within the isolate belong to its namespace. For
example, the names of the two properties above are
`t_theory.expanding` and `t_theory.transitivity`.

The isolate contains four declarations. The first, says the type `t`
is to be interpreted as the integers. This instantiates the theory
of the integers for type `t`, giving the usual meaning to operators
like `+` and `<`. The second defines *f* to be the integer successor
function.  These two declarations are contained an *implementation*
section. This means that the `auto` tactic will use them only within
the isolate and not outside.

The remaining two statements are properties about *t* and *f* to
be proved. These properties are proved using only the context of the
isolate, without any judgments admitted outside.

Now suppose we want to prove an extra property using `t_theory`:

```
    isolate extra = {

        theorem [prop] {  
            property Y < Z -> Y < f(Z)
        }
        proof
            assume t_theory.expanding with X = Z
    }
    with t_theory

```
The 'with' clause says that the properties in `t_theory` should be
used by the `auto` tactic within the isolate. In this case, the `transitivy` 
property will be used by default. This pattern is particularly useful when
we have a collection of properties of an abstract datatype that we wish to
use widely without explicitly instantiating them. 

Notice that `auto` will not use the interpretation of *t* as the
integers and the definiton of *f* as the successor function, since
these are in the implementation section of isolate `t_theory` and are therefore
hidden from other isolates. Similarly, theorem `expanding` is not used by default
because it is a schema. This is as intended, since including any of these facts would
put the verification condition outside the decidable fragment.

We used two typical techniques here to keep the verification
conditions decidable.  First, we hid the integer theory and the
definition of *f* inside an isolate, replacing them with some
abstract properties. Second, we eliminated a potential cycle in the
function graph by instantiating the quantifier implicit in theorem
`expanding`, resulting in a stratified proof goal.



Hierarchies of isolates
=======================

An isolate can in turn contain isolates. This allows us to structure a
proof hierarchically. For example, the above proof could have been
structured like this:

```
    isolate extra2 = {

        function f(X:t) : t

        isolate t_theory = {

            implementation {
                interpret t -> int
                definition f(X) = X + 1
            }

            theorem [expanding] { 
                property f(X) > X
            }
            property [transitivity] X:t < Y & Y < Z -> X < Z        

        }

        theorem [prop] {  
            property Y < Z -> Y < f(Z)
        }
        proof
            assume t_theory.expanding with X = Z

    }

```
The parent isolate `extra2` uses only the visible parts of the child isolate `t_theory`. 

Proof ordering and refinement
=============================

Thus far, proof developments have been presented in order. That is,
judgements occur in the file in the order in which they are admitted
to the proof context.

In practice, this strict ordering can be inconvenient. For example,
from the point of view of clear presentation, it may often be better
to state a theorem, and *then* develop a sequence of auxiliary
definitions and lemmas needed to prove it.  Moreover, when developing
an isolate, we would like to first state the visible judgments, then
give the hidden implementation.

To achieve this, we can use a *specification* section. The
declarations in this section are admitted logically *after* the other
declarations in the isolate.

As an example, we can rewrite the above proof development so that the
visible properties of the isolates occur textually at the beginning:



```
    isolate extra3 = {

        function f(X:t) : t

        specification {
            theorem [prop] {  
                property Y < Z -> Y < f(Z)
            }
            proof
                assume t_theory.expanding with X = Z
        }

        isolate t_theory = {

            specification {
                theorem [expanding] { 
                    property f(X) > X
                }
                property [transitivity] X:t < Y & Y < Z -> X < Z        
            }

            implementation {
                interpret t -> int
                definition f(X) = X + 1
            }
        }
    }
```

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
"isolates". Our proof obligations in each isolate are confined to a
logical fragment that an automated prover can handle reliably.


Primitives
==========

A logical development in IVy is a succession of statements or
*judgments*. Each judgment must be justified by a primitive axiom or
inference rule.

Type declarations
-----------------

On such primitive is a type declaration, like this:

    type t

This can be read as "let `t` be a type". This judgement is admissible
provided `t` is new symbol that has not been used up to this point
in the development.

Functions and individuals
-------------------------

We can introduce a constant like this:

    individual n : t

where `n` is new. This can be read as "let `n` be of type
`t`". Every type has at least one element in it. This judgement gives
a name to such an element.

Similarly, we can introduce new function symbolss:

    function f(X:t) : t

This is read as "for all *X* of type *t*, let *f*(*X*) be of type *t*". 

Axioms
------

An *axiom* is a statement that is admitted by fiat. For example:

    axiom [idempotence] f(f(X)) = f(X)

The free variable *X* in the formula is taken as universally
quantified. The text "idempotence" between brackets is a name for the
axiom and is optional. The axiom is simply admitted in the current
context without proof. Axioms are dangerous, since they can introduce
inconsistencies. You should use axioms only if you are developing a
foundational theory and you know what you are doing.

Properties
----------

A *property* is a statement that can be admitted only if it follows
logically from judgments in the current context. For example:

    property [idem_n] f(n) = n -> f(f(n)) = n

A property requires a proof (see below). If a proof is not supplied,
IVy applies its proof tactic `auto`.  This calls the automated prover
Z3 to attempt to prove the property from all of previously admitted
judgments in the current context.

Definitions
-----------

A definition is a special form of axiom that cannot introduce an
inconsistency. As an example:

    function g(X:t) : t
    definition g(X) = f(X) + 1

This is read as "for all *X*, let *g*(*X*) be *f*(*X*) + 1". The
definition is admissible if the symbol *g* is "fresh", meaning it does
not occur in any existing properties or definitions. Further *g* must
not occur on the right-hand side of the equality (that is, a recursive
definition is not admissible without proof -- see "Recursion" below).

Theory instantiations
---------------------

IVy has built-in theories that can be instantated with a specific type
as their carrier. For example, the theory of integer arithmetic is
called `int`. It has the signature `{+,-,*,/,<}`, plus the integer
numerals, and provides the axioms of Peano arithmetic. To instantiate
the theory `int` using type *t* for the integers, we write:

    interpret t -> int

This declaration requires that type `t` is not previously interpreted
and that the symbols `{+,-,*,/,<}` in the signature of `int` are
fresh. Notice, though, that the symbols `{+,-,*,/,<}` are
overloaded. This means that `+` over distinct types is considered to
be a distinct symbol.  Thus, we can we can instantiate the `int`
theory over different types (and also instantiate other theories that
have these symbols in their signature).

Schemata
========

A *schema* is a compound judgment that a collection of judgments as
input (the premises) and produces a judgment as output (the
conclusion). The meaning of schema is that we can provide any
type-correct values for the premises and the conclusion will follow.

Here is a simple example of a schema taken as an axiom:

    axiom [congruence] {
        type d
	type r
        function f(X:d) : r
        #--------------------------
        property X=Y -> f(X) = f(Y)
    }

The schema is contained in curly brackets and gives a list of premises
following a conclusion. In this case, it says that, given types *d* and *r* and a function *f* from
*d* to *r*, we can infer that, for all *X*,*Y*, *X*=*Y* implies
*f*(*X*) = *f*(*Y*). The dashes separating the premises from the conclusion are
just a comment. The conclusion is always the last judgement in the rule.

The keyword `axiom` tells IVy that this rule should be taken as
primitive, without proof. 

Any judgment that has been admitted in the current context can be
*applied* in a proof. When we apply a schema, we supply values for its
premises to infer its conclusion.

    property [prop_n] Z=n -> Z + 1 = n + 1
    proof 
        apply congruence

The `proof` declaration tells IVy to apply the axiom schema `congruence` to prove the property. 
IVy tries to match the proof goal `prop_n` to the schema's conclusion by picking particular
values for premises, that is, the types *d*,*r* function *f*. It also chooses values for the
the free variables *X*,*Y* occurring in the schema. In this case, it
discovers the following assignment:

    d = t
    r = t
    X = Z
    Y = n
    f(N) = N + 1

After plugging in this assignment, the conclusion of the rule exactly matches
the property to be proved, so the property is admitted.

The problem of finding an assignment such as the one above is called
"second order matching".  It is a hard problem, and the answer is not
unique. In case IVy did not succeed in finding the above match, we
could also write the proof more explicitly, like this:

    proof
        apply congruence with d=t, r=t, X=Z, Y=n, f(N)=N+1

Each of the above equations acts as a constraint on the assignment. That is,
it must convert *d* to *t*, *r* to *t*, *X* to *Z* and so on. By giving such equations,
we can narrow the possibilities down to just one assignment. We don't have to do this,
however. We can also give a subset of the desired assignment, relying on Ivy's
matching algorithm to fill in the rest.

It's also possible to write constraints that do not allow for any
assignment. In this case, Ivy complains that the provided match is
inconsistent.

Proof chaining
--------------

When applying a schema, we are not required to provide values for the
premises of the schema that are properties. An unsupplied premise
becomes a *subgoal* which we must then prove.

For example, consider the following axiom schema:

    axiom [mortality_of_man] {
        property [prem] man(X)
        #---------------
        property mortal(X)
    }

Suppose we write this proof:

    property mortal(socrates)
    proof
        apply mortality_of_man with X=socrates

To apply the axiom `mortality _of_man`, IVy needs to supply the premise
`man(socrates)`. In the absense of such a judgment, IVy sets it up as a new proof goal. Since we didn't
supply a proof for this subgoal, IVy would use its default tactic
`auto`, which supplies the proof using the automated prover, if possible.

Suppose on the other hand that we have this axiom available:

    axiom [socrates_species] {
        #------------------
	property man(socrates)
    }

We could chain this rule to the first one like this:

    proof
        apply mortality_of_man with X=socrates;
        apply socrates_species

The prover maintains a list of proof goals, to be proved in order from
first to last
Applying a rule, if it succeeds, removes the first goal from the list,
possibly replacing it with subgoals. At the end of the proof, the
prover applies its default tactic `auto` to the remaining goals.

In the above proof, we start with this goal:

    property mortal(socrates)

Applying axiom `mortality_of_man` we are left with the following subgoal:

    property man(socrates)

Applying axiom `socrates_species` then leaves us with no unproved goals.

Notice that proof chaining works backward from conclusions to premises.

Generally speaking, it isn't a good idea to build up complex proof
sequences. Such proofs are difficult to read, since the sub-goals are
not visible. We could instead have been a bit more explicit, like
this:

    property man(socrates)
    proof
        apply socrates_species
    
    property mortal(socrates)
    proof
        apply mortality_of_man with X=socrates

The first proof provides the premise needed by the second.

A note on matching. There may be many ways to match a given proof goal
to the conclusion of a rule. Different matches can result in different
sub-goals, which may affect whether a proof succeeds. IVy doesn't
attempt to verify that the match it finds is unique. For this reason,
when subgoals are produced, it may be a good idea to give the match
explicitly (as we did above, though in this case there is only one
match).

When chaining proof rules, it is helpful to be able to see the
intermediate subgoals. This can be done with the `showgoals` tactic,
like this:

    proof
        apply mortality_of_man with X=socrates;
        showgoals;
        apply socrates_species

When checking the proof, the `showgoals` tactic has the effect of printing the current list
of proof goals, leaving the goals unchanged.

Theorems
--------

Thus far, we have seen schemata used only as axioms. However, we can also
prove the validity of a schema as a *theorem*. Here's a simple example:

    theorem [simple] {
        type t
        function f(X:t) : t
        property forall X. f(f(x)) = f(x)
        #--------------------------------
        

Recursion
---------

Recursive definitions are permitted in IVy by instantiating a
definitional schema. As an example, consider the following axiom schema:

    axiom [ rec[t] ] {
	type q
	function base(X:t) : q
	function step(X:q,Y:t) : q
	fresh function fun(X:t) : q
	#---------------------------------------------------------
	definition fun(X:t) = base(X) if X <= 0 else step(fun(X-1),X)
    }

This schema shows how to construct a fresh function `fun` from two functions:

- `base` gives the value of the function for inputs less than or equal to zero.
- `step` gives the value for positive *X* in terms of *X* and the value for *X*-1

A definition schema such as this requires that the defined function
symbol be fresh. With this schema, we can define a recursive function that
adds the non-negative numbers less than or equal to *X* like this:

    function sum(X:t) : t
    definition sum(X:t) = 0 if X <= 0 else (X + sum(X-1))
    proof
       apply rec[t]

IVy matches this definition to the schema `rec[t]` with the following
assignment:

    q=t, base(X) = 0, step(X,Y) = Y + X, fun(X) = sum(X)

This allows the recursive definition to be admitted, providing that
`sum` is fresh in the current context.

When we instantiate a theory, it generally comes with a recursion
schema for the given type.  For example, if we say:

    intepret t -> int

then the above recursion schema `rec[t]` automatically becomes available.

### Extended matching

Suppose we want to define a function that takes an additional
parameter. For example, before summing, we want to divide all the
numbers by *N*. We can define such a function like this:

    definition sumdiv(N,X) = 0 if X <= 0 else (X/N + sumdiv(N,X-1))
    proof
       apply rec[t]

In matching the recursion schema `rec[t]`, IVy will extend the free
function symbols in the schema with an extra parameter *N* so that
schema becomes:

    axiom [ rec[t] ] = {
	type q
	function base(N:t,X:t) : q
	function step(N:t,X:q,Y:t) : q
	fresh function fun(N:t,X:t) : q
	#---------------------------------------------------------
	definition fun(N:t,X:t) = base(N,X) if X <= 0 else step(N,fun(N,X-1),X)
    }

The extended schema matches the definition, with the following assignment:

    q=t, base(N,X)=0, step(N,X,Y)=Y/N+X, fun(N,X) = sum2(N,X)
    
This is somewhat as if functions were "curried", in which case the
free symbol `fun` would match the term `sum2 N`. The upshot of this is
that to match the recursion schema, a function definition must be
recursive in its last parameter.

Induction
---------

The `auto` tactic can't generally prove properties by induction. For
that IVy needs manual help. To prove a property by induction, we define
an invariant and prove it by instantiating an induction schema. Here is
an example of such a schema:

   axiom ind[t] = {
       relation p(X:t)
       property X <= 0 -> p(X)
       property p(X) -> p(X+1)
       #--------------------------
       property p(X)    
   }

Suppose we want to prove that `sum(X)` is always greater than or equal
to *X*:

    property sum(X) >= X
    proof
       apply ind[t]

This produces two sub-goals, a base case and an induction step:

    property X <= 0 -> sum(X) <= X
    property sum(X) <= X -> sum(X+1) <= X + 1

The `auto` tactic can prove both of these using the definition of
`sum`, if we allow it to use undecidable theories. Later, we'll see a
more reliable way to do this, however.

Generally, when a theory such as the theory of integer arithmetic is
instantiated, a suitable induction schema such as the above is made
available.

Naming
------

If we can prove that something exists, we can give it a name.
For example, suppose that we can prove that, for every *X*, there
exists a *Y* such that `succ(X,Y)`. The there exists a function
that, given an *X*, produces such a *Y*. We can define such a function
called `next` in the following way:

    property exists Y. succ(X,Y) named next(X)

Provided we can prove the property, and that `next` is fresh, we can infer
that, for all *X*, `succ(X,next(X))` holds. Defining a function in this way,
(that is, as a "Skolem function") can be quite useful in constructibg a proof.
It doesn't, however, give us any way to *compute* the function `next`.



Hierarchical proof development
==============================

A proof structured as a sequence of judgments isn't very
organized. Moreover, as the proof context gets larger, it becomes
increasingly difficult for the automated prover to handle it.

Isolates
--------

IVy provides a mechanism to structure the proof into a collection of
localized proofs called "isolates". An isolate is a restricted proof
context. An isolate can make parts of its proof context available to
other isolates and keep other parts hidden. Moreover, isolates can
contain isolates, allowing us to structure a proof development
hierarchically.

Suppose, for example, that we want to define a function *f*, but keep
the exact definition hidden, exposing only certain properties of the
function. We could write something like this:

    type t
    function f(X:t) : t

    isolate t_theory = {

        interpret t -> int
	definition f(X) = X + 1

        property [expanding] f(X) > X
	property [transitivity] X:t < Y & Y < Z -> X < Z	

    }

The isolate contains four statements. The first, says the type `t` is
to be interpreted as the integers. This instantiates the theory of the
integers for type `t`, giving the usual meaning to operators like `+`
and `<`. The second defines *f* to be the integer successor function.

The remaining two statements are properties about *t* and *f* to
prove. These properties are proved using only the context of the
isolate, without any facts declared outside.

Now suppose we want to prove an extra property using `t_theory`:

    isolate extra = {
 
        property [prop] f(f(X)) > X

    }
    with t_theory.expanding, t_theory.transitivity

The 'with' clause says that the properties `expanding` and
`transitivy` from isolate `t_theory` should be included in the context when
proving `extra.prop`. The interpretation of *t* as the integers
and the definiton of *f* as the successor function are ignored.

Exporting properties
--------------------

As an alternative, we cal tell IVY which facts in `t_theory` are to be
made available to other isolates and which are to be hidden. We place
the hidden parts in a component object called `impl`:

    type t
    function f(X:t) : t

    isolate t_theory = {

        object impl = {
            interpret t -> int
	    definition f(X) = X + 1
        }

        property [expanding] f(X) > X
	property [transitivity] X:t < Y & Y < Z -> X < Z	

    }

Now, we can bring in the visible parts of `t_theory` like this:

    isolate extra = {
 
        property [prop] f(f(X)) > X

    }
    with t_theory

Hierarchies of isolates
-----------------------

An isolate can in turn contain isolates. This allows us to structure a
proof hierarchically. For example, the above proof could have been
structured like this:

    type t
    function f(X:t) : t

    isolate extra = {
 
	isolate t_theory = {

	    object impl = {
		interpret t -> int
		definition f(X) = X + 1
	    }

	    property [expanding] f(X) > X
	    property [transitivity] X:t < Y & Y < Z -> X < Z	

	}
 
        property [prop] f(f(X)) > X

    }

The parent isolate uses only the visible parts of the child isolate. 

Proof ordering and refinement
-----------------------------

Thus far, proof developments have been presented in order. That is,
judgements occur in the file in the order in which they are admitted
to the proof context.

In practice, this strict ordering can be inconvenient, or at least not
very pedagogically sound. For example suppose we are developing a
representation of sets based on arrays. We would like to specify first
the visible parts of the interface (for example the algebraic
properties of sets) and then later give the actual definitions of the
set operations in terms of array operations.

To allow this sort of development, IVY constructs the proof order
based on dependencies rather than the textual order within the file.
The rules for dependencies are:

- A property or definition referencing symbol *s* depends on the definition of *s*,
- The properties in an isolate depend on any properties and definitions referenced in its `with` clause,
- A property depends on any textually preceeding properties within the same isolate, and
- A judgment depends on any property explicitly named in its proof.

For these purposes, a property whose proof requires *s* to be fresh
counts as a definition of *s*. For example, `property ... named s`
counts as a definition of *s*.

A proof that can't be ordered because of a dependency cycle is invalid.

As an example, we can rewrite the above proof development so that the
visible properties of the isolates occur textually at the beginning:


    type t
    function f(X:t) : t

    isolate extra = {
 
        property [prop] f(f(X)) > X

	isolate t_theory = {

	    property [expanding] f(X) > X
	    property [transitivity] X:t < Y & Y < Z -> X < Z	

	    object impl = {
		interpret t -> int
		definition f(X) = X + 1
	    }

	}
    }

IVy still requires that the first use of a symbol be its `type` or
`function` declaration.

Note that according to the above rules, a definition cannot depend on
property unless the property is explicitly named in its proof. Suppose,
for example, we have this definitional schema:

    schema genrec[t] = {
        type q
	function pred(X:t) : q
        function step(X:q,Y:t) : q
        function fun(X:t) : q
        property [descending] pred(X) < X
	#--------------------------------
        definition fun(X:t) = 0 if X <= 0 else step(fun(pred(X),X))
    }

This allows us to recur on any value less than *X* rather than just *X*-1.
However, to admit this, we must prove the the function `pred` is descending.	
We can use this schema as follows:

    property [myprop] X-2 < X

    definition mysum(X:t) = 0 if X <= 0 else (X + sum(X-2))
    proof
       apply genrec[t] with descending = myprop





    

    











    










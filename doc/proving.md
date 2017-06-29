---
layout: page
title: IVy as a theorem prover
---

IVy is intended primarily for the development of distributed
systems. In this process, we sometimes have to reason about
mathematical functions and relations in ways that automated theorem
provers can't handle. IVy provides facilities for the user to supply
the necessary proofs. IVy's approach to theorem proving is designed to
make maximal use of automated provers. We do this by localizing the
proof into "isolates". Our proof obligations in each isolate are
confined to a logical fragment that an automated prover can handle
reliably.


Primitives
==========

A logical development in IVy is a succession of statements. Each
statement must be justified by a primitive axiom or inference rule of
the system.

Type declarations
-----------------

On such primitive is a type declaration, like this:

    type t

This can be read as "let `t` be a type". This judgement is admissible
provided `t` is fresh symbol that has not been used up to this point
in the development.

Functions and individuals
-------------------------

We can introduce a constant like this:

    individual n : t

where `n` is fresh. This can be read as "let `n` be of type
`t`". Every type has at least one element in it. This judgement gives
a name to such an element.

Similarly, we can introduce functions:

    function f(X:t) : t

This is read as "for all *X* of type *t*, let *f*(*X*) be of type *t*". 

Axioms
------

An *axiom* is a statement that is admitted by fiat. For example:

    axiom [idempotence] f(f(X)) = f(X)

The free variable *X* in the formula is taken as universally
quantified. The text "idempotence" between brackets is a name for the
axiom and is optional. The axiom is simply admitted in the current
context without proof. 

Properties
----------

A *property* is a statement that can be admitted only if it follows
logically from the facts in the current context. For example:

    property [idem_n] f(n) = n -> f(f(n)) = n

A property requires a proof. If a proof is not supplied, IVy applies its proof tactic `auto`.
This calls the automated prover Z3 to attempt to prove the property from the judgments
in the current context.

Definitions
-----------

A definition is a special form of axiom that cannot introduce an
inconsistency. As an example:

    function g(X:t) : t
    definition g(X) = f(X) + 1

This is read as "for all *X*, let *g*(*X*) be *f*(*X*) + 1". The
definition is admissible if the symbol *g* is "fresh", meaning it does
not occur in any existing properties or definitions. Further *g* must
not occur on the right-hand side of the equality (that is, a
definition may not be recursive, but see "Recursion" below).

Theory instantiations
---------------------

IVy has built-in theories that can be instantation with a specific
type as their carrier. For example, the theory of integer arithmetic
is called `int`. It has the signature `{+,-,*,/}`, plus the integer
numerals, and provides the axioms of Peano arithmetic. To instantiate
the theory `int` using type *t* for the integers, we write:

    interpret t -> int

This declaration requires that type `t` as well as the symbols
`{+,-,*,/}` in the signature of `int` be fresh. Notice, though, that
the symbols `{+,-,*,/}` are polymorphic. This means that `+` over
distinct types is considered to be a distinct symbol.  This means we
can we can instantiate the `int` theory over different types (and also
instantiate other theorys that have these symbols in their signature).

Inference rules
===============

An inference rule takes a collection of judgments as input (the
premises) and produces a judment as output (the conclusion). The rule
is *sound* if the conclusion logically follows from the premises.

Here is a simple example of an inference rule:

    schema congruence1 = {
        type d
	type r
        function f(X:d) : r
        #--------------------------
        property X=Y -> f(X) = f(Y)
    }

This rules says that, given types *d* and *r* and a function *f* from
*d* to *r*, we can infer that, for all *X*,*Y*, *X*=*Y* implies
*f*(*X*) = *f*(*Y*). The dashes separating the premises from the conclusion are
just a comment. The conclusion is always the last judgement in the rule.

The keyword `schema` tells IVY that this rule should be taken as
primitive, without proof. Like `axiom`, `schema` runs the risk of
introducing an inconsistency.

Any schema that is defined in the current context can be used in a proof.
Here is an example:

    property [prop_n] Z=n -> Z + 1 = n + 1
    proof congruence1

The `proof` declaration tells IVy to use schema `congruence1` to prove the property. 
IVy tries to match the proof goal `prop_n` to the schema's conclusion by picking particular
values for types *d*,*r* function *f* and the free variables *X*,*Y*. In this case, it
discovers the following assignment:

    d = t
    r = t
    X = Z
    Y = n
    f(X) = X + 1

After plugging in this assignment, the conclusion of the rule exactly matches
the property to be proved, so the property is admitted.

In case IVY did not succeed in finding this match, we could also write
the proof more explicitly, like this:

    proof concruence1 with d=t, r=t, X=Z, Y=n, f(X)=X+1

We could also give a subset of this assignment, relying on IVY's
matching algorithm to fill in the rest.

Proof chaining
--------------

If the premises of a rule contain a property that is not present in the current context,
IVy will try to prove these premises in turn. For example, consider the following rule:

    schema mortality_of_man = {
        property [prem] man(X)
        #---------------
        property mortal(X)
    }

Suppose we write this proof:

    property mortal(socrates)
    proof mortality_of_man with X=socrates

To match the rule, IVy needs to supply the premise
`man(socrates)`. IVy sets it up as a new proof goal. Since we haven't
specified any proof for this sub-goal, IVy will use its default tactic
`auto` which supplies the proof using the automated prover.

Suppose on the other hand that we have this rule available:

    schema socrates_species = {
        #------------------
	man(socrates)
    }

We could chain this rule to the first one like this:

    proof mortality_of_man with X=socrates; socrates_species

The prover maintains a list of proof goals, each with a context.
Applying a rule, if it succeeds, removes the first goal from the list,
possibly replacing it with sub-goals. At the end of the proof, the
prover applies its default tactic `auto` to the remaining goals.

Generally speaking, it isn't a good idea to build up complex proof
sequences, since the sub-goals are not visible. We could instead have
been a bit more explicit, like this:

    property man(socrates)
    proof socrates_species
    
    property mortal(socrates)
    proof mortality_of_man with X=socrates

Recursion
---------

Recursive definitions are permitted in IVy by instantiating a
definitional schema. As an example, consider the following schema:

    schema rec[t] = {
	type q
	function base(X:t) : q
	function step(X:q,Y:t) : q
	fresh function fun(X:t) : q
	#---------------------------------------------------------
	definition fun(X:t) = base(X) if X <= 0 else step(fun(X-1),X)
    }

This schema shows how to construct a fresh function `fun` from two functions:

- `base` gives the value of the function for inputs less than or equal to zero.
- `step` gives the value for positive *X* in terms of `X` and the value for `X-1`

A definition schema such as this requires that the defined function
symbol be fresh. With this schema, we can define a recursive function that
adds the non-negative numbers less than or equal to *X* like this:

    function sum(X:t) : t
    definition sum(X:t) = 0 if X <= 0 else (X + sum(X-1))
    proof rec[t]

IVy matches this definition to the schema `rec[t]` with the following
assignment:

    q=t, base(X) = 0, step(X,Y) = Y + X, fun(X) = sum(X)

This allows the recursive definition to be admitted. When we instantiate
a theory, it generally comes with an induction schema for the given type.
For example, if we say:

    intepret t -> int

then the above induction schema automatically becomes available.

### Extended matching

Suppose we want to define a function that takes an additional
parameter. For example, before summing, we want to divide all the
numbers by *N*. We can define such a function like this:

    definition sumdiv(N,X) = 0 if X <= 0 else (X/N + sumdiv(N,X-1))
    proof rec[t]

In matching the recursion schema `rec[t]`, IVy will extend the free function symbols in the schema with an extra
parameter *N* so that schema becomes:

    schema rec[t] = {
	type q
	function base(N:t,X:t) : q
	function step(N:t,X:q,Y:t) : q
	fresh function fun(N:t,X:t) : q
	#---------------------------------------------------------
	definition fun(N:t,X:t) = base(N,X) if X <= 0 else step(N,fun(N,X-1),X)
    }

The extended schema matches the definition, with the following assignment:

    q=t, base(N,X)=0, step(N,X,Y)=Y/N+X, fun(N,X) = sum2(N,X)
    
This is somewhat as if functions were "Curried", in which case the free symbol `fun`
would match the term `sum2 N`. The upshot of this is that to match the
recursion schema, a function definition must be recursive in its last
parameter.

Induction
---------

The `auto` tactic can't generally prove properties by induction. For
that IVy needs manual help. To prove a property by induction, we define
an invariant and prove it by instantiating an induction schema. Here is
an example of such a schema:

   schema ind[t] = {
       relation p(X:t)
       property X <= 0 -> p(X)
       property p(X) -> p(X) + 1
       #--------------------------
       property p(X)    
   }

Suppose we want to prove that `sum(X)` is always greater than or equal
to *X*:

    property sum(X) >= X
    proof ind[t]

This produces two sub-goals:

    property X <= 0 -> sum(X) <= X
    property sum(X) <= X -> sum(X+1) <= X + 1

The `auto` tactic can prove both of these using the definition of `sum`.

Generally, when a theory such as the theory of integer arithmetic is instantiated,
a suitable induction schema such as the above is made available.

Naming
------

If we can prove that something exists, we can give it a name. That is,
we can reason according to this schema:

    schema naming = {
        type t
	relation p(X:t)
        property exists X. p(X)
	fresh individual n:t
	#----------------------
	property p(n)
    }

This rule gives a name to a value satisfying *p*, provided we can show that such a value exists. For example:

    property exists Y. succ(X,Y)

    function next(X:t):t
    property succ(X,next(X))
    proof naming with n = next(X), p(Y) = succ(X,Y)

This generates a proof goal `exists Y. succ(X,Y)` that is discharged by `auto` using the property above.

This kind of argument is common enough that IVy provides a shorthand for it:

    function next(X:t):t
    property exists Y. succ(X,Y) named next(X)

This transforms the property to `succ(X,next(X))`, provided `next` is
fresh. Readers familiar with logic may recognize this transformation as
"Skolemization".


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
    with t_theory.expanding, t_theory.transivity

The 'with' clause says that the properties `expanding` and
`transitivy` from isolate `t_theory` should be included in the context when
proving `extra.prop`. The interpretation of *t* as the integers
and the definiton of *f* as the successor function will be ignored.

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
    proof genrec[t] with descending = myprop





    

    











    










---
layout: page
title: Decidability
---

Automated provers can substantially increase productivity in the
formal verification of complex systems. However, the unpredictability
of automated provers presents a major hurdle to usability of these
tools. To be usable in large proofs, the performance of proof
automation must be:

1. Predictable, for example not diverging on small problems,
2. Continuous, that is, not highly sensitive to small input changes, and
3. Transparent, that is, providing actionable feedback when proof fails.

These issues are particularly acute in case of provers that handle
undecidable logics, for example, first-order logic with quantifiers.

On the other hand, there is a long history of work on *decidable*
logics or fragments of logics. Generally speaking, decision procedures
for these logics perform more predictably and fail more transparently
than provers for undecidable logics. In particular, in the case of a
false proof goal, they usually can provide a concrete counter-model to
help diagnose the problem.

Ivy is designed to support the user in reducing the proof of
correctness of a system to lemmas expressed in a decidable fragment of
the logic. The lemmas checked by the decision procedure are also
called *verification conditions*. If a verification condition falls outside
the decidable fragment, Ivy produces an explanation for this in terms
of specific formulas appearing in the program or its proof. The user then
has a variety of options available for correcting the problem.

When specifying and implementing a system in IVy, it's important to
understand the decidable fragment, and also how verification
conditions are produced. This understanding will help to plan a
specification in advance to achieve decidable verification conditions,
and also to correct problems as they arise.

Verification conditions
=======================

Proofs of programs can be couched in terms of the calculus of *weakest
liberal preconditions*. If *S* is a program statement and *R* is a some
condition on the program state, `wlp(S,R)` is the weakest condition *P*
such that, if *P* holds before the execution of *S* and if *S* terminates,
then *R* holds after the execution of *S*.

As an example, consider the following Ivy code:

    type t
    interpret t -> nat

    action decr(x:t) returns (y:t) = {
        require x > 0;
        y := x - 1;
        ensure y < x;
    }

    export decr

The verification condition for this program can be written as:

    x > 0 -> wlp(y := x - 1, y < x)

That is, the precondition `x > 0` has to imply that after executing
`y := x - 1`, the postcondition `y < x` holds (assuming the theory
of the natural numbers holds for type `t`).

One of the rules of the wlp calculus is this:

    wlp(y := e,R) = R[e/y]

That is to get the weakest liberal precondition of *R* with respect
the the assignment `y := e`, we just substitute *e* for *y* in *R*.
In our example above, the verification condition can therefore
be written as:

    x > 0 -> x - 1 < x

Since this formula is valid over the natural numbers, meaning it holds
true for any natural number *x*, we conclude that the program is
correct. 

In fact, we can check the validity of this formula automatically.
Technically, the way this is done is by *negating* the formula,
then passing it to an tool called an [SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) to determine
if it is *satisfiable*. In this case, the negated verification condition
is:

   ~(x > 0 -> x - 1 < x)

which is logically equivalent to:

   x > 0 & x - 1 >= x

We can easily see that this is unsatisfiable, in the sense that there
is no natural number *x* that makes it true.

Moreover, a typical SMT solver can determine definitely whether this
formula is satisfiable, since it is expressed in the form of affine
constraints over the natural numbers without quantifiers. Solving
constraints of this kind is an NP-complete problem. This means that all
known solution algorithms use exponential time in the worst case,
but in practice we can almost always solve problems that have a moderate
number of variables.

More generally, a typical SMT solver can handle a theory called QFLIA,
which stands for "quantifier-free linear integer arithmetic" and
allows us to form arbitrary combinations of affine constraints with
"and", "or" and "not". We can easily reduce formulas with
natural-number variables to formulas using only integer variables, so
the solver doesn't need a special theory for natural numbers.

If the negated verification condition has a solution, it means that
the verification condition is not valid, so something is wrong with
our proof. Suppose, for example, we change the precondition of action
`decr` from `x > 0` to `x < 42`. The negated verification condition
becomes:

    x < 42 & x - 1 >= x

In Ivy's natural number theory, we have `0 - 1 = 0`. That means that
the above formula is actually true for `x = 0`. The assignment `x = 0`
is called a *model* of the formula, that is, it describes a possible
situation in which the formula is true. That means the assignment `x =
0` is also a *counter-model* for the verification condition: it shows
why the proof doesn't work.

Counter-models are extremely important from the point of view of
transparency.  That is, if our proof fails, we need a clear
explanation of the failure so we can correct the system or its
specification.

The wlp calculus provides us with rules to cover all of the basic
programming constructs in the Ivy language. For example, another way
to look at the above example is to consider `requires` and `ensures`
as program statements that have a semantics in terms of wlp.
When verifying action `decr`, IVy treats the `requires` statement
as an *assumption* and the `ensures` statement as a *guarantee*.
This means the program statement we must verify is really:

    assume x > 0;
    y := x - 1;
    assert y < x

The semantics of the `assume` and `assert` statements are given by:

    wlp(assume Q, R) = (Q -> R)
    wlp(assert Q, R) = (Q & R)

That is, we treat `assume Q` as a statement that only terminates if
*Q* is true, and `assert Q` as a statement that only succeeds if *Q*
is true (that is, if `Q` is false, it does not even satisfy the
postcondition `true`). 

We can compute the wlp of a sequential composition of statements like this:

    wlp(S;T, R) = wlp(S,wlp(T,R))

To show that our action `decr` satisfies its guarantees, assuming its assumptions,
we compute the wlp of `true`. Computing this for our example using the above rule,
we have:

    wlp(assert y < x, true) = (y < x)
    wlp(y := x -1, y < x) = (x - 1 < x)
    wlp(assume x > 0, x - 1 < x) = (x > 0 -> x - 1 < x)

which is just what we got before. Carrying on, we have this rule for conditionals:

    wlp(if C {T} {E}, R) = ((C -> wlp(T,R)) & (~C -> wlp(E,R)))

For a while loop with invariant I, the wlp is defined as:

    wlp(while C invariant I {B}, R) = I
                                      & forall mod(B). I & C -> wlp(B,I)
                                      & forall mod(B). I & ~C -> R

Where `mod(B)` is the list of variables modified in the loop body
*B*. This says, essentially, that the invariant must initially hold,
that the loop body must preserve the invariant if the entry condition
holds, and that otherwise the invariant implies the postcondition.

Finally a program (or an isolate) maintains its invariant *I* if its
initializer establishes *I* and if each exported action preserves 
*I*. Thus, the verification condition for a program is:

    wlp(init,I)

where `init` is the initializer, and, for each exported action *a*:

    I -> wlp(a,I)

Notice we haven't dealt with procedure calls here, but for present
purposes we can consider that all calls are "in-lined" when verifying
the program.

Verification conditions for even moderately complex programs are big
messy formulas that are hard to read. Fortunately, from the point of
view of decidability, we need not be concerned with the exact form of
the VC. Rather, for each formula occurring in the program or its
specifications, we will be concerned with whether the formula
occurs *positively* in the VC, or *negatively* or both. 

A positive occurrence is one under an even number of negations,
while a negative occurrence is under an odd number. For example,
in the following formula:

    ~(~P | Q)

*P* occurs positively and *Q* occurs negatively. In the formula
`P -> Q`, *P* occurs negatively and *Q* positively, since this
is equivalent to `~P | Q`. In the formula `P <-> Q`, *P* and *Q*
occur *both* positively and negatively, since this is equivalent
to `(P -> Q) & (Q -> P)`.

In the negated verification conditions, generally speaking, an
assumption occurs positively, while a guarantee occurs
negatively. Assignments in the code behave like assumptions.  To see
this, we can rewrite the semantics of assignment using a quantifier,
like this:

    wlp(y := e, R) = R[e/y]
                   = forall y. y = e -> R

Using this method, and converting to [prenex normal form](https://en.wikipedia.org/wiki/Prenex_normal_form), the
negated VC for our example becomes a conjunction of the following
three formulas:

    x > 0
    y = x - 1
    ~(x < y)

We can see that the assumption `x > 0` occurs positively, the assignment
`y = x - 1` occurs positively as an equation, and the guarantee `x < y`
occurs negatively. 

On the other hand, as noted above, the VC's for a program invariant
*I* have this form: `I -> wlp(a,I)`. This means that the invariant *I*
occurs both positively and negatively (or put another way, it is both
an assumption and a guarantee). 

Understanding which formulas occur positively and negatively in the negated VC
will be important in understanding why the VC is or is not in the decidable
fragment.

The decidable fragment
---------------------- 

IVy defines a subset of first-order formulas as its *decidable
fragment*. Whether a formula is in the fragment can depend on which
theories are in use. The decidable fragment has the property that,
given enough time and memory, the SMT solver Z3 that underlies IVy can
always determine whether a formula in the fragment is satisfiable, and
if it is, give a model of the formula. In practice, Z3 behaves in a
much more predictable, continuous and transparent manner than it does
for formulas outside the fragment. Generally speaking, it will succeed
on small formulas, its performance will not be greatly effected by
small changes in the formula, and it can always effectively explain why
the VC is invalid by giving a counter-model. Outside the fragment, Z3
can easily diverge on a small formula, or because of a slight change
in the formula syntax, and it does not give reliable counter-models.

The main issue in defining the decidable fragment is the instantiation
of quantifiers. In fact, all the quantifier-free formulas are in the decidable
fragment. Suppose, as an example, that we have the following
assumption in the program:

    forall X. f(X) > X

This formula will occur positively as one conjunct of the negated VC.
The way Z3 handles this formula is by plugging in [ground terms](https://en.wikipedia.org/wiki/Ground_expression) for
the universally quantified variable *X*. This is called *instantiating*
the quantifier. For example, if there is some constant `y` in the program
of the appropriate type, we could create the following instantiation:

    f(y) > y

Clearly, if the VC is unsatisfiable using just this instantiation,
then it is unsatisfiable in general. In fact, the method of using
ground instances is complete in the sense that if a first-order logic
formula is unsatisfiable, then some finite set of instances of the
formula is unsatisfiable (this is a consequence of [Herbrand's
theorem](https://en.wikipedia.org/wiki/Herbrand%27s_theorem)).

Unfortunately, the fact that some instantiation is satisfiable tells
us nothing in general. Z3 might go on forever generating ground
instances without ever constructing a model of the formula. For example,
we might generate `f(y) > y`, then `f(f(y)) > f(y)`, then `f(f((y))) > f(f(y))`
and so on, *ad infinitum*.

In the decidable fragment, however, we can show that there is always a
*finite* set of ground instances such that, if these are satisfiable,
then the formula is satisfiable. As you may imagine, this set depends
strongly on the way that function symbols and quantifiers are used.

Effectively propositional formulas
==================================

For the moment, we will consider just the formulas with the EA quantifier
structure. That means the in prenex normal form, they have this form:

    exists X1,...,XN. forall Y1,...,YM. p(X1,...,XN,Y1,...,YM)

From the point of view of satisfiability of the formula, the initial
existential quantifiers don't matter. That is, `exists X.p(X)` is
satisfiable exactly when `p(X)` is satisfiable. So in the following we
will assume any initial existential quantifiers have been dropped,
leaving only universal quantifiers.

If the predicate `p` contains no function symbols, we say the formula
is in the [effectively propositional](https://en.wikipedia.org/wiki/Bernays%E2%80%93Sch%C3%B6nfinkel_class) fragment (EPR). Since we can only
generate a finite set of instances of such a formula (by plugging in
constants for the universal variables) it follows that this fragment
is decidable.

Though this fragment seems fairly limited, we can still do some useful
reasoning about relations with is, especially about orders. For example,
suppose we take the axioms of a partial order as assumptions:

    forall X,Y,Z. X < Y & Y < Z -> X < Z
    forall X,Y. ~(X < Y & Y < Z)

Notice these are in EPR. The VC for the following program is also in
EPR:

    require forall X,Y. r(X,Y) -> X > Y;
    if r(x,y) & r(y,z) {
        r(x,z) := true
    };
    ensure forall X,Y. r(X,Y) -> X > Y;

To see this, let's expand it out to the conjunction of the following formulas
in prenex normal form:

    forall X,Y. r(X,Y) -> X > Y
    r(x,y) & r(y,z) -> (r'(x,z) & forall X,Y. X ~= x | Y ~= y | r'(X,Y) = r(X,Y))
    ~(r(x,y) & r(y,z)) -> r'(X,Y) = r(X,Y))
    exists X,Y. ~(r'(X,Y) -> X > Y)

The first of these formulas says that the precondition holds. The second says
that if we take the "if" branch, then *r* is updated so that `r(x,z)` holds
and otherwise it remains unchanged. The third says that if we take the "else"
branch, *r* is unchanged. The last says that, finally, the guarantee is false.
Notice that a fresh symbol *r*' was introduced. Technically, this symbol
was introduced to allow us to move a universal quantifier on *r* to prenex
position without 'capturing' other occurrences of *r*. However, we can think
of it as just the "next" value of *r*, after the assignment.

We can see that the precondition and the constraint defining the
semantics of assignment both occur positively. These formulas are in
EPR, and so the corresponding conjuncts of the negated VC also are.
The guarantee formula occurs negatively as `exists X,Y. ~(r'(X,Y) -> X > Y)`.
That is, when we see `~forall X. p(X)`, we convert it to the
equivalent `exists X. ~p(X)` in prenex form. This formula is also in
EPR. In fact, IVy will convert it to `~(r'(a,b) -> a > b)`, where *a*
and *b* are fresh constant symbols.

In general, if we don't use function symbols, and if all of our assumptions
and guarantees are A formulas, then the negated VC will be in EPR.

Stratified function symbols
===========================

EPR is a very restrictive logic, since in effect it only allows us to say
that something exists if it has an explicit name. We can go a bit further
by adding *stratified* function symbols. For example, suppose we define
the following vocabulary of functions and constants:

    individual x : t
    function f(X:t) : u
    function g(Y:u) : v

Using this vocabulary, we can only generate three ground terms: `x,
f(x), g(f(x))`. This means the EA formulas using this vocabulary are
decidable. In general, suppose we construct a directed graph `(V,E)`
where the vertices *V* are the types, and we have an edge `(t,u)` in
`E` whenever there is a function from `... * t * ...` to *u*. The
function symbols are *stratified* if there is no cycle in this graph
(including trivial cycles from *t* to *t*). Stratified EA formulas are
in the decidable fragment. Since the axioms of equality are in EPR,
the equality symbol is also allowed.

Using stratified function symbols is an important strategy for keeping
verification conditions in the decidable fragment. When planning the
specification of a system, it is useful to carefully choose an order
on the types, so that it is possible to use only functions from lesser
to greater types. When a functions from types *t* to *u* and *u* to
*t* are both needed, the best practice is to separate these function
symbols by confining them to different isolates.

Stratified quantifier alternations
==================================

Ultimately we need to be able to write formulas in AE form. That is,
we want to say things like "for every epoch E there exists a leader
L". When these formulas occur positively (as assumptions) they are not
in EPR. However, the decidable fragment still contains a limited
subset of such formulas.

To see this, we need to understand how AE formulas are handled when
determining satisfiability. This is done using a transformation called
[skolemization](https://en.wikipedia.org/wiki/Skolem_normal_form). The formula `forall X. exists Y. p(X,Y)` is
satisfiable if and only if `forall X. p(X,f(X))` is satisfiable for a
fresh function symbol *f* called a *Skolem function*. This means that
we can always eliminate all of the existential quantifiers from the
negated VC. However, the Skolem functions must also be considered with
regard to decidability. That is, if the set of all function symbols, 
*including* Skolem functions, is stratified, then the formula is in
the decidable fragment. Another way to think of this is that
the quantifier sequence  `forall X:t. exists Y:u` induces an arc
from *t* to *u* in the type graph. 

In fact, we can be a little more liberal than this. Consider the
formula:

    forall X:t,Y:u. q(X,Y) -> exists Z:v. p(X,Z)

There is no arc induced from type *u* to type *v*, since the variable
*Y* does not occur under the existential quantifier, and thus the
Skolem function does not depend on it.

Because of stratified quantifier alternations, the negated VC of
the following program is in the decidable fragment:

    require forall X:t. exists Y:u. r(X,Y);
    if f(x) = y {
        r(x,y) := true
    };       
    ensure forall X:t. exists Y:u. r(X,Y)

The precondition occurs positively, so in introduces an arc from *t*
to *u*. The postcondition occurs negatively, so it is an EA formula.
Since there are no other arcs in the type graph, it is acyclic, so the
negated VC is stratified.

Relevant vocabularies
=====================

We can take the decidable fragment further by considering the set of
ground instances needed for the proof in greater detail.

Following [Ge and de Moura](http://leodemoura.github.io/files/ci.pdf),
we will define a *relevant vocabulary* for every universal quantifier
and for each argument of every uninterpreted function or predicate
symbol. The idea is that, if we instantiate each universal quantifier
with just the ground terms in its relevant vocabulary, then any model
of these instances can be converted to a model of the original
formula. If the relevant vocabulary is finite, the formula is in the
decidable fragment.

To determine the relevant vocabularies, we have a set of rules that
depend on the formula. We will say that `V[X]` is the relevant
vocabulary of universally quantified variable `X` and `V[f,i]` is the
relevant vocabulary of argument *i* of uninterpreted function or
predicate symbol *f*.  The rules are in one of two forms:

- If vocabulary V contains term t then vocabulary W contains term u, or
- Vocabulary V equals vocabulary U.

The relevant vocabularies are the least ones that satisfy all the
rules. To express the rules, we use `t[X1...XN]` to stand for a term
with free variables `X1...XN` (so if N=0, it is a ground term). We
use `t[V1...VN]` to stand for any instantiation of *t* using the
vocabularies `V1...VN`.

For first-order logic, we have the following rules:

- if `t[X1...XN]` is the *i*th argument of *f*, every instance
  `t[V[X1],...,V[X1]]` is in V[f,i]

- if universal variable *X* is the *i*th argument of *f*, then `V[X] =
  V[f,i]`.

As an example, consider the conjunction of the following formulas:

    r(f(a),c)
    forall X. r(f(X),X)

The relevant vocabularies are:

    V[f,1] = {a,c}
    V[r,1] = {f(a),f(c)}
    V[r,2] = {a,c}
    V[X] = {a,c}

We can arrive at this result by just applying the rules until we reach
a fixed point. From the first rule, we have `V[f,1] = {a}` and `V[r,2]
= {c}`. Then, from the second rule, because *X* occurs in argument
position 1 of *f* and 2 of *r*, we have `V[f,1] = V[r,2] = V[X] =
{a,c}`.  The first rule then gives us `V[r,1] =
{f(a),f(c)}` and we have reached a fixed point.

Since the relevant vocabularies are finite, this conjunction is in the
decidable fragment.

To handle equality, we introduce a vocabulary `V[t]` for each type *t*
and add these rules:

- If `X:u = e` or `e = X:u` occurs, then `V[X] = V[u]`,

- If `t[X1...XN]:u = e` or `e = t[X1...XN]:u`  occurs then every instance
`t[V[X1],...,V[XN]]` is in `V[u]`.

As an example, suppose *f* is a function from *u* to *u* and we have
this conjunction:

    f(a) = c
    forall X. r(f(X),X)

The relevant vocabularies are:

    V[u] = {f(a),c}
    V[f,1] = {a}
    V[r,1] = {f(a)}
    V[r,2] = {a}
    V[X] = {a}

That is, even though the function *f* is not stratified, we still need
only a finite instantiation to determine satisfiability of this
formula. It is easy seen, however, that all the stratified formulas
have finite relevant vocabularies.

To determine if the relevant vocabulary is finite, we don't need to
compute it. It suffices to determine if the rules create a cycle that
can generate an infinite set of terms.  To do this, we build a graph
whose nodes are vocabularies and whose arcs are defined by the
following rules:

| term                 |  arc(s)         |
|----------------------|-----------------|
| f(..,X,..)           | V[X] <-> V[f,i] |
| f(..,t[..,X,..],..)  | V[X] -> V[f,i]  |
| X:u = e              | V[X] <-> V[u]   |
| t[...,X:u,...] = e   | V[X] -> V[u]    |
|                      |                 |

where *i* is the relevant argument position in *f* and `x = y` is
considered equivalent to `y = x`.

IVy constructs this graph for each negated VC. If the graph has a
cycle, Ivy reports the sequence of terms that induced the cycle (and
gives references to line numbers in the IVy program). This information
can be used to determine the source of the problem and and correct it.

As an example, consider the following formula:

    forall X. r(X,a) -> r(f(X),X)

There is a cycle `V[X] -> V[f,1] -> V[r,1] -> V[X]` induced by these terms:

    f(X)
    r(f(X),X)
    r(X,a)

The finite essentially uninterpreted fragment
=============================================

Thus far we haven't dealt with theories.  If we have symbols that are
interpreted by theories (for example, integer arithmetic) then
additional rules apply. For example, the following conditions
suffice for a formula with interpreted symbols to be in the decidable fragment:

- The relevant vocabularies are finite
- Universal variables appear only as arguments of uninterpreted symbols

This set of formulas is called *finite essentially uninterpreted*, or
FEU. As an example, this set of formulas is in the FEU fragment, 
where *f*, *g* and *h* are functions over integers:

    g(X, Y) = 0 | h(Y) = 0
    g(f(X), b) + 1 <= f(X)
    h(b) = 1
    f(a) = 0

The equality predicate on integers is also considered interpreted here.
Since *X* and *Y* occur only under uninterpreted functions *f*,*g*,*h*
(and as the reader can confirm, the relevant vocabularies are finite)
the conjunction of these formulas is in FEU.

Ivy checks this condition and will report cases of variables occurring
under interpreted operators (with one exception described in the next
section).

The finite almost interpreted fragment
======================================

We can go a little further than FEU while still requiring only finite
instantiation, allowing some use of universal variables under
arithmetic operators. We say an *arithmetic* literal is of the form `X
< Y`, `X < t`, `t < X` or `X = t` where *X* and *Y* are universal
variables and *t* is a ground term, all of integer type. We allow only
arithmetic literals that occur positively.  However, a negative
occurrence of `x < y` can be converted to `~(x = y | y < x)`, while a
negative occurrence of `x = t` can be eliminated by a method called
"destructive equality resolution".

For arithmetic literals, we add the following rule to the construction
of the relevant vocabulary graph:

| positive term          | arc(s)              |
|------------------------|---------------------|
| X < Y                  | V[X] <-> V[Y]       |
|                        |                     |

The *finite almost interpreted* fragment (FAU) consists of formulas satisfying
the following conditions:

- the relevant vocabularies are finite, and

- universal variables occur only as arguments to uninterpreted symbols
  *or* arithmetic literals

For example, the following formula is in FAU but not FEU:

    forall X. 0 <= X & X < m - 1 -> p(X)

Arithmetic literals can be useful, for example, when reasoning about
the contents of an array indexed by the integers. On the other hand, in
Ivy it is more typical to treat array indices as an uninterpreted
totally ordered type.

Definitions in verification conditions
======================================

A definition can be seen as simply an equality constraint. For
example, if we write:

    definition r(X,Y,Z) = (X = Y - Z);

this could be treated as an assumption:

    forall X,Y,X. r(X,Y,Z) <-> X = Y - Z

However, it is easily seen that such a formula will take us outside
FAU.  Instead of this, if a definition is not recursive, we can simply
unfold it. For example, suppose we have this program:

    require r(x,y,z);
    y := y + 1;
    z := z + 1;
    ensure r(x,y,z);

This gives us the following negated VC:

    forall X,Y,X. r(X,Y,Z) <-> X = Y - Z
    r(x,y,z)
    y' = y + 1
    z' = z + 1
    ~r(x,y',z')

Unfolding the definition of *r* gives us the equivalent:

    x = y - z
    y' = y + 1
    z' = z + 1
    ~(x = y' - z')

This is not only in FAU, it is actually quantifier-free.

The fragment checker
--------------------

IVy's decidable fragment consists of all the formulas that are in FAU
after full unfolding of all the non-recursive definitions.

However, Ivy's check for this is somewhat conservative. That is, since
fully unfolding all of the definitions could be exponential, Ivy
over-approximates the set of terms that might occur under an instance
of a defined symbol in a
[context-insensitive](https://en.wikipedia.org/wiki/Data-flow_analysis)
way.  This means IVy may occasionally report arcs in the relevant
vocabulary graph that would not occur if the analysis were fully
precise.

When a verification condition is not in the decidable fragment, IVy
refuses to check it, and instead produces an error message explaining
the problem. This explanation is generally in the form of a list of
terms that induce a cycle in the relevant vocabulary graph, or an
instance of an interpreted symbol applied to universal variable that
is not an arithmetic literal.

There are several approaches to correcting such a problem. For
example, we can change the encoding of the state of the system to use
relations instead of functions. Alternatively, we can use modularity
to hide a function symbol or theory that is problematic, or we can
apply proof tactics to transform the property to be proved. We will see
examples of all of these approaches in the following chapters.















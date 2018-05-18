---
layout: page
title: Decidability
---

Automated provers can substantially increase productivity in the
formal verification of complex systems. However, the unpredictability
of automated provers presents a major hurdle to usability of these
tools. To be usable in large proofs, the performance of proof
automation must be:

1) Predictable, for example not diverging on small problems,
2) Continuous, that is, not highly sensitive to small input changes, and
3) Transparent, that is, providing actionable feedback when proof fails.

These issues are particularly acute in case of provers that handle
undecidable logics, for example, first-order logic with quantifiers.

On the other hand, there is a long history of work on \emph{decidable}
logics or fragments of logics. Generally speaking, decision procedures
for these logics perform more predictably and fail more transparently
than provers for undecidable logics. In particular, in the case of a
false proof goal, they usually can provide a concrete counter-model to
help diagnose the problem.

Ivy is designed to support the the user in reducing the proof of
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

    x > 0 -> wp(y := x - 1, y < x)

That is precondition `x > 0` has to imply that after executing
`y := x - 1`, the postcondtion `y < x` holds (assuming the theory
of the natural numbers holds for type `t`).

One of the rules of the wlp calculus is this:

    wp(y := e,R) = R[e/y]

That is to get the weakest liberal procondition of *R* with respect
the the assignment `y := e`, we just subtitute *e* for *y* in *R*.
In our example above, the verification condition can therefore
be written as:

    x > 0 -> x - 1 < x

Since this formula is valid over the natural numbers, meaning it holds
true for any natural number *x*, we conclude that the program is
correct. 

In fact, we can check the validity of this formula automatically.
Technically, the way this is done is by *negating* the formula,
then passing it to an tool called an [SMT solver](???} to determine
if it is *satisfiable*. In this case, the nagated verification condition
is:

   ~(x > 0 -> x - 1 < x)

which is logically equivalent to:

   x > 0 & x - 1 >= x

We can easlity see that this is unsatisfiable, in the sense that there
is no natural number *x* that makes it true.

Moreover, a typical SMT solver can determine definitely whether this
formula is satisfiable, since it is expressed in the form of affine
constraints over the natural numbers without quantifiers. Solving
constraints of this kind is an NP-complete problem. This means that all
known solution algorithms use exponential time in the worst case,
but in practice we can almost always solve problems that have a moderate
number of variables.

More generally, a typical SMT solver can handle a theory called QFLIA,
which satands for "quantifier-free linear integer arithmetic" and
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

In Ivy's natrual number theory, we have `0 - 1 = 0`. That means that
the above formula is actually true for `x = 0`. The assignment `x = 0`
is called a *model* of the formula, that is, it describes a possible
situation in which the formula is true. That means the assignment `x =
0` is also a *conter-model* for the verification condition: it shows
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

That is, we trear `assume Q` as a statement that only terminates if
*Q* is true, and `assert Q` as a statement that only succeeds if *Q*
is true (that is, if `Q` is false, it does not even satisfy the
post-condition `true`). 

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
initializer establishes *I* and if each exported action preserves the
*I*. Thus, the verification condition for a program is that,

    wlp(init,I)

where `init` is the initializer, and, for each exported action *a*:

    I -> wlp(a,I)

Notice we haven't dealt with procedure calls here, but for present
purposes we can consider that all calls are "in-lined" when verifying
the program.

Verifaction conditions for even moderately complex programs are big
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


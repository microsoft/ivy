# The IVy language

IVy's language is designed to let you to model systems in a way that
is both convenient and conducive to automated
verification. Technically, this means that important verification
problems like invariant checking and bounded model checking fall
within a [decidable fragment][df] of first-order logic.

[df]: https://en.wikipedia.org/wiki/Bernays%E2%80%93Sch%C3%B6nfinkel_class

## State and actions

An IVy program describes objects that have state and provide actions
that operate on state. State is described using mathematical relations
and functions (much as in the [Alloy][al] language, but
with important differences that we will discuss later).

[al]: http://alloy.mit.edu

### Types and declarations

Suppose we have a network consisting of nodes, with pair-wise links
between the nodes. We can model the structure of the network with a
relation `link` like this:

    type node

    relation link(X:node,Y:node)

This says that `link` is a set of pairs (*X*,*Y*) where *X* and *Y*
are nodes. In IVy, as in [Prolog][pl], identifiers beginning with capital
letters are variables. The colon introduces a type annotation. In the
above declaration, the variables *X* and *Y* are just taking up space,
telling us what sort of relation `link` is. 

[pl]: https://en.wikipedia.org/wiki/Prolog

We can also declare a function, for example, one that gives an ID to each node:

    type id

    function node_id(X:node) : id

An individual of a given type can be declared like this:

    individual root:node

In logic, `root` would be called a *constant* (it might also be
considered a function of zero arguments). In IVy, though, since the
values of declared symbols can be mutated by actions, the term constant
could be misleading. Instead, we will refer to relations, functions and
individuals collectively as *components*.

### Enumerated types

The type `node` declared above is an *interpreted* type. This means
it can be any set with at least one element. Often it is useful to
define a type *in extension*, that is, by enumerating its elements
explicitly. An example of an enumerated type in IVy would be:

    type color = {red,green,blue}

This declares a type with exactly three values, and also declares
individuals `red`, `green` and `blue` as its elements.

### Actions

An *action* in IVy mutates components of the state. For example, here
is a declaration of an action that adds a link between two nodes:

    action connect(x:node, y:node) = {
        link(x,y) := true
    }

The action `connect` is defined in terms of one of IVy's primitive
actions: an assignment. An assignment modifies the value of a function
or relation. In this case, the single pair (*x*,*y*) is added to
`link` (or put another way, the value of the expression `link(x,y)` is
set to true, without otherwise modifying `link`). The values of all other
components remain unchanged by the assignment.

We can use variables to make larger modifications to a relation. For
example, here is an action that removes all links from a given node *x*:

    action clear(x:node) = {
        link(x,Y) := false
    }

The effect of the assignment with variable *Y* is to simultaneously
assign `link(x,Y)` for all nodes *Y*. We don't have to give a type
annotation for *Y* because it can be inferred from context.

We can be a little more selective by giving a Boolean expression in
the assignment. For example, this action removes links from *x* to all
nodes in the set `failed`:

    action clear_failed(x:node) = {
        link(x,Y) := link(x,Y) & ~failed(Y)
    }

## Control

### Sequential execution

We can execute two actions sequentially by separating them with
semicolon. For example, this action removes all links from *x*, then
links *x* to *y*:

    action connect_unique(x:node, y:node) = {
        link(x,Y) := false;
        link(x,y) := true
    }

The semicolon is a sequential composition operator in IVy, not a
statement terminator. In this case, we could have written the sequence
of assignments equivalently as:

    link(x,Y) := Y = y

### Calling actions

We could also have written `connect_unique` by *calling* `clear` and `connect`:

    action connect_unique(a:node, b:node) = {
        call clear(a);
        call connect(a,b)
    }
    
IVy uses the [call-by-value][cbv] convention. That is, when we call
`clear(a)` a local variable *x* is created during the execution of
`clear` and assigned the value *a*. This means that, as in the [C
programming language][cpl], modifying the value of *x* in `clear` would
not result in modifying the value of *a*.

[cbv]: https://en.wikipedia.org/wiki/Evaluation_strategy#Call_by_value
[cpl]: https://en.wikipedia.org/wiki/C_(programming_language)

### Conditionals

Conditionals in IVy are much as in any procedural programming
language. For example, the following code clears the incoming links to
node *y* if *y* is in the failed set:

    if failed(y) {
        link(X,y) := false
    }

The curly brackets around the assignment are required. No parentheses
are need around the condition.  A conditional can have an associated else
clause, for example:

    if failed(y) {
        link(X,y) := false
    } else {
        link(y,z) := true
    }

As in the C programming language, the "else" is associated to the
nearest "if".

### No loops

There are no looping constructs in IVy. This is because loops would
make important verification problems undecidable. Frequently,
though, we can write the *effect* of a loop in logic. For example, instead of
something like this:

    for y in type {
        link(x,y) := false
    }

we can instead write this:

    link(x,Y) := false

In other procedural languages used for formal modeling and
verification, loops must be decorated with invariants, which
essentially encode the effect of the loop into logic. Since IVy is
intended for abstract models and not implementations, we keep the
logic and dispense with the loop (IVy might in the future
support refinement to implementations).


## Non-deterministic choice

The asterisk "*" can be used to represent non-deterministic choice in IVy in
two situations. First, on the right-hand side of an assignment:

    x := *

This cause *x* to be assigned non-deterministically to any value of its type.
We can use variables in non-deterministic assignments, so for example:

    link(x,Y) := *

causes *x* to be linked to an arbitrary set of nodes.

Further, we can use asterisk in a conditional to create a non-deterministic branch:

    if * {
        link(x,y) := true
    } else {
        link(x,z) := true
    }

Non-deterministic choice also occurs when we create a local variable (see below).

## Expressions

Expressions in IVy are terms or formulas in [first-order logic][fol] with
equality. IVy provides the following built-in operators: `~` (not),
`&` (and), `|` (or), `->` (implies), `<->` (iff) and `=`
(equality). The equality operator binds most strongly, followed by
not, and, iff, implies.

[fol]: https://en.wikipedia.org/wiki/First-order_logic

Expressions may also use logical quantifiers. For example, this formula says that
there exists a node *X* such that for every node *Y*, *X* is linked to *Y*:

    exists X. forall Y. link(X,Y)

In this case, the variables do not need type annotations, since we can infer that
both *X* and *Y* are nodes. However, in some cases, annotations are needed. For example,
this is a statement of the transitivity of equality:

    forall X,Y,Z. X=Y & Y=Z -> X=Y

We can determine from this expression that *X*, *Y* and *Z* must all
be of the same type, but not what that type is. This means we have to
annotate at least one variable, like this:

    forall X:node,Y,Z. X=Y & Y=Z -> X=Y

## Assume, assert and init

The primitive actions `assume` and `assert` allow us to write
specifications. The `assert` action fails if the associated condition
is false. For example, suppose we wish the `connect` action to handle
only the case where the node *y* is not in the failed set. We could
write

    action connect(x:node, y:node) = {
        assert ~failed(y);
        link(x,y) := true
    }

If the condition `~failed(y)` is true, control passes through the
`assert` and this action behaves in the same way as the original.  If
the condition `~failed(y)` is false, however, the semantics of
`assert` is undefined.  This means that whenever we use `connect` we
must prove that the *y* argument is not in the failed set.

On the other hand, the `assume` action does not allow control to pass
through if the associated condition is false. A typical application of
`assume` in modeling a protocol is to implement a guarded command. For
example, this action non-deterministically chooses a non-failed node
and connects *x* to it:

    action connect_non_failed(x:node) = {
        y := *;
        assume ~failed(y);
        link(x,y) := true
    }

Of course, if all the nodes are failed, this action cannot
terminate. There is some degree of risk in using assumptions when
modeling, since assumptions can eliminate behaviors in unexpected
ways.

In `assert` and `assume` actions, any [free variables][fv] are treated
as universally quantified. For example, if we want to connect *x* to a
node that is not currently linked to any node, we could change the
assumption above to

     assume ~link(y,Z)

[fv]: https://en.wikipedia.org/wiki/Free_variables_and_bound_variables

Normally, we expect a system to start in some well-defined state, or
at least for some specified conditions to hold initially. In IVy, we use an
`init` declaration for this purpose. For example:

    init ~link(X,Y)

This says that initially, no two nodes are linked. As in `assume` and
`assert`, unbound variables are universal.


## Local variables

The above example of a guarded command action assumes that *y* is a
declared component of type `node`. We can also declare *y* locally,
however, like this:

    action connect_non_failed(x:node) = {
        local y:node {
            y := *;
            assume ~failed(y);
            link(x,y) := true
        }
    }

This creates a fresh *y* that is in scope only within the 'local'
declaration. In fact, we don't need the non-deterministic assignment
to *y* since the value of *y* is already non-deterministic at the
beginning of the `local` action.

## Axioms and background theories

The built-in types and operators provided by IVy are fairly
impoverished. We have only uninterpreted types, enumerated types and
the basic operators of first-order logic. This is by design. By
introducing richer data types, or *theories*, we would quickly make
our verification problems undecidable, meaning we would sacrifice
reliability of automated verification. In practice, before
introducing, say, the integers into a model, we should make sure that
the power of the integers is really needed. It may be, for example,
that all we require is a totally ordered set.

IVy allows us to introduce background theories in the form of logical
axioms. This in turn allows us to avoid using unnecessarily powerful
theories. As an example, consider defining an ordering relation over 
our node ID's:

    relation (I:id < J:id)

This is an example of an *infix* symbol. The symbol `<` is no
different than other relational symbols, except that IVy pre-defines
it as having infix syntax. 

We can ensure that `<` is a total order by writing axioms:

    axiom X:id < Y & Y < Z -> X < Z
    axiom ~(X:id < X)
    axiom X:id < Y | X = Y | Y < X

These axioms say, respectively, that `<` is [transitive][tr], [anti-symmetric][as]
and [total][to]. As in other cases, the free variables are universally
quantified. You may also notice that we annotated the variable *X*
with its type.  This has to do with the fact that `<` is polymorphic,
an issue we will deal with shortly.

Of course, axioms are assumptions and assumptions are dangerous.  We
want to make sure that our axioms are consistent, that is, that they
have at least one [model][mo]. The Ivy tool can be helpful in
determining this.

### Polymorphic operators.

In IVy the equality operator is *polymorphic* in the sense that it
applies to any pair of arguments so long as they are of the same
type. One way to think of this is that there is really a distinct
equality operator pre-declared for each type, but that we use `=` as a
short-hand for all of them. It is useful to be able to declare other
such polymorphic operators to avoid, for example, having to invent a
new "less than" symbol for every ordered type, or adding type
annotations to operators. 

IVy provides for this in a limited way. Certain symbols, such as `<`
and `+` are always polymorphic. This allows us to declare relations
with the same symbol over different sorts and to disambiguate them
based on type inference. Unlike built-in equality, however, these
relations must still be declared explicitly. So we might write:

    relation (X:id < Y:id)
    relation (X:length < Y:length)

These are two distinct relations and might obey different axioms.  To
make type inference stronger, the operators also come with type
constraints. In functional language terms, `<` has type `alpha * alpha
-> bool` and `+` has type `alpha * alpha -> alpha`. 

The language might be extended in the future to allow user-defined
polymorphic symbols.

## Concurrency

IVy is intended for modeling concurrent systems, such as network
protocols and distributed services. However, there is no explicit
model of concurrency in the IVy language. Instead concurrency is
modeled by interleaving guarded commands.

An IVy program exports a set of actions to its environment. Each of
these actions can be used to model a single atomic step of a process
in system of concurrent processes, or perhaps a single step of a
non-deterministically chosen process. Since the environment is allowed
to call these action arbitrarily, the IVy program can be used to model
arbitrary interleaving of atomic actions.

There is one important caveat in this approach, however: IVy actions
are atomic.  This means that it is not possible for the execution of
action to preempt another.  Because there is no "preemption" in IVy,
there is no reasonable way to model threaded programs with shared
memory in IVy. This is by design, since the language is intended for
modeling distributed protocols at a level of abstraction that hides
low-level concurrency control mechanisms.



## Modules

## Invariants


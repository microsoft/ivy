---
layout: page
title: The IVy language
---

IVy's language is designed to let you to specify and implement systems
in a way that is both convenient and conducive to automated
verification. Technically, this means that important verification
problems like invariant checking and bounded model checking fall
within a [decidable fragment][df] of first-order logic.

[df]: https://en.wikipedia.org/wiki/Bernays%E2%80%93Sch%C3%B6nfinkel_class

For this reason, the IVy language has certain unusual features. IVy
divides the world into three categories of things:

- Data values,
- Function values and
- Procedures.

Data values are the kinds of things that can be printed out, stored in
files, transmitted over the internet and so on. These are sometimes
refered to as POD types for "plain old data". Function values are pure
mathematical functions. They can be evaluated on arguments to produce
deterministic results, and they have no side effects. In other words,
evaluating a function does not modify the value of any variable. On
the other hand, a procedure, when called, has an *effect*. In addition
to returning values, it may also modify the values of variables.

Data values and function values can be stored in variables and passed
as arguments. That is, data and functions are "first class" values. On
the other hand, procedures cannot be stored in variables or passed as
arguments.

A particularly unusual aspect of the IVy langauge is that there are
*no references*. Two distinct variables are never "aliases" for the
same underlying "object". Modifying variable `a` never has an effect
on the value of variable `b`. IVy's philosphy is that references are a
low-level optimization that should be used by compilers to avoid
copying, but should never appear in high-level programs. The absense
of aliases enormously simplifies the analysis, testing and
verification of programs.

Another unusual aspect of the IVy language is that it is *synchronous*. This means that:

- All actions occur in reaction to input from the environment, and
- all actions are *isolated*, that is, they appear to occur
instantantaneously, with no interruption.

This aspect of IVy's semantics greatly simplifies reasoning about
concurrent and distributed systems.

We will now consider the basic elements of an IVy program.

## The language specifier

Every IVy file begins with a line like the following:

    #lang ivy1.5

This tells IVy what version of the language we are using.

## State and actions

An IVy program describes *objects* that have state variables and
provide *actions* that operate on state. State variables may hold
either plain old data or mathematical relations and functions (much as
in the [Alloy][al] language, but with important differences that we
will discuss later).

[al]: http://alloy.mit.edu

### Types and declarations <a name="declarations"></a>

Suppose we have a network consisting of nodes, with pair-wise links
between the nodes. We can model the structure of the network with a
relation `link` like this:

    type node

    relation link(X:node,Y:node)

This says that `node` is a POD type, but tells us nothing yet about
how values of type `node` are represented. At this point, we say that
`node` is an *uninterpreted* type. Further, we declared 
that `link` is a set of pairs (*X*,*Y*) where *X* and *Y*
are nodes.

In IVy, as in [Prolog][pl], identifiers beginning with capital letters
are logical variables, or place-holders. These are not to be confused
with program variables, which hold the program state.  The colons
introduce type annotations. In the above declaration, the variables
*X* and *Y* are just taking up space, telling us what sort of relation
`link` is (that is, for every *X* and *Y* of type `node`, `link(X,Y)`
is a Boolean value.

[pl]: https://en.wikipedia.org/wiki/Prolog

We could equivalently have written the relation declaration as:

    function link(X:node,Y:node) : bool

Either way, we create a variable `link` that holds a function value, in particular
a function from pairs of `node` to `bool`.

As another example, here is a declaration of a function that gives an
ID to each node:

    type id

    function node_id(X:node) : id

A variable that holds just a node value can be declared like this:

    individual root:node


### Enumerated types

The type `node` declared above is an *uninterpreted* type. This means
it can be any set with at least one element. Often it is useful to
define a type *in extension*, that is, by enumerating its elements
explicitly. An example of an enumerated type in IVy would be:

    type color = {red,green,blue}

This declares a type with exactly three distinct values, and also declares
individuals `red`, `green` and `blue` as its elements.

### Actions

An *action* in IVy mutates the values of state variables. For example,
here is a declaration of an action that adds a link between two nodes:

    action connect(x:node, y:node) = {
        link(x,y) := true
    }

The action `connect` is defined in terms of one of IVy's primitive
actions: an assignment. An assignment modifies the value of a
variable.  In this case, the single pair (*x*,*y*) is added to the
relation `link` (or put another way, the value of the expression
`link(x,y)` is set to true, without otherwise modifying
`link`). Because there is no aliasing in IVy.  the values of all other
variables remain unchanged by the assignment.

We can use place-holders to make larger modifications to a relation. For
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

If there are no parameters, we don't use parentheses. For example:

    action flip = {
        bit := ~bit
    }

In fact, you will never see a pair of empty parentheses in IVY. An action can also have return parameters. For example:

    action swap(a:t,b:t) returns (c:t,d:t) = {
        c := b;
        d := a
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
statement terminator. However, an extra semicolon is allowed before an
ending brace `}` to make editing sequences of statements easier. In
this case, we could have written the sequence of two assignments
equivalently as:

    link(x,Y) := Y = y

### Calling actions

We could also have written `connect_unique` by *calling* `clear` and `connect`:

    action connect_unique(a:node, b:node) = {
        call clear(a);
        call connect(a,b)
    }
    
Since there are no references in IVy, so in effect, IVy uses the
[call-by-value][cbv] convention. That is, when we call `clear(a)` a
local variable *x* is created during the execution of `clear` and
assigned the value *a*. This means that, as in the [C programming
language][cpl], modifying the value of *x* in `clear` would not result
in modifying the value of *a* in `connect_unique`.

[cbv]: https://en.wikipedia.org/wiki/Evaluation_strategy#Call_by_value
[cpl]: https://en.wikipedia.org/wiki/C_(programming_language)

The return values of an action can be obtained like this:

    call x,y := swap(x,y)

An action with a single return value can be called within an expression.
For example, if `sqrt` is an action, then:

    x := y + sqrt(z)

is equivalent to

    call temp := sqrt(z)
    x := y + temp

If there is more than call within an expression, the calls are
executed in left-to-right order.

Parentheses are not used when calling an action with no parameters. 
For example, if we have:

    action next returns (val:t) = {
        current := current + 1;
        val := current
    }

then we would write:

    x := y + next

The lack of paretheses introduces no ambiguity, since the action
`next` is not a value and cannot itself be passed as an argument to
the function `+`. An advantage of this convetion is that we don't have
to remember whether `next` is an action or a variable, and we can
easily replace a variable by an action without modifying all references
to the variable.

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

The following syntax can be used to find a element of a type that
satisfies some condition:

    if some x:t. f(x) = y {
        z := x + y
    }
    else {
        z := y
    }        

Here, if there is any value `x` of type `t` such that `f(x) = y`, then
such a value is assigned to `x` and the assignment `z := x + y` is
executed. If there is more than one such value, the choice is
non-deterministic. If there is no such value, the `else` clause is
executed. The symbol `x` is only in scope in the `if` clause. It acts
like a local variable and is distinct from any `x` declared in an
outer scope. 

It is also possible to choose a value of `x` minimizing some function
of `x`. For example, we can find an element of a set `s` with the least key like this:

    if some x:t. s(x) minimizing key(x) {
       ...
    }

This is logically equivalent to the following:

    if some x:t. s(x) & ~exists Y. s(Y) & key(Y) < key(x) {
       ...
    }

Besides being more concise, the `minimizing` syntax can be more
efficiently compiled and is easier for Ivy to reason about (see the
[decidability](decidability.html) discussion). The keyword
`maximizing` produces the same result with the direction of `<` reversed.


### Loops

Loops are discouraged IVy. Often, the effect of a loop can be
described using an assignment or an `if some` conditional. 

For example, instead of something like this:

    for y in type {
        link(x,y) := false
    }

we can instead write this:

    link(x,Y) := false

When a loop is needed, it can be written like this:

    sum := 0;
    i := x;
    while i > 0
    {
        sum := sum + f(i);
	i := i - 1
    }

This loop computes the sum of `f(i)` for `i` in the range `(0,x]`.
A loop can be decorated with a invariants, like this:

    while i > 0
    invariant sum >= 0
    {
        sum := sum + f(i);
	i := i - 1
    }

The invariant `sum >= 0` is a special assertion that is applied
on each loop iteration, before the evaluation of the condition.
Invariants are helpful in proving properties of programs with loops.


## Non-deterministic choice

The asterisk "*" can be used to represent non-deterministic choice in IVy in
two situations. First, on the right-hand side of an assignment:

    x := *

This cause *x* to be assigned non-deterministically to any value of its type.
We can use variables in non-deterministic assignments, so for example:

    link(x,Y) := *

causes *x* to be linked to an arbitrary set of nodes.

Further, we can use an asterisk in a conditional to create a
non-deterministic branch:

    if * {
        link(x,y) := true
    } else {
        link(x,z) := true
    }

Non-deterministic choice also occurs when we create a local variable (see below).
On entry to an action the values of return parameters are non-deterministically chosen.

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

## Modelling interleaving concurrency in IVy

Actions in an IVy program execute only in response to calls from the
program's environment. IVy makes the synchronous hypothesis: when the
environment calls an action, it waits for the action to complete
before issuing another call. Put another way, IVy actions appear to
execute in zero time. At first blush, it might seem that this
eliminates the possiblity of concurrency. In fact, the synchronous
hypothesis is intended to make the implementation of concurrent and
distributed systems simpler. The key idea is that only the
*appearance* of synchronicity is required. In practice actions can
execute concurrently, provided that to an outside observer they appear
to have executed sequentially.

For now, we will leave aside the question of how to enforce the
synchronous hypothesis in practice. Instead, we will consider how to
use the synchronous IVY language to model a distributed protocol at an
abstract level using *interleaving* concurrency. In an interleaving
model, processes take turns executing actions in isolation (that is,
in apparently zero time) in a non-deterministic order. 

An IVy program exports a set of actions to its environment. Each of
these actions can be used to model a single isolated step of a
process.  Since the environment is allowed to call these actions in an
arbitrary order, the IVy program can be used to model arbitrary
interleaving of process actions.


### An abstract interface model

The following is a very abstract model of an interface that establishes
connections between clients and servers. Each server has a semaphore
that is used to guarantee that at any time at most one client can be
connected to the server.

    #lang ivy1.5

    type client
    type server

    relation link(X:client, Y:server)
    relation semaphore(X:server)

    init semaphore(W) & ~link(X,Y)

    action connect(x:client,y:server) = {
      assume semaphore(y);
      link(x,y) := true;
      semaphore(y) := false
    }

    action disconnect(x:client,y:server) = {
      assume link(x,y);
      link(x,y) := false;
      semaphore(y) := true
    }

    export connect
    export disconnect

This program declares two types `client` and `server`. The state of
the protocol model consists of two relations. The relation `link`
tells us which clients are connected to which servers, while
`semaphore` tells us which servers have their semaphore "up".  The
`link` and `semaphore` components aren't "real". They are abstractions
that represent the interface user's view of the system.

The program exports two actions to the environment: `connect` and
`disconnect`. The `connect` actions creates a link from client `x` to
server `y`, putting the server's semaphore down. Notice that `connect`
assumes the server's semaphore is initially up. The `disconnect`
action removes a link and puts the semaphore up. The two `export`
declarations at the end tell us that the environment may call
`connect` and `disconnect` in arbitrary sequence, though it must obey
the stated assumptions.

## Safety and invariant conjectures

A program is *safe* if the environment cannot call it in any way that
causes an assertion to be false. There are various ways to use
assertions to specify desired safety properties of a program. A simple
one is to add a test action that asserts some property of the program
state. In the client/server example above, we might specify that no
two distinct clients can be connected to a single server using the
following test action:

    action test = {
      assert ~(X ~= Z & link(X,Y) & link(Z,Y))
    }

    export test

The assertion is implicitly universally quantified over (distinct)
clients `X` and `Z` and server `Y`. To help IVy to prove that this
assertion always holds, we can suggest facts that might be useful in
constructing an inductive invariant. For example:

    conjecture X = Z | ~link(X,Y) | ~link(Z,Y)
    conjecture link(X,Y) -> ~semaphore(Y)

Here, we state that no two clients are connected to the same server
(which is just the property we want to prove) and additionally that
when a client is connected to a server, its semaphore is down. These
facts are *inductive* in the sense that they are initially true, and
each of our three actions preserves them. Moreover, they are
sufficient to guarantee that our test assertion is true. Thus, IVy can
use these conjectures to prove safety of the program.

While we can give IVy conjectured invariants, there is no way outside
of an action to *assert* that a proposition is invariant. This is to
avoid ambiguity as to exactly *when* an invariant should be
established. In IVy we can only state that a formula is true at a
specific point in the execution of an action.

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

These axioms say, respectively, that `<` is
[transitive](https://en.wikipedia.org/wiki/Transitive_relation),
[anti-symmetric](https://en.wikipedia.org/wiki/Antisymmetric_relation)
and [total](https://en.wikipedia.org/wiki/Total_relation). As in other
cases, the free variables are universally quantified. You may also
notice that we annotated the variable *X* with its type.  This has to
do with the fact that `<` is *polymorphic*, an issue we will deal with
shortly.

Of course, axioms are assumptions and assumptions are dangerous.  We
want to make sure that our axioms are consistent, that is, that they
have at least one [model](https://en.wikipedia.org/wiki/Logic_model). The IVy tool can be helpful in
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
based on type inference.

To make type inference stronger, the polymorphic operators also come
with type constraints. In functional language terms, `<` has type
`alpha * alpha -> bool` and `+` has type `alpha * alpha -> alpha`.

### Numerals

Numerals are a special case of polymorphic symbols. A numeral is any
symbol beginning with a digit, for example `0`, or `0xdeadbeef`. The
types of numerals are inferred from context. For example, if `x` has
type `foo`, then in the expression `x+1`, the numeral `1` is inferred
to have type `foo`.

Numerals are special symbols in the sense that they do not have to be
explicitly declared. However, IVy gives them no special
interpretation. IVy does not even assume that distinct numerals have
distinct values. This means that `0 = 2` is not necessarily false.  In
fact, this equation might be true in a type representing the integers
mod 2.

Section [Interpretations] describes how to give concrete
interpretations to IVy types, so that symbols like `+` and `0` have
specific meanings.

### Quoted symbols

A quoted symbols a possibly-empty sequence of characters enclosed in
double quote characters (and not containing a double quote character).
An example would be `"ab$c"`. Quoted symbols are similar to numerals:
their type is inferred from context. 

## Modules

A *module* in IVy is a group of declarations that can be instantiated.
In this way it is similar to a template class in an object-oriented
programming language. Besides defining classes of objects, modules can be
used to capture a re-usable theory, or structure a modular proof.

Here is a simple example of a module representing an up/down counter
with a test for zero:

    module counter(t) = {

        individual val : t
        init val = 0

        action up = {
            val := val + 1
        }

        action down = {
            val := val - 1
        }

        action is_zero returns(z : bool) = {
            z := (val = 0)
        }
    }

This module takes a single parameter `t` which is the type of the
counter value `val`. We can create an instance of the module like this:

     type foo

     instance c : counter(foo)

This creates an *object* `c` with members `c.val`, `c.up`, `c.down`
and `c.is_zero`. 

Any IVy declaration can be contained in a module. This includes
axioms, conjectures, instances and modules. As an example, here is a
module representing a theory of partial orders:

    module po(t,lt) = {
        axiom lt(X:t,Y) & lt(Y,Z) -> lt(X,Z)
        axiom ~(lt(X:t,Y) & lt(Y,X))
    }

This module takes a type `t` and a relation `lt` over `t`. It provides
axioms stating that `lt` is transitive and antisymmetric. We might instantiate it
like this:

    type foo

    instantiate po(foo,<)

Since we didn't give an object name, the members of `po` are created
within the current object (which in this case is the global
object). Notice that we passed the polymorphic infix symbol `<` as a
parameter. Any symbol representing a type, function, relation, action
or object can be passed as a module parameter.

Like a class in an object-oriented programming language, a module can
contain references to symbols declared outside the module. However, a
declaration inside the module takes precedence. For example, consider this
code:

    relation r,s

    module m = {
        relation r
        axiom s -> r
    }

    instance c : m

The axiom in `c` is equivalent to:

    axiom s -> c.r

That is, the local declaration of `r` shadows the global one.

### Singleton objects

We can create a module with just one instance like this:

    object foo = {
        relation bit
        init ~bit
        action flip = {
            bit := ~bit
        }
    }

This creates a single object `foo` with members `foo.bit` and
`foo.flip`, exactly as if we had created a module and instantiated it
once.

### Parameterized objects

An array of instances of the same module can be created like this:

    type foo
    type bar

    instance c(X:bar) : counter(foo)

This creates one instance `c(X)` of module `counter` for for every
element of type `bar`. Since we haven't said how many elements there
are in type `bar`, we have effectively created a collection of objects
of arbitrary but fixed size.

If `x` is of type `bar`, we can treat `c(x)` as we would any object,
for example:

    call c(x).down;
    if c(x).is_zero {
        call c(x).up
    }

The parameter `X` can also be passed to the module being instantiated.
This is useful to create a collection of objects with unique identifiers.
For example:

    type id_t

    module thing(id) = {
       action my_id returns (x:id_t) = {
            x := id
       }
    }

    instance c(X:id_t) : thing(X)

In this case, calling `c(id).my_id` will return `id`.

An alternative way to write the above would be:

    type id_t

    object c(id:id_t) = {
       action my_id returns (x:id_t) = {
            x := id
       }
    }

Notice that the object parameter is given as a logical constant rather
than a place-holder. This constant can be referred to in the body of the
object.

Types in IVy are never parameterized. For example, if we write:

    object foo(self:t) = {
        type t
    }

this creates a single type called `foo.t`, not a collection of types
`foo.t(self)` for all values of `self`.

## Monitors

While embedding assertions in code is a useful way to write
specifications, there are good reasons to separate a specification
from the object being specified. For example, this allows you to
re-use specifications, to construct modular proofs and to refine
specifications into implementations.


The IVy language supports these goals using *monitors*. A monitor is
an ordinary object, except that its actions are synchronized with the
actions of other objects. For example, suppose that in the
client/server example above, we want to specify that callers to
`connect` do not request a connection to a server whose semaphore is
down. We could express this property as a monitor like this:

    object mon = {
        action pre_connect(x:client,y:server) = {
            assert semaphore(y)
        }        
        execute pre_connect before connect
    }

The `execute` declaration says that whenever `connect` is called,
action `pre_connect` should be executed first, with the same
parameters. If any caller tries to connect a client to a busy server,
the assertion will fail.

Monitors can also check the return values of actions. For example:

    action post_incr(inp:t) returns(out:t) = {
        assert inp < out
    }

    execute post_incr after incr

Here, we have an action `incr` that is supposed to increment a value,
and we specify that the output must be greater than the input.

As a shorthand, we can write out monitor action like this:

    after c.post(inp:t) returns(out:t) {
        assert inp < out
    }

This creates a monitor action called `post.after` that is executed after `c.post`.
Similarly, we can write:

    before connect(x:client,y:server) {
        assert semaphore(y)
    }        

If we drop the input or output parameters, they are inherited from the monitored action.
For example:

    after c.post {
        assert inp < out
    }

This is a useful shorthand when the declaration of `c.post` is nearby,
but should probably be avoided otherwise.

### Monitor state

Usually, monitors contain state components that allow them to remember
some of the history of past events. For example, here is a monitor specifying a 
property of `counter` objects. It requires that immediately after a call to `up`,
the `is_zero` action cannot return true:

    module counter_prop(c) = {

        relation was_up
        init ~was_up 

        after c.up {
            was_up := true
        }

        after c.down {
            was_up := false
        }

        after c.is_zero returns (z:bool) {
            assert was_up -> ~z
        }
    }

This module is parameterized on `c`, the counter being specified. This
makes the specification re-usable. It has a single state component
`was_up` that remembers whether the last counting action was
`up`. This is accomplished by the actions `up` and `down` that
synchronize with actions of counter `c` (in this case it doesn't make
any difference whether it is before or after). The action `is_zero`
executes after calls for the counter's `is_zero` action and asserts a
fact about the return value: if the last action was `up` the result
cannot be true. 


## Assume/guarantee reasoning

IVy doesn't require us to prove all at once that a program is safe.
Instead, we can break the proof down into smaller proofs using the
*assume/guarantee* approach. 

For example, suppose we have the following program with two objects:

    #lang ivy1.5

    type nat

    relation even(N:nat), odd(N:nat)
    axiom even(0) & (even(N) -> odd(N+1))
    axiom odd(1) & (odd(N) -> even(N+1))

    object evens = {
        individual number : nat
        init nat = 0

        action step = {
            call odds.put(number + 1)
        }

        action put(n:nat) = {
            number := n;
        }
    }

    object odds = {
        individual number : nat
        init nat = 1

        action step = {
            call evens.put(number + 1)
        }

        action put(n:nat) = {
            number := n;
        }
    }

    export evens.step
    export odds.step

Each object stores a number when its `put` action is called and sends this number plus one to the
other object when its `step` action is called by the environment. We want to
prove that `even.put` only receives even numbers, while `odd.put` only receives
odd numbers. Here is a specification of this property as a monitor:

    object spec = {

        before even.put {
            assert even(n)
        }

        before odd.put = {
            assert odd(n)
        }
    }

We would like to break the proof that these two assertions always hold
into two parts. In the first part, we assume the object `evens` gets
correct inputs and prove that it always produces correct outputs. In
the second part, we assume the object `odds` gets correct inputs and
prove that it always produces correct outputs.

This argument seems circular on the surface. It isn't, though, because
when we prove one of the assertion holds, we are only assuming that
the other assertions has always held *in the past*. So what we're
really proving is that neither of the two objects is the first to
break the rules, and so the rules always hold.

IVy calls the two parts of the proof *isolates*. They are declared like this:

    isolate iso_even = evens with spec
    isolate iso_odd = odds with spec

In the first isolate, we prove the assertion that `evens`
guarantees. We do this in context of the `spec` object, but we forget
about the state of the `odds` object. What this means is that in isolate `iso_even`,
the `assert` statement in `even.put` becomes an `assume` statement.

The result is as if we had actually entered the following program:

    #lang ivy1.5

    type nat
    function (X:nat + Y:nat) := nat

    relation even(N:nat), odd(N:nat)
    axiom even(0) & (even(N) -> odd(N+1))
    axiom odd(1) & (odd(N) -> even(N+1))

    object evens = {
        individual number : nat
        init nat = 0

        action step = {
            call odds.put(number + 1)
        }

        action put(n:nat) = {
            assume even(nat)
            number := n;
        }
    }

    object odds = {

        action put(n:nat) = {
            assert odd(nat)
        }
    }

    export evens.step
    export evens.put

In isolate `iso_even`, the `odds` object acts like part of the
environment. The side effect of `odds.put` has been eliminated, and
what remains is just the assertion that the input value is odd (IVy
has to verify that this side effect is in fact invisible to
`evens`). The assertion that inputs to `evens` are even has become as
assumption. We can prove this isolate is safe by showing that
`even.number` is invariantly even, which means that `odds.put` is
always called with an odd number.

The other isolate, `iso_odd` looks like this:

    #lang ivy1.5

    type nat
    function (X:nat + Y:nat) := nat

    relation even(N:nat), odd(N:nat)
    axiom even(0) & (even(N) -> odd(N+1))
    axiom odd(1) & (odd(N) -> even(N+1))

    object evens = {

        action put(n:nat) = {
            assert even(nat)
        }
    }

    object odds = {
        individual number : nat
        init nat = 1

        action step = {
            call evens.put(number + 1)
        }

        action put(n:nat) = {
            assume odd(nat)
            number := n;
        }
    }

    export odds.step
    export odds.put


If both of these isolates are safe, then we know that neither
assertion in `spec` is the first to fail, so the original program is
safe.

IVy has default rules for determining, for each object, which
assertions are assumptions and which assertions are guarantees.

The assumptions are:

- Monitor assertions executed *before* the object's actions
- Monitor assertions executed *after* the object's calls

The guarantees are:

- Assertions within the object's actions
- Monitor assertions executed *after* the object's actions
- Monitor assertions executed *before* the object's calls

Roughly speaking, this means that assertions about an object's inputs
are assumptions for that object, while assertions about its outputs
are guarantees.

## Action implementations

Often it is useful to separate the declaration of an action from
its implementation. We can declare an action like this:

    action incr(x:t) returns(y:t)

and then give its implementation like this:

    implement incr {
        y := x + 1
    }

This is useful for defining and specifying interfaces. For example,
we could define the interface between "evens" and "odds" like this:

    object intf = {
    
        action put_even(n:nat)
        action put_odd(n:nat)

        object spec = {

            before put_even {
                assert even(n)
            }

            before put_odd = {
                assert odd(n)
            }
        }
    }

The `even` object would then be:

    object evens = {
        individual number : nat
        init nat = 0

        action step = {
            call intf.put_odd(number + 1)
        }

        implement intf.put_even(n:nat) = {
            number := n;
        }
    }

In this way, we can make the interface specification into a re-usable
component.


## Initializers

In some cases it is awkward to give the initial condition as a
formula. An alternative is to use an initializer. This is a special
action that is executed once initially, before any exported actions
are called. For example:

    individual bit : bool

    after init {
        bit := false
    }

This behaves like a monitor after a special internal action called
`init`. As the `after` implies, the initial condition prescribed by
the `init` declarations is assumed to be established before any
initializers are called. Initializers are executed in the order they
are declared.

Initializers may call other actions. For example, suppose we have a
module `collection` representing a set of objects that is initially
empty.  If we wanted a set that initially contained the value zero, we
could use an initializer like this:

    type t

    object foo = {
        instance myset : collection(t)

        after init {
            call myset.add(0)
        }
    }

This action is called exactly once after `myset` is initialized.

Parameterized objects can also have initializers. For example, we may
want to have a collection of objects that each contain a bit, where initially
only the bit of object 0 is true:

    type t

    object foo(self:t) = {
        individual bit : bool

        after init {
            bit := (self = 0)
        }
    }

There are some restrictions in initializers of parameterized objects,
however. These are:

- Conditions of `if` statements may not refer to the parameter, and

- In assignments, the left-hand side must contain the parameter if the right-hand side does.

For example, this initializer would not be legal:

    type t

    individual bit : bool

    object foo(self:t) = {
        after init {
            bit := (self = 0)
        }
    }

This is because the component `bit` being assigned is not
parameterized.  This means it is in effect being assigned a different
value for each value of `self`.  The restrictions guarantee that the
result of the initializer does not depend on the order in which it is
called for different parameter values.

## Definitions

We can define the value of a previously declared function like this:

    function square(X:t):t

    definition square(X) = X * X

Notice we don't have to give the type of X in the definition, since it
can be inferred from the type of `square`. Logically, the definition
is equivalent to writing:

    axiom square(X) = X * X

However, definitions have several advantages. Primarily, they are safer,
since definitions are guaranteed to be consistent. In addition they can be
computed. If we use an axiom, the only way that Ivy can compile the
function `square` is to compile a table of squares. On the other hand,
IVy can compile the definition of `square` into a procedure. 

IVy doesn't (currently) allow recursive definitions. So, for example,
this is not allowed:

    definition factorial(X) = X * factorial(X-1) if X > 0 else 1

### Macro definitions

A macro is a definition that is only "unfolded" when it is used.  For
example, let's say we want to define a predicate `rng` that is true of
all the elements in range of function `f`. We could write it like
this:

    definition rng(X) = exists Y. f(Y) = X

The corresponding axiom might be problematic, however. Writing it out
with explicit quantifiers, we have:

    axiom forall X. (rng(X) <-> exists Y. f(Y) = X)

This formula has an alternation of quantifiers that might result in
verification conditions that IVy can't decide (see the
[decidability](decidability.html) discussion). Suppose though, that we only need
to know the truth value of `rng` for some specific arguments. We can instead
write the definition like this:

    definition rng(x:t) = exists Y. f(Y) = x

Notice that the argument of `rng` is a constant `x`, not a place-holder
`X`. This definition acts like a macro (or an axiom *schema*) that can be
instantiated for specific values of `x`. So, for example, if we have an assertion
to prove like this:

    assert rng(y)

Ivy will instantiate the definition like this:

    axiom rng(y) <-> exists Y. f(Y) = y

In fact, all instances of the macro will be alternation-free, since
IVy guarantees to instantiate the macro using only ground terms for
the constant arguments.  A macro can have both variables and constants
as arguments. For example, consider this definition:

    definition g(x,Y) = x < Y & exists Z. Z < x

Given a term `g(f(a),b)`, Ivy will instantiate this macro as:

    axiom g(f(a),Y) = f(a) < Y & exists Z. Z < f(a)

### Choice functions

Suppose we want to define a function `finv` that is
the inverse of function `f`. We can write the definition like this:

    definition finv(X) = some Y. f(Y) = X in Y

This special form of definition says that `finv(X)` is `Y` for *some*
`Y` such that `f(Y) = X`. If there is no such `Y`, `finv(X)` is left
undefined. The corresponding axiom is:

    axiom forall X. ((exists Y. f(Y) = X) -> f(finv(X)) = X)

With this definition, `finv` is a function, but it isn't fully
specified.  If a given element `Y` has two inverses, `finv` will yield
one of them. This isn't a non-deterministic choice, however. Since `f`
is a function, it will always yield the *same* inverse of any given
value `Y`.

If we want to specify the value of `finv` in case there is no inverse,
we can write the definition like this:

    definition finv(X) = some Y. f(Y) = X in Y else 0

The `else` part gives us this additional axiom:

    axiom forall X. ((~exists Y. f(Y) = X) -> finv(X) = 0)

Notice that this axiom contains a quantifier alternation. If this
is a problem, we could use a macro instead:

    definition finv(x) = some Y. f(Y) = x in Y else 0

The axiom we get is

    axiom (~exists Y. f(Y) = x) -> finv(x) = 0)

which is alternation-free.

## Interpreted types and theories

The normal way of using IVy is to declare uninterpreted types and to
give the necessary axioms over those types to prove desired properties
of a system. However, it is also possible in IVy to associate types
with sorts that are interpreted in the underlying theorem prover. 

For example:

    type idx

    interpret idx -> int

This says that IVy type `idx` should be interpreted using sort `int`
of the theorem prover. This does not mean that `idx` is equated with
the integers. If we also interpret type `num` with `int`, we still
cannot compare values of type `idx` and type `num`. In effect, these
two types are treated as distinct copies of the integers.

When we declare `idx` as `int`, certain polymorphic functions and
relations on `idx` are also automatically interpreted by the
corresponding operators on integers, as are numerals of that
type. So, for example, `+` is interpreted as addition and `<` as
'less than' in the theory of integers. Numerals are given their normal
interpretations in the theory, so `0:idx = 1:idx` would be false.

Concrete sorts that are currently available for interpreting IVy types
are:

- int: the integers
- {*X*..*Y*}: the subrange of integers from *X* to *Y* inclusive
- {*a*,*b*,*c*}: an enumerated type
- bv[*N*]: bit vectors of length *N*, where *N* > 0

An arbitrary function or relation symbol can be interpreted. This is useful
for symbols of the theory that have no pre-defined polymorphic symbol in IVy.
For example:

    type t
    type s
    function extract_lo(X:t) : s
    
    interpret t -> bv[8]
    interpret s -> bv[4]
    interpret extract_lo -> bfe[3][0]

Here `bfe[3][0]` is the bit field extraction operator the takes the
low order 4 bits of a bit vector.
---
layout: page
title: The Ivy language
---

Ivy's language is designed to let you to specify and implement systems
in a way that is both convenient and conducive to automated
verification. Technically, this means that important verification
problems like invariant checking and bounded model checking fall
within a [decidable fragment][df] of first-order logic.

[df]: decidiability.html

For this reason, the Ivy language has certain unusual features. Ivy
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

A particularly unusual aspect of the Ivy language is that there are
*no references*. Two distinct variables are never "aliases" for the
same underlying "object". Modifying variable `a` never has an effect
on the value of variable `b`. Ivy's philosophy is that references are a
low-level optimization that should be used by compilers to avoid
copying, but should never appear in high-level programs. The absense
of aliases enormously simplifies the analysis, testing and
verification of programs.

Another unusual aspect of the Ivy language is that it is *synchronous*. This means that:

- All actions occur in reaction to input from the environment, and
- all actions are *isolated*, that is, they appear to occur
instantaneously, with no interruption.

This aspect of Ivy's semantics greatly simplifies reasoning about
concurrent and distributed systems.

We will now consider the basic elements of an Ivy program.

## The language specifier

Every Ivy file begins with a line like the following:

    #lang ivy1.7

This tells Ivy what version of the language we are using. This is
important because in successive version of the language, certain
features may be changed or deprecated. Providing the language version
allows old programs to keep working. They current version of the Ivy
language is 1.7. Changes between versions of the language are listed
at the end of this document.

## State and actions

An Ivy program describes *objects* that have state and
provide *actions* that operate on state. State variables may hold
either plain old data or mathematical relations and functions (much as
in the [Alloy][al] language, but with important differences that we
will discuss later).

[al]: http://alloy.mit.edu/alloy/

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

In Ivy, as in [Prolog][pl], identifiers beginning with capital letters
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
explicitly. An example of an enumerated type in Ivy would be:

    type color = {red,green,blue}

This declares a type with exactly three distinct values, and also declares
individuals `red`, `green` and `blue` as its elements.

### Actions

An *action* is Ivy's notion of a procedure that mutates the values of
state variables. For example, here is a declaration of an action that
adds a link between two nodes:

    action connect(x:node, y:node) = {
        link(x,y) := true
    }

The action `connect` is defined in terms of one of Ivy's primitive
actions: an assignment. An assignment modifies the value of a
variable.  In this case, the single pair (*x*,*y*) is added to the
relation `link` (or put another way, the value of the expression
`link(x,y)` is set to true, without otherwise modifying
`link`). Because there is no aliasing in Ivy,  the values of all other
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

The semicolon is a sequential composition operator in Ivy, not a
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
    
Ivy uses the
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

If there is more than one call within an expression, the calls are
executed in left-to-right order. Calls inside conditional operators
occur whether or not the condition is true. For example, the statement:

    x := sqrt(y) if c else z
    
is equivalent to:

    call temp := sqrt(y);
    x := temp if c else z

Parentheses are not used when calling an action with no parameters. 
For example, if we have:

    action next returns (val:t) = {
        current := current + 1;
        val := current
    }

then we would write:

    x := y + next

The lack of parentheses introduces no ambiguity, since the action
`next` is not a value and cannot itself be passed as an argument to
the function `+`. An advantage of this convention is that we don't have
to remember whether `next` is an action or a variable, and we can
easily replace a variable by an action without modifying all references
to the variable.


### Conditionals

Conditionals in Ivy are much as in any procedural programming
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

Because brackets are required, there is no ambiguity as to which 'if'
an 'else' belongs to.

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

Loops are discouraged in Ivy. Often, the effect of a loop can be
described using an assignment or an `if some` conditional. 

For example, instead of something like this:

    for y in type {
        link(x,y) := false
    }

we can write this:

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

In some situations we need to guarantee that a loop always terminates. We can do this
with ranking function that is supplied by the keyword `decreases`, like this:

    while i > 0
    invariant sum >= 0
    decreases i
    {
        sum := sum + f(i);
        i := i - 1
    }

The argument of `decreases` is an expression whose value must decrease
with every loop iteration and such that the loop is never entered when
the expression is less than `0`.


## Non-deterministic choice

The asterisk "*" can be used to represent non-deterministic choice in Ivy in
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

Expressions in Ivy are terms or formulas in [first-order logic][fol]
with equality. Ivy provides the following built-in operators: `~`
(not), `&` (and), `|` (or), `->` (implies), `<->` (iff) `=`
(equality). There is also a built-in conditional operator `X if C else
Y` that returns `X` if the Boolean condition `C` is true and `Y`
otherwise. The if/else operator binds most strongly, followed by
equality, not, and, or. The weakest binding operators are `<->` and
`->`, which have equal precedence.

[fol]: https://en.wikipedia.org/wiki/First-order_logic

The binary and ternary operators are left-associating (i.e., they bind
more strongly on the left). For example, `x if p else y if q else z`
is equivalent to `(x if p else y) if q else z` and `p -> q -> r` is
equivalent to `(p -> q) -> r`. *Warning*: in the case of if/else and
`->`, this is non-standard and is due to an error in the parser. This
will change in a future version of the language. In the interim it is
best to always parenthesize expressions with multiple uses if if/else
and `->`.

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

## Assume, require and ensure

The primitive actions `require` and `ensure` allow us to write
specifications. These actions fail if the associated condition
is false. For example, suppose we wish the `connect` action to handle
only the case where the node *y* is not in the failed set. We could
write

    action connect(x:node, y:node) = {
        require ~failed(y);
        link(x,y) := true
    }

If the condition `~failed(y)` is true, control passes through the
`require` and this action behaves in the same way as the original.  If
the condition `~failed(y)` is false, however, the `require` action
fails.  This means that whenever we use `connect` we must prove that
the *y* argument is not in the failed set.

The `ensure` action is similar, except it is the responsibility of the action
itself to ensure the truth of the formula. For example:

    action increment(x:node) returns (y:node) = {
        y := x + 1;
        ensure y > x
    }

The semantics of `require` and `ensure` are the same, except for the
assignment of blame when they fail. With `require`, the onus of
guaranteeing the truth of the formula falls on the action's caller,
while with `ensure` it falls on the action itself. We will refer to
`require` and `ensure` actions collectively as *assertions*.

On the other hand, the `assume` action does not allow control to pass
through if the associated condition is false. A typical application of
`assume` is to make a temporary modeling assumption that we wish later
to remove. For example, this action non-deterministically chooses a
non-failed node and connects *x* to it:

    action connect_non_failed(x:node) = {
        y := *;
        assume ~failed(y);
        link(x,y) := true
    }

Of course, if all the nodes are failed, this action cannot
terminate. There is some degree of risk in using assumptions when
modeling, since assumptions can eliminate behaviors in unexpected
ways. Ideally, a finished program will not contain any occurrence of
`assume`.

In `require`, `ensure` and `assume` actions, any [free variables][fv] are treated
as universally quantified. For example, if we want to connect *x* to a
node that is not currently linked to any node, we could change the
assumption above to

     assume ~link(y,Z)

[fv]: https://en.wikipedia.org/wiki/Free_variables_and_bound_variables

## Initialization

Normally, we expect a system to start in some well-defined state, or
at least for some specified conditions to hold initially. In Ivy, we use an
`after init` declaration for this purpose. For example:

    after init {
        link(X,Y) := false
    }

This provides an action that executes at initialization, before the
environment calls any other actions. Multiple `after init` actions are
executed in the order in which they are declared in the program.


## Local variables

The above example of a guarded command action assumes that *y* is a
declared program variable of type `node`. We can also declare *y* locally
within the action, like this:

    action connect_non_failed(x:node) = {
        var y:node;
        assume ~failed(y);
        link(x,y) := true
    }

This creates a fresh *y* that is in scope only within the action (or generally to the
end of the most tightly enclosing pair of brackets). We don't need a non-deterministic assignment
to *y* since the value of *y* is already non-deterministic at the point where it is declared.
We can create a local variable and assign it in the same statement, like this:

    var y:node := x

or, if the type of `y` can be inferred, just this:

    var y := x


## Modelling interleaving concurrency in Ivy

Actions in an Ivy program execute only in response to calls from the
program's environment. Ivy makes the synchronous hypothesis: when the
environment calls an action, it waits for the action to complete
before issuing another call. Put another way, Ivy actions appear to
execute in zero time. At first blush, it might seem that this
eliminates the possibility of concurrency. In fact, the synchronous
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

An Ivy program exports a set of actions to its environment. Each of
these actions can be used to model a single isolated step of a
process.  Since the environment is allowed to call these actions in an
arbitrary order, the Ivy program can be used to model arbitrary
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

    after init {
        semaphore(W) := true;
        link(X,Y) := false
    }

    action connect(x:client,y:server) = {
      require semaphore(y);
      link(x,y) := true;
      semaphore(y) := false
    }

    action disconnect(x:client,y:server) = {
      require link(x,y);
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
requires that server's semaphore be up on entry. The `disconnect`
action removes a link and puts the semaphore up. The two `export`
declarations at the end tell us that the environment may call
`connect` and `disconnect` in arbitrary sequence, though it must obey
the stated requirements.

## Safety and invariants

A program is *safe* if it cannot fail, so long as in the past all
requirements of the environment have been satisfied (that is, it is safe if 
any failure of the program can be blamed on the environment).

There are various ways to use assertions to specify desired safety
properties of a program. A simple one is to add a test action that
asserts some property of the program state. In the client/server
example above, we might specify that no two distinct clients can be
connected to a single server using the following test action:

    action test = {
      ensure ~(X ~= Z & link(X,Y) & link(Z,Y))
    }

    export test

The assertion is implicitly universally quantified over (distinct)
clients `X` and `Z` and server `Y`. To help Ivy to prove that this
assertion always holds, we can suggest facts that might be useful in
constructing an inductive invariant. For example:

    invariant X = Z | ~link(X,Y) | ~link(Z,Y)
    invariant link(X,Y) -> ~semaphore(Y)

Here, we state that no two clients are connected to the same server
(which is just the property we want to prove) and additionally that
when a client is connected to a server, its semaphore is down. These
facts are *inductive* in the sense that they are initially true, and
each of our three actions preserves them. Moreover, they are
sufficient to guarantee that our test assertion is true. Thus, Ivy can
use these invariants to prove safety of the program.

An invariant is asserted to hold at all times after initialization
when an exported action is *not* executing. In particular, the
invariant is not guaranteed to hold when the program calls back to the
environment (see `import` below) or when it calls one of its own
actions.


## Axioms and background theories

The built-in types and operators provided by Ivy are fairly
impoverished. We have only uninterpreted types, the Boolean type
`bool`, enumerated types and the basic operators of first-order
logic. This is by design. By introducing richer data types, or
*theories*, we would quickly make our verification problems
undecidable, meaning we would sacrifice reliability of automated
verification. In practice, before introducing, say, the integers into
a model, we should make sure that the power of the integers is really
needed. It may be, for example, that all we require is a totally
ordered set.

Ivy allows us to introduce background theories in the form of logical
axioms. This in turn allows us to avoid using unnecessarily powerful
theories. As an example, consider defining an ordering relation over 
our node ID's:

    relation (I:id < J:id)

This is an example of an *infix* symbol. The symbol `<` is no
different than other relational symbols, except that Ivy pre-defines
it as having infix syntax. 

We can ensure that `<` is a total order by writing axioms:

    axiom X:id < Y & Y < Z -> X < Z
    axiom ~(X:id < X)
    axiom X:id < Y | X = Y | Y < X

These axioms say, respectively, that `<` is
[transitive](https://en.wikipedia.org/wiki/Transitive_relation),
[anti-symmetric](https://en.wikipedia.org/wiki/Antisymmetric_relation)
and [total](https://en.wikipedia.org/wiki/Total_relation). As in other
cases, the free variables are universally quantified. 

Of course, axioms are assumptions and assumptions are dangerous.  We
want to make sure that our axioms are consistent, that is, that they
have at least one [model](https://en.wikipedia.org/wiki/Logic_model). The Ivy tool can be helpful in
determining this.

### Overloaded operators.

In Ivy the equality operator is *overloaded* in the sense that it
applies to any pair of arguments so long as they are of the same
type. One way to think of this is that there is really a distinct
equality operator pre-declared for each type, but that we use `=` as a
short-hand for all of them. It is useful to be able to declare other
such overloaded operators to avoid, for example, having to invent a
new "less than" symbol for every ordered type, or adding type
annotations to operators. 

Ivy provides for this in a limited way. Certain symbols, such as `<`,
`+` and `0` are always overloaded. This allows use the same symbol
with different type signatures disambiguate these uses based on type
inference.

To make type inference stronger, the overloaded operators also come
with type constraints. In functional language terms, `<` has type
`alpha * alpha -> bool` and `+` has type `alpha * alpha -> alpha`.

### Numerals

Numerals are a special case of overloaded symbols. A numeral is any
symbol beginning with a digit, for example `0`, or `0xdeadbeef`. The
types of numerals are inferred from context. For example, if `x` has
type `foo`, then in the expression `x+1`, the numeral `1` is inferred
to have type `foo`.

Numerals are special symbols in the sense that they do not have to be
explicitly declared. However, Ivy gives them no special
interpretation. Ivy does not even assume that distinct numerals have
distinct values. This means that `0 = 2` is not necessarily false.  In
fact, this equation might be true in a type representing the integers
mod 2.

Section [Interpretations] describes how to give concrete
interpretations to Ivy types, so that symbols like `+` and `0` have
specific meanings.

### Quoted symbols

A quoted symbol is a possibly-empty sequence of characters enclosed in
double quote characters (and not containing a double quote character).
An example would be `"ab$c"`. Quoted symbols are similar to numerals:
their type is inferred from context. 

## Modules

A *module* in Ivy is a group of declarations that can be instantiated.
In this way it is similar to a template class in an object-oriented
programming language. Besides defining classes of objects, modules can be
used to capture a re-usable theory, or structure a modular proof.

Here is a simple example of a module representing an up/down counter
with a test for zero:

    module counter(t) = {

        individual val : t
        after init {
            val := 0
        }

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

Any Ivy declaration can be contained in a module. This includes
axioms, invariants, instances and modules. As an example, here is a
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
object). Notice that we passed the overloaded infix symbol `<` as a
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
        after init {
            bit := false
        }
        action flip = {
            bit := ~bit
        }
    }

This creates a single object `foo` with members `foo.bit` and
`foo.flip`, exactly as if we had created a module and instantiated it
once.

### This

The special symbol `this` refers to the innermost surrounding object
or module. For example:

    object foo = {
        relation bit
        after init {
            this.bit := false
        }
    }
    
Here `this.bit` refers to `foo.bit`. In the outermost scope `this`
refers to the root object, which contains the entire program.

### Type objects

A type may have the same name as an object. This makes it possible
to define types with *traits*. For example:

    object num = {
        type this
        function next(N:this) : this
        function plus(X:this,Y:this) : this
    }
    
This declares a type `num` and also a function `num.next` from type
`num` to type `num` and am  function `plus` that takes two arguments of type `num`
and returns a `num`. The function `num.next` can be applied using
a special syntax. That is, if `x` is of type `num`, then the expression
`x.next` is a shorthand for `num.next(x)`. Similarly, `x.plus(y)` is a shorthand
for `num.next(x,y)`. Actions can similary be traits of types. For example:

    object num = {
        type this
        action plus(x:this,y:this) returns (z:this) = {
            z := x + y;
        }
    }
    
In this case, `x.plus(y)` is a shorthand for the action call `num.plus(x,y)`. 


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

Types in Ivy are never parameterized. For example, if we write:

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


The Ivy language supports these goals using *monitors*. A monitor is
an ordinary object, except that its actions are synchronized with the
actions of other objects. For example, suppose that in the
client/server example above, we want to specify that callers to
`connect` do not request a connection to a server whose semaphore is
down. We could express this property as a monitor like this:

    object mon = {
        action pre_connect(x:client,y:server) = {
            require semaphore(y)
        }        
        execute pre_connect before connect
    }

The `execute` declaration says that whenever `connect` is called,
action `pre_connect` should be executed first, with the same
parameters. If any caller tries to connect a client to a busy server,
the assertion will fail. Notice we used `require` here, so the
blame for the failure is on the caller of `connect`.

Monitors can also check the return values of actions. For example:

    action post_incr(inp:t) returns(out:t) = {
        ensure inp < out
    }

    execute post_incr after incr

Here, we have an action `incr` that is supposed to increment a value,
and we specify that the output must be greater than the input. Here,
we use `ensure`, so the blame for any failure falls in the
implementation of action `incr`.

As a shorthand, we can write our monitor action like this:

    after c.post(inp:t) returns(out:t) {
        ensure inp < out
    }

This creates a monitor action called `post.after` that is executed after `c.post`.
Similarly, we can write:

    before connect(x:client,y:server) {
        require semaphore(y)
    }        

If we drop the input or output parameters, they are inherited from the monitored action.
For example:

    after c.post {
        ensure inp < out
    }

This is a useful shorthand when the declaration of `c.post` is nearby,
but should probably be avoided otherwise.

We can write this:

    around foo {
        stmts1
        ...
        stmts2
    }

as a shorthand for this:

    before foo {
        stmts1
    }

    after foo {
        stmts2
    }

At present, local variables declared in `stmts1` cannot be referenced
in `stmts2`, but the intention is to make this possible, to reduce the
need to use `old` in after monitors.


### Monitor state

Usually, monitors contain state components that allow them to remember
some of the history of past events. For example, here is a monitor specifying a 
property of `counter` objects. It requires that immediately after a call to `up`,
the `is_zero` action cannot return true:

    module counter_prop(c) = {

        relation was_up
        after init {
            was_up := false
        }

        after c.up {
            was_up := true
        }

        after c.down {
            was_up := false
        }

        after c.is_zero returns (z:bool) {
            ensure was_up -> ~z
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


## Action implementations

It is often useful to separate the declaration of an action from its
implementation. We can declare an action like this:

    action incr(x:t) returns(y:t)

and then give its implementation separately like this:

    implement incr {
        y := x + 1
    }


## Initializers

As noted above, an initializer is a special action that is executed
once initially, before any exported actions are called. For example:

    var bit : bool

    after init {
        bit := false
    }

This behaves like a monitor after a special internal action called
`init`. Initializers are executed once in the order they are declared.

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
        var bit : bool

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

    var bit : bool

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
Ivy can compile the definition of `square` into a procedure. 

Ivy doesn't (currently) allow recursive definitions. So, for example,
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
verification conditions that Ivy can't decide (see the
[decidability](decidability.html) discussion). Suppose though, that we only need
to know the truth value of `rng` for some specific arguments. We can instead
write the definition like this:

    definition rng(x:t) = exists Y. f(Y) = x

Notice that the argument of `rng` is a constant `x`, not a place-holder
`X`. This definition acts like a macro (or an axiom *schema*) that can be
instantiated for specific values of `x`. So, for example, if we have an assertion
to prove like this:

    ensure rng(y)

Ivy will instantiate the definition like this:

    axiom rng(y) <-> exists Y. f(Y) = y

In fact, all instances of the macro will be alternation-free, since
Ivy guarantees to instantiate the macro using only ground terms for
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

The normal way of using Ivy is to declare uninterpreted types and to
give the necessary axioms over those types to prove desired properties
of a system. However, it is also possible in Ivy to associate types
with sorts that are interpreted in the underlying theorem prover. 

For example:

    type idx

    interpret idx -> int

This says that Ivy type `idx` should be interpreted using sort `int`
of the theorem prover. This does not mean that `idx` is equated with
the integers. If we also interpret type `num` with `int`, we still
cannot compare values of type `idx` and type `num`. In effect, these
two types are treated as distinct copies of the integers.

When we declare `idx` as `int`, certain overloaded functions and
relations on `idx` are also automatically interpreted by the
corresponding operators on integers, as are numerals of that
type. So, for example, `+` is interpreted as addition and `<` as
'less than' in the theory of integers. Numerals are given their normal
interpretations in the theory, so `0:idx = 1:idx` would be false.

Concrete sorts that are currently available for interpreting Ivy types
are:

- int: the integers
- nat: the non-negative integers
- {*X*..*Y*}: the subrange of integers from *X* to *Y* inclusive
- {*a*,*b*,*c*}: an enumerated type
- bv[*N*]: bit vectors of length *N*, where *N* > 0

Arithmetic on `nat` is saturating. That is, any operation that would yield
a neagtive number instead gives zero. 

An arbitrary function or relation symbol can be interpreted. This is useful
for symbols of the theory that have no pre-defined overloaded symbol in Ivy.
For example:

    type t
    type s
    function extract_lo(X:t) : s
    
    interpret t -> bv[8]
    interpret s -> bv[4]
    interpret extract_lo -> bfe[3][0]

Here `bfe[3][0]` is the bit field extraction operator the takes the
low order 4 bits of a bit vector.

## Parameters

A *parameter* is a value supplied by the environment before
initialization. A parameter is declared like this:

    parameter p : t

where *p* is the parameter name and *t* is the type. Parameters may be
declared anywhere in the object hierarchy. Except for the fact that it
is initialized by the environment, a parameter is identical to an
individual. The manner in which parameters are supplied is dependent
on the compiler. For example, if a program is compiled to an
executable file, the parameter values are supplied on the command
line. If it is compiled to a class in C++, parameters are supplied as
arguments to the constructor. In either case, the order of parameters
is the same as their order of declaration in the program.

## Imported actions

An imported action is an action whose implementation is provided by
the environment. For example:

    action callback(x:nat) returns (y:nat)
    import callback
    
or simply:

    import action callback(x:nat) returns (y:nat)

Like any action, the imported action may be given preconditions and
postconditions.  For example:

    before callback {
        require x > 0;
    }
    
    after callback {
        ensure y = x - 1;
    }
    
The `require` in this case is guarantee for the program and an
assumption for the environment. Similarly, the `ensure` is an
assumption for the program and a guarantee for the environment.  The
environment is assumed to be non-interfering, that is, Ivy assumes
that the call to `callback` has no visible side effect on the program.
An imported action may not be implemented by the program.

## Assume/guarantee reasoning

Ivy doesn't require us to prove all at once that a program is safe.
Instead, we can break the proof down into smaller proofs using the
*assume/guarantee* approach. 

For example, suppose we have the following program with two objects:

    #lang ivy1.7

    object num = {
        type this

        interpret this -> nat

        function even(X:this) = (X / 2 * 2 = X)
        function odd(X:this) = ~even(X)
    }

    object evens = {
        var number : num
        after init {
            number := 0
        }

        action step = {
            call odds.put(number + 1)
        }

        action put(n:num) = {
            number := n;
        }

        invariant number.even

    }

    object odds = {
        var number : num
        after init {
            number := 1
        }

        action step = {
            call evens.put(number + 1)
        }

        action put(n:num) = {
            number := n;
        }

        invariant number.odd

    }

    export evens.step
    export odds.step

Each object stores a natural number when its `put` action is called
and sends this number plus one to the other object when its `step`
action is called by the environment. We want to prove the invariants
that `evens.number` remains even, and `odds.number` remains odd.
Moreover, we would like to prove these invariants by reasoning about
`evens` and `odds` in isolation.  To do this, we use an
assume/guarantee specification.


Here is the `evens` object with separate specification and implementation:

    isolate evens = {

        action step
        action put(n:num)

        specification {
            before put {
                require n.even
            }
        }

        implementation {

            var number : num
            after init {
                number := 0
            }

            implement step {
                call odds.put(number + 1)
            }

            implement put(n:num) {
                number := n;
            }

            invariant number.even
        }
    }
    with odds,num

An *isolate* is a special kind of object that acts as a unit of
verification.  It generally has three parts. It starts with a
declaration of the *interface* of the object. This usually consists of
types, functions and actions that are provided by the object. The next
section is the *specification*. This usually consists of variables,
properties and monitors that are *visible* outside the
isolate. Finally, we have the *implementation*.  It usually consists
of variables, function definitions and action implementations that are
*hidden*. An isolate may depend on the visible parts of other objects.
This is declares using the keyword `with`. In this case `evens`
depends on `odds` and `nat`.

The isolate for `odds` is similar:

    isolate odds = {

        action step
        action put(n:num)

        specification {
            before put {
                require n.odd
            }
        }

        implementation {

            var number : num
            after init {
                number := 1
            }

            implement step {
                call evens.put(number + 1)
            }

            implement put {
                number := n;
            }

            invariant number.odd

        }
    }
    with evens,num


Effectively, this breaks the proof that the two assertions always hold
into two parts. In the first part, we assume the object `evens` gets
correct inputs and prove that it always sends correct outputs to
`odds`. In the second part, we assume the object `odds` gets correct
inputs and prove that it always sends correct outputs to `evens`.

This argument seems circular on the surface. It isn't, though, because
when we prove one of the assertion holds, we are only assuming that
the other assertion has always held *in the past*. So what we're
really proving is that neither of the two objects is the first to
break the rules, and so the rules always hold.

In the first isolate, we prove the assertion that `evens`
guarantees. We do this using the visible part of `odds`, but we forget
about the hidden state of the `odds` object (in particular, the
variable `odss.number`). To model the call to `evens.put` in the
hidden part of `odds`, Ivy exports `evens.put` to the environment.
The `requires` statement in the specification `even.put` thus becomes a
guarantee of the environment. That is, each isolate only guarantees those assertions for
which it receives the blame. The rest are assumed.

When we verifiy isolate `evens`, the result is as if we had actually entered the following program:

    #lang ivy1.7

    object nat {
        ...
    }

    object evens = {
        var number : nat
        after init {
            number := 0
        }

        action step = {
            call odds.put(number + 1)
        }

        action put(n:nat) = {
            require even(nat)
            number := n;
        }

        invariant number.even
    }

    object odds = {

        action put(n:nat) = {
            require odd(nat)
        }
    }

    export evens.step
    export evens.put

Notice the implementation of `odds.put` has been eliminated, and what
remains is just the assertion that the input value is odd (Ivy
verifies that the eliminated side effect of `odds.put` is in fact
invisible to `evens`). The assertion that inputs to `evens` are even
has in effect become an assumption. We can prove this isolate is safe
by showing that `even.number` is invariantly even, which means that
`odds.put` is always called with an odd number.

The other isolate, `odds`, looks like this:

    #lang ivy1.7

    object nat {
        ...
    }

    object evens = {

        action put(n:nat) = {
            require even(nat)
        }
    }

    object odds = {
        var number : nat
        after init {
            number = 1
        }

        action step = {
            call evens.put(number + 1)
        }

        action put(n:nat) = {
            require odd(nat)
            number := n;
        }

        invariant number.odd
    }

    export odds.step
    export odds.put


If both of these isolates are safe, then we know that neither
assertion is the first to fail, so the original program is safe.

The general rule is that a `require` assertion is a guarantee for the
calling isolate and and assumption for the called isolate, while an `ensure` action is
a guarantee for the called isolate and an assumption for the callinf isolate. When we
verify an isolate, we check only those assertions that are gurantees
for actions in the isolate.



## Changes between Ivy language versions

### New in version 1.2

- Keywords: returns, mixin, before, after, isolate, with, export, import, delegate, include

### Deprecated in version 1.2

- Keywords: state, set, null, match

### New in version 1.5

- Keywords: function, class, object, method, execute, destructor, 
  some, maximizing, maximizing, private, implement, using, property, while, invariant,
  struct, definition, ghost, alias, trusted, this, var, attribute, scenario, proof, named, fresh

### New in version 1.6

- Keywords: variant, of, globally, eventually, temporal

### New in version 1.7

- Keywords: decreases, specification, implementation, require, ensure, around, parameter
- The `iterable` module is added the standard library file `order`. This makes it possible
to declare a type that is finite and iterable, and whose size is a parameter.
- Due to an error, the `->` and `<->` operators changed from right-associating to left-associating.

### Deprecated in version 1.7

- The init declation (only 'after init' is now supported for initialization)



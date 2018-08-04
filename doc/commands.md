---
layout: page
title: IVy command reference
---

IVy's commands share a common argument syntax:

*command* *option*=*value* ... *file*.ivy

Common options
--------------

These options are common to all the IVy commands. In the following,
`name` represents a hierarchical IVy name, which may contain the `.`
character, and `boolean` represents a Boolean value `true` or `false`.


`isolate=name`

This options specifies the name of a isolate to verify or extract. 

`show_compiled=boolean`

If true, this option causes a representation of the elaborated IVy
code to be printed before doing any other work. The elaborated code
reflects all the module instantiations as well as the various
transformations performed by IVy's compiler to produce an
isolate. This is useful to see in detail what is contained in an
isolate.

`pedantic=boolean`

If true, certain optional warnings are enabled. The default value is false.


Commands
--------

ivy_check
=========

This command checks the proof of an IVy program. This includes
checking all the invariants and program assertions as well as the
non-interference check which guarantees that the division of the proof
into isolates is sound. If a particular isolate is specified with the
`isolate` option, then only the guarantees of this isolate are
checked.  To guarantee correctness of the program, it must be checked
without the `isolate` option.

During checking, `ivy_check` prints a summary of the contents of each
isolate being verified, including all assumptions and guarantees. For
each check of a guarantee, `PASS` is printed if the check passes and
`FAIL` if it fails.

The options of the `ivy_check` command are:

`diagnose=boolean`

If true, this options causes the check to stop at the first guarantee
that fails. A counterexample for this guarantee is constructed and the
graphical counterexample viewer is launched to display the
counterexample. The default value is false.

`trace=boolean`

If true, this options causes the check to stop at the first guarantee
that fails. A counterexample for this guarantee is constructed and a
corresponding execution trace is printed on standard out. The trace is
formatted so that in an emacs compilation buffer, references to source
lines are active links. The printed trace can be more convenient than the
graphical counterexample viewer, especially if the state contains functions
or relations of arity greater than two. 
The default value is false.

`summary=boolean`

If true, this causes the summary to be printed, but no actual checking
occurs. The default value is false.

`mutax=boolean`

If true, the check on use of mutable symbols in axioms is
relaxed. This feature should be used with caution. In principle an
axiom should be a tautology, in which case it is safe to assert it
even if it contains mutable symbols. In practice, however, it is very
easy to rule out possible system behaviors by incorrect use of axioms.
The default value of this option is false.

`interference=boolean`

If false, the interference check is not applied. This feature is
unsound and should be applied only as a temporary measure. The default
value is true.

`complete=logic`

This option affects the behavior of the fragment checker that checkers
whether verification conditions are contained in the prover's
decidable fragment. The possible values of `logic` are: 

- `epr` This is the "effectively propositional" fragment, which is extended to
  include stratified use of function symbols.
- `qf` This fragment allows interpreted theories of the prover, but no quantifiers.
- `fo` This is unrestricted first-order logic modulo the prover's theories.

The last option does not guarantee decidability and may result in
significant instability of the prover. The default value is `epr`.

`macro_finder=boolean`

This option enables the "macro finder" option in Z3. This detects
quantified formulas that behave as macros, and eliminates them by
substitution. This option is usually helpful, but occasionally causes
Z3 to be very slow. The default is true.

`incremental=boolean`

If true, Z3 is used incrementally when checking invariants. Default is true.

`seed=integer`

Sets the random seed for the SMT solver. 

ivy_show
--------

This command prints the elaborated program (see the option
`show_compiled` above) and exits.


ivy
-----

This command runs an interactive user interface for constructing
inductive invariants. The options are as follows:

`ui=interface`

Here, `interface` specifies the user interface for invariant construction. The values are:

- `art` This interface supports interactive construct of an Abstract Reachability Tree.
- `cti` This interface supports an interactive approach to invariant construction based
   on counterexamples to induction.

The default value is `art`.

ivy_to_cpp
------------

This command extracts an IVY program to C++. The `isolate` option in
this command usually references an 'extract' in the IVy program,
representing an implementation to be extracted. The options are:

`target={repl,test,class}"

The `ivy_to_cpp` command can extract code in several forms:

- `repl` This is a a "read-eval-print" loop that reads calls to exported actions from the
command line and writes output on calls to imported actions. 

- `test` This composes the extract with a randomized tester.

- `class` This produces only a C++ class representing the extract, without a main function.

There is no default value.

`classname=cname`

This gives the name of the extracted C++ class. The default is the
name of the main IVy file, without the `.ivy` extension. The names of
the extracted header and implementation files are `cname.h` and
`cname.cpp` respectively.

`build=boolean`

If true, this option causes the extracted C++ to be compiled. In case
of `repl` or `test` targets, the code is also linked into an
executable file. On Unix the name of the executable is the same as the
class name, whereas on Windows it is `cname.exe`, where `cname` is the
class name.

`compiler={g++,cl}`

This option determines the compiler used to build the code. The default is g++
on Unix and cl on Windows.

`trace=boolean`

This option causes statements producing trace information on stdout to
be inserted in the extracted code.

`main=cname`

Determines the name of the main function, if one is generated. The default is `main`.

`stdafx=boolean`

Causes the file `stdafx.h` to be included in the first line of the implementation file.

`outdir=directory`

Causes output files to be generated in `directory`. Default is the current directory.

 
 

 

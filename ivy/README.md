A tour of the code:
===================

Utilities
---------

- ivy_utils.py: utility function, command-line parameters, etc.


Logic
-----

- logic.py: AST representation for IVY's logic
- logic_util.py: support, substitution, etc.
- type_inference.py: type inference for the logic
- ivy_logic.py: wrapper for the above, plus logical signatures
- ivy_logic_utils.py: many utilities built on the above

SMT
---

- ivy_smtlib.py: definitions of SMTLIB theories
- ivy_solver.py: interface to Z3 SMT solver

Theorem proving
---------------

- ivy_theory.py: fragment checker and built-in proof rules
- ivy_proof.py: tactical prover

IVy language
------------

- ivy_lexer.py: lexical analyzer
- ivy_logic_parser.py: parser for formulas
- ivy_parser.py: parser for IVy language
- ivy_module.py: internal representation of IVy modules
- ivy_compiler.py: compiles IVy files to internal representation

Front-ends
----------

- ivy.py: interactive graphical invariant generation
- ivy_checker.py: command-line proof checker
- ivy_show.py: show isolates

Code extraction and Test
------------------------

- ivy_cpp_types.py: impementation of IVy types in C++
- ivy_cpp.py: internal representation of C++ programs
- ivy_to_cpp.py: translator to C++










- 
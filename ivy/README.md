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

Concept graphs
--------------

- concept.py: representation of concept domains
- concept_alpha.py: abstract the models of a constraint into a concept domain
- concept_interactive_session: interactive concept domain session
- cy_elements.py: representation if directed graphs in cytoscape format
- dot_layout.py: annotates cytoscape graphs with layout information using dot 
- ivy_graph.py: lays out concept domain element as a graph

A concept domain defines an abstraction in terms of a collection of concepts
and concept combiners. These is represented by the classes Concept, ConceptCombiner
qand ConceptDomain in concept.py. An element of the concept domain is represented
by a list of assignments of truth values to "facts", which are obtained by applying
concept combiners to concepts. 

The abstraction operator alpha for a domain takes a set of logical
structures, represented as the models of a formula, and yields the
abstraction of this set as an element of the concept domain. This is
computed by the function alpha in ivy_alpha.py, which uses an SMT
solver to determine validity of the facts in the concept domain over
the given set of structures.

An interactive concept domain session contains a formula to be abstracted and
a concept domain. It provides a set of operations for modifying the concept domain
interactively, for example, by case-splitting concepts. This is represented by the class
ConceptInteractiveSession in concept_interactive_session.

An object of class IvyGraph (in ivy_graph.py) encapsulates an
interactive concept session, and translates values in the concept
domain into graph layouts. It uses a JSON-based representation for
graphs also used by Cytoscape, represented by class CyElements
(cy_elements.py). Layout annotations are added to the graph using the
dot graph layout tool from graphviz. The vertices and edges of the
graph are also back-annotated with the corresponding "facts" from the
concept domain.

The graphs produced by IvyGraph are then wrapped with GUI elements
described below.

GUI elements
------------

- ivy_graph_ui.py: toolkit-indepent UI for concept graphs
- ivy_ui.py: toolkit-independent top level UI
- tk_cy.py: displays a cytoscape graph in a tk canvas
- tk_graph_ui.py: tcl/tk back end for ivy_graph_ui.py
- tk_ui.py: tcl/tk back end for ivy_ui.py

The basic UI operations for concept graphs are implemented in class
GraphWidget in ivy_graph_ui.py. This provides the user with a set of
operations for changing the concept domain, with an undo/redo
stack. Some user operations are also provided for constructing
abstract reachability graphs (ARG's). The GraphWidget class is
toolkit-independent, and is designed to be used as a mixin with a GUI
widget using a particular GUI toolkit. 

The class TkGraphWidget (tk_graph_ui.py) provides a GUI for concept
graphs using the tcl/tk toolkit. It uses tk_cy.py to render cytoscape
graphs onto a tk canvas.

The main UI for Ivy is provided by the class IvyUI (ivy_ui.py). Again,
this is the toolkit-independent part of the UI and is intended to be
used as a mixin. The main UI contains a collection of tabs, each of
which has an ARG and optionally a concept graph.

The class TkUI implements toolkit-dependent operations of the
top-level UI using tcl/tk.










- 

---
layout: page
title: Home
tags: "top-nav"
---


IVy is a tool for specifying, modeling, implementing and verifying
protcols. IVy is intended to allow interactive development of
protocols and their proofs of correctness and to provide a platform
for developing and experimenting with automated proof techniques. In
particular, IVy provides interactive visualization of automated
proofs, and supports a use model in which the human protocol designer
and the automated tool interact to expose errors and prove
correctness.


IVy has two primary design goals: to be as *transparent* as possible,
and to produce *design artifacts* that are useful even to engineers
who may lack the skills or resources needed to construct formal
proofs.

## Transparency

The research community has developed many impressive automated tools
for formal proof. For example, SMT solvers such as [Microsoft's
Z3](https://github.com/Z3Prover/z3) can check the validity of formulas
in various logics and can even generate inductive invariants. Because
these tools are heuristic in nature, however, they fail in ways that
are unpredictable and often not understandable by a human user.  To
reduce this problem, Ivy relies on interactive visualization, 
decidable logics and modularity

### Interactive visualization

Ivy constructs inductive invariants interactively, using visualization
techniques. When there is a problem in the proof, it searches for a
simple scenario to explain the problem and displays it graphically,
highlighting possibly relevant facts. Users can combine their
intuition with automated generalization techniques to refine the
proof. This approach can greatly reduce the *human time* needed to
construct a proof.

### Decidable logics and modularity

A logic is *decidable* if there is a algorithm that can determine the
truth of any formula. In practice, using decidable logics makes proof
automation more reliable and repeatable. It also makes it possible to
give transparent explanations of proof failures.

IVy's language is designed to make it practical to reduce all proof
obligations to statements in decidable logics. It provides primitives
to support modeling in decidable logics, and also modular refinement
techniques the makes it possible to separate the verification effort
into local, decidable problems. For example, we can verify a protocol
at a high level assuming that a given abstract type is totally
ordered, then implement that abstract type using bit vectors or
integers.

## Design artifacts

Another key focus of Ivy is to produce composable specifications that
can be used as a reference by designers and for rigorous testing of
designs. Ivy supports specifications that are both composable and
temporal. This means that if all components locally satisfy their
specifications, we know that the system as a whole correctly
implements its high-level semantics. Moreover, each component’s
specification can be used independently to test and verify that
component.

From composable specifications, Ivy can generate test benches and
tests oracles that can be used to test design components rigorously
against their specifications. Such testers can reveal latent bugs
in component implementations that do not appear in integration tests or
ad-hoc unit testing.


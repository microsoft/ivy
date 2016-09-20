---
layout: page
title: Introduction
---

Modular specifications have uses other than verification. Imagine that
we have formal interface specifications of all of the components of a
system. A formal argument tells us that, if all the component
implementations satisfy their specifications, then the system as a
whole satisfies its specification. However, we don't yet have formal
proofs that the component implementations are correct.

In this scenario we can use *compositional testing* to improve our
confidence in the system's correctness. We test each
component rigorously against its formal specification. If we have high
confidence in the correctness of all of the components, this
confidence transfers to the system as a whole because of our formal
proof. Put another way, if the system as a whole fails to satisfy its
specification, then necessarily one of its components fails its
specification and we can discover this fact by component testing.

The question is, how can we test the components rigorously in a way
that will give us high confidence of their correctness? One
possibility is to use a *constrained random* approach. That is, we
automatically generate test inputs for the component in a way that
satisfies its interface assumptions. We then check that the component's outputs
satisfy its interface guarantees. The purpose of randomness is to avoid bias
that might creep into a manually generated test suite or testbench.

Ivy can do just that. It can extract a component and a randomized test
environment for that component.  The test environment generates inputs
for the component, calling its exported actions with input parameters
that satisfy the component's assumptions. It also checks that all the
component outputs satisfy the component's guarantees.

This sort of rigorous component-based testing combines the advantages
of unit testing and integration testing. Like informal unit testing,
the method has the advantage that the component's inputs can be
controlled directly. This gives us much more flexibility to cover the
component's "corner cases" and to expose design errors. Unlike
informal unit testing, however, the method uses only the component's
specification, eliminating the possibility of human bias, and giving a
definitive reference for evaluating the test results. Like integration
testing, compositional testing allows us to gain confidence in the
correctness of the system as a whole. Compositional testing can be
much faster, however, because it takes many fewer steps to stimulate a
component bug through the component's interface rather than through
the system's interface. In addition, of course, we do not have to
execute the entire system to test it compositionally.

In the next few sections, we'll run through the same examples we
looked at with [compositional formal verification](../specification.html), but instead we'll
use compositional testing.


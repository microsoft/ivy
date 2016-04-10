#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
An example of the client server after one action.

Here is the formula I got from Ken (after some renaming and simplification):

Exists C0, S0, A0, B0. ForAll X, Y. (
S0(Y) &
~C0(X, Y) &
c(A0, B0) &
(~c(X, Y) | X = A0) &
(~c(X, Y) | Y = B0) &
~s(B0) &
(s(Y) | Y = B0)
)

"""

from logic import *
from concept import *
from concept_alpha import alpha
from logic_util import *

client_sort = UninterpretedSort('client')
server_sort = UninterpretedSort('server')

c = Const('c', FunctionSort(client_sort, server_sort, Boolean))
s = Const('s', FunctionSort(server_sort, Boolean))

X = Var('X', client_sort)
Y = Var('Y', server_sort)
A0 = Var('A0', client_sort)
B0 = Var('B0', server_sort)
C0 = Var('C0', c.sort)
S0 = Var('S0', s.sort)

state = Exists([C0, S0, A0, B0], ForAll([X, Y], And(
    S0(Y),
    Not(C0(X,Y)),
    c(A0,B0),
    Implies(c(X,Y), Eq(X,A0)),
    Implies(c(X,Y), Eq(Y,B0)),
    Not(s(B0)),
    Or(s(Y), Eq(Y,B0)),
)))

a0 = Const('a0', client_sort)
b0 = Const('b0', server_sort)
c0 = Const('c0', c.sort)
s0 = Const('s0', s.sort)

state_sk = substitute(state.body, {
    A0: a0,
    B0: b0,
    C0: c0,
    S0: s0,
})

# materialization constrains
a = Const('a', client_sort)
b = Const('b', server_sort)
constrains = And(Not(s(b)), c(a,b))

concepts = ConceptDict()
concepts.add('nodes','client', [X], Eq(X,X))
concepts.add('nodes','server', [Y], Eq(Y,Y))
concepts.add('node_labels','s', [Y], s(Y))
concepts.add('edges','c', [X,Y], c(X,Y))

cd = ConceptDomain(concepts, get_standard_combiners(), get_standard_combinations())

if __name__ == '__main__':
    print "State:"
    print state
    print

    print "Skolemized State:"
    print state_sk
    print


    print "Concept Domain:"
    cd.output()
    print

    print "Facts:"
    for tag, formula in cd.get_facts():
        print '   ', tag, formula
    print

    print "alpha:"
    a = alpha(cd, state_sk)
    for tag, value in a:
        if value:
            print '   ', tag
    print

    print "\n=== Splitting c_server on c_s ===\n"

    cd.split('server', 's')

    print "Concept Domain:"
    cd.output()
    print

    print "Facts:"
    for tag, formula in cd.get_facts():
        print '   ', tag, formula
    print

    print "alpha:"
    a = alpha(cd, state_sk)
    for tag, value in a:
        if value:
            print '   ', tag
    print

    from concept_render import render_concept_graph

    elements = render_concept_graph(
        a,
        cd.concepts['nodes'],
        cd.concepts['edges'],
        cd.concepts['node_labels'],
    )
    print "graph elements:"
    for x in elements:
        print '   ', x, ','
    print

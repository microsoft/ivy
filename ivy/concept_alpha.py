#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
"""

from z3_utils import z3_implies
from logic import Or

def alpha(concept_domain, state, cache=None):
    """
    Right now, state is just a plain formula

    This is a *very* unoptimized implementation
    """
    if z3_implies(state, Or()):
        return [(tag, True) for tag, formula in concept_domain.get_facts()]

    if cache is None:
        cache = dict()
    facts = concept_domain.get_facts()
    result = []
    for tag, formula in facts:
        if tag in cache:
            value = cache[tag]
        else:
            # assert len(cache) == 0, tag
            value = z3_implies(state, formula)
        result.append((tag, value))
    return result


if __name__ == '__main__':
    from collections import OrderedDict
    from logic import (Var, Const, Apply, Eq, Not, And, Or, Implies,
                       ForAll, Exists)
    from logic import UninterpretedSort, FunctionSort, first_order_sort, Boolean
    from logic_util import free_variables, substitute, substitute_apply
    from concept import Concept, ConceptCombiner, ConceptDomain

    def test(st):
        print st, "=", eval(st)

    S = UninterpretedSort('S')
    UnaryRelation = FunctionSort(S, Boolean)
    BinaryRelation = FunctionSort(S, S, Boolean)

    X, Y, Z = (Var(n, S) for n in ['X', 'Y', 'Z'])
    U = Var('U', UnaryRelation)
    U1 = Var('U1', UnaryRelation)
    U2 = Var('U2', UnaryRelation)
    B = Var('B', BinaryRelation)
    B1 = Var('B1', BinaryRelation)
    B2 = Var('B2', BinaryRelation)

    nstar = Const('nstar', BinaryRelation)
    x = Const('x', S)
    y = Const('y', S)

    c11 = Concept([X], And(Eq(x,X), Eq(y,X)))
    c10 = Concept([X], And(Eq(x,X), Not(Eq(y,X))))
    c01 = Concept([X], And(Not(Eq(x,X)), Eq(y,X)))
    c00 = Concept([X], And(Not(Eq(x,X)), Not(Eq(y,X))))

    cnstar = Concept([X, Y], nstar(X,Y))
    cnplus = Concept([X, Y], And(nstar(X,Y), Not(Eq(X,Y))))

    notexists = ConceptCombiner([U], Not(Exists([X], U(X))))
    exists = ConceptCombiner([U], Exists([X], U(X)))
    singleton = ConceptCombiner([U], ForAll([X,Y], Implies(And(U(X), U(Y)), Eq(X,Y))))
    all_to_all = ConceptCombiner(
        [U1, U2, B],
        ForAll([X,Y], Implies(And(U1(X), U2(Y)), B(X,Y)))
    )

    cd = ConceptDomain(
        OrderedDict([
            ('xy', c11),
            ('other', c00),
            ('x', c10),
            ('y', c01),
            ('nstar', cnstar),
            ('nplus', cnplus),
        ]),
        OrderedDict([
            ('notexists', notexists),
            ('exists', exists),
            ('singleton', singleton),
            ('all_to_all', all_to_all),
         ]),
        OrderedDict([
            ('node_info', (
                ['notexists', 'exists', 'singleton'],
                ['xy', 'other', 'x', 'y'],
            )),
            ('binary_info', (
                ['all_to_all'],
                ['xy', 'other', 'x', 'y'],
                ['xy', 'other', 'x', 'y'],
                ['nstar', 'nplus'],
            ))
        ]),
    )

    facts = cd.get_facts()
    print "facts = ["
    for tag, formula in facts:
        print '   ', tag, formula, ','
    print "]\n"

    state = And(
        ForAll([X,Y,Z], And(
            nstar(X,X),
            Implies(And(nstar(X,Y), nstar(Y,X)), Eq(X,Y)),
            Implies(And(nstar(X,Y), nstar(Y,Z)), nstar(X,Z)),
            Implies(And(nstar(X,Y), nstar(X,Z)), Or(nstar(Y,Z), nstar(Z,Y))),
        )),

        nstar(x,y),
        Not(Eq(x,y)),
        ForAll([Z], Implies(And(nstar(x,Z), Not(Eq(x,Z))), nstar(y,Z))),
    )

    abstract_value = alpha(cd, state)
    print "abstract_value = ["
    for tag, value in abstract_value:
        print '   ', tag, value, ','
    print "]\n"

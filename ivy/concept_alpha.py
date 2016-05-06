#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
"""

# from z3_utils import z3_implies
import ivy_solver as slvr
from logic import Or, Not
import time
import ivy_utils as iu

def alpha(concept_domain, state, cache=None, projection=None):
    """
    Right now, state is just a plain formula

    This is a *very* unoptimized implementation
    """

    time1 = time.time()

    facts = concept_domain.get_facts(projection)

    time2 = time.time()

    solver = slvr.new_solver()

    slvr.solver_add(solver,state)

#    iu.dbg('state')

    if cache is None:
        cache = dict()
    result = []
    for tag, formula in facts:
        if tag in cache:
            value = cache[tag]
#            print "cached: {} = {}".format(tag,value)
        else:
            # assert len(cache) == 0, tag
            solver.push()
            slvr.solver_add(solver,Not(formula))
            value = not slvr.is_sat(solver)
            solver.pop()
            cache[tag] = value
#            print "computed: {} = {}".format(tag,value)

        result.append((tag, value))

    time3 = time.time()

#    print 'alpha times: get_facts: {} check: {}'.format(time2-time1,time3-time2)

    return result


if __name__ == '__main__':
    from collections import ConceptDict
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

    c11 = Concept('xy',[X], And(Eq(x,X), Eq(y,X)))
    c10 = Concept('x',[X], And(Eq(x,X), Not(Eq(y,X))))
    c01 = Concept('y',[X], And(Not(Eq(x,X)), Eq(y,X)))
    c00 = Concept('other',[X], And(Not(Eq(x,X)), Not(Eq(y,X))))

    cnstar = Concept('nstar',[X, Y], nstar(X,Y))
    cnplus = Concept('nplus',[X, Y], And(nstar(X,Y), Not(Eq(X,Y))))

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

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Conversion of logic.py's formulas to Z3 and some tests using Z3

Ideally, this file should be the only file to improt the z3 module
"""

import z3

from logic import (Var, Const, Apply, Eq, Ite, Not, And, Or, Implies,
                   Iff, ForAll, Exists)
from logic import (UninterpretedSort, FunctionSort, Boolean, true,
                   false, first_order_sort)


_z3_interpreted = {
    Boolean: z3.BoolSort(),
    true: z3.BoolVal(True),
    false: z3.BoolVal(False),
}

_z3_uninterpreted_sorts = {}

_z3_operators = {
    Eq: lambda t1, t2: t1 == t2,
    Ite: z3.If,
    Not: z3.Not,
    And: z3.And,
    Or: z3.Or,
    Implies: z3.Implies,
    Iff: lambda t1, t2: t1 == t2,
}

_z3_quantifiers = {
    ForAll: z3.ForAll,
    Exists: z3.Exists,
}

_to_z3_cache = {}

def to_z3(x):
    """
    Convert terms or sorts to Z3 objects.
    """
    if x not in _to_z3_cache:
        _to_z3_cache[x] = _to_z3(x)
    return _to_z3_cache[x]


def _to_z3(x):
    """
    Convert a term or a sort to a Z3 object.
    """

    if x in _z3_interpreted:
        return _z3_interpreted[x]

    elif type(x) is UninterpretedSort:
        if x not in _z3_uninterpreted_sorts:
            _z3_uninterpreted_sorts[x] = z3.DeclareSort(x.name)
        return _z3_uninterpreted_sorts[x]

    elif type(x) is FunctionSort:
        assert False, "FunctionSort's aren't converted to Z3"

    elif type(x) in (Var, Const) and first_order_sort(x.sort):
        return z3.Const(x.name + ':' + str(x.sort), to_z3(x.sort))

    elif type(x) in (Var, Const) and type(x.sort) is FunctionSort and len(x.sort.sorts) == 1:
        # convert to first order
        s = x.sort.sorts[0]
        return z3.Const(x.name + ':' + str(s), to_z3(s))

    elif type(x) in (Var, Const) and type(x.sort) is FunctionSort:
        assert type(x) is Const, "Cannot convert high-order variables to Z3, only constants"
        return z3.Function(x.name, *(
            to_z3(s) for s in x.sort
        ))

    elif type(x) is Apply and len(x.terms) == 0:
        # convert application to use of first order symbol
        return to_z3(x.func)

    elif type(x) is Apply:
        return to_z3(x.func)(*(to_z3(t) for t in x.terms))

    elif type(x) in _z3_operators:
        return _z3_operators[type(x)](*(to_z3(y) for y in x))

    elif type(x) in _z3_quantifiers:
        if len(x.variables) == 0:
            return to_z3(x.body)
        else:
            return _z3_quantifiers[type(x)](
                [to_z3(v) for v in x.variables],
                to_z3(x.body),
            )

    else:
        assert False, type(x)


_implies_cache = {}


def z3_implies(f1, f2, timeout=False):
    """
    Use z3 to test if f1 imples f2
    """
    key = (f1, f2)
    if key in _implies_cache:
        return _implies_cache[key]
    s = z3.Solver()
    if timeout:
        s.set("timeout", 2000) # 2 seconds
        #s.set("timeout", 60000) # 1 minute
    s.add(to_z3(f1))
    s.add(to_z3(Not(f2)))
    res = s.check()
    if res == z3.sat:
        _implies_cache[key] = False
        return False
    elif res == z3.unsat:
        _implies_cache[key] = True
        return True
    else:
        # no caching of unknown results
        print "z3 returned: {}".format(res)
        assert False
        return None


def z3_implies_batch(premise, formulas, timeout=False):
    """
    Use z3 to test if premise implies each formula in formulas

    Equivalent to: [z3_implies(premise, f) for f in formulas]
    but more efficient
    """
    #import IPython
    #IPython.embed()
    s = z3.Solver()
    if timeout:
        s.set("timeout", 2000) # 2 seconds
        #s.set("timeout", 60000) # 1 minute
    s.add(to_z3(premise))
    result = []
    for f in formulas:
        key = (premise, f)
        if key in _implies_cache:
            result.append(_implies_cache[key])
        else:
            s.push()
            s.add(to_z3(Not(f)))
            res = s.check()
            s.pop()
            if res == z3.sat:
                _implies_cache[key] = False
                result.append(False)
            elif res == z3.unsat:
                _implies_cache[key] = True
                result.append(True)
            else:
                # no caching of unknown results
                print "z3 returned: {}".format(res)
                assert False
                result.append(None)
    return result


if __name__ == '__main__':
    S = UninterpretedSort('S')
    X, Y, Z = (Var(n, S) for n in ['X', 'Y', 'Z'])
    BinRel = FunctionSort(S, S, Boolean)
    leq = Const('leq', BinRel)
    transitive1 = ForAll((X, Y, Z), Implies(And(leq(X,Y), leq(Y,Z)), leq(X,Z)))
    transitive2 = ForAll((X, Y, Z), Or(Not(leq(X,Y)), Not(leq(Y,Z)), leq(X,Z)))
    transitive3 = Not(Exists((X, Y, Z), And(leq(X,Y), leq(Y,Z), Not(leq(X,Z)))))
    antisymmetric = ForAll((X, Y), Implies(And(leq(X,Y), leq(Y,X), true), Eq(Y,X)))

    print z3_implies(transitive1, transitive2)
    print z3_implies(transitive2, transitive3)
    print z3_implies(transitive3, transitive1)
    print z3_implies(transitive3, antisymmetric)
    print

    print z3_implies(true, Iff(transitive1, transitive2))
    print

    x, y = (Const(n, S) for n in ['x', 'y'])
    b = Const('b', Boolean)
    print z3_implies(b, Eq(Ite(b, x, y), x))
    print z3_implies(Not(b), Eq(Ite(b, x, y), y))
    print z3_implies(Not(Eq(x,y)), Iff(Eq(Ite(b, x, y), x), b))

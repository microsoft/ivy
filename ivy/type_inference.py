#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Hindley Milner style type inference for formulas with TopSort's in them.

Note that the top sorts do not have type variables.

Type inference identifies variables and constants by name, so any two
symbols with the same name will be unified, and a SortError will be
raised if the unification fails.

TODO: add support for Ite and Iff.
"""

from itertools import product, chain

from logic import (Var, Const, Apply, Eq, Ite, Not, And, Or, Implies,
                   Iff, ForAll, Exists)
from logic import (UninterpretedSort, FunctionSort, Boolean, TopSort,
                   SortError, contains_topsort, is_polymorphic)
from logic_util import used_constants, free_variables


class SortVar(object):
    """
    A sort variable, to be replaced by an arbitrary sort.

    The instance property is used to implement union find, and it can
    either be None, another SortVar object, or a sort object.

    Note that a SortVar passes the first_order_sort test, even though
    it may stand for a second order sort, so it can be passed to
    FunctionSort.
    """
    def __init__(self):
        self.instance = None
    def __str__(self):
        if self.instance is not None:
            return str(self.instance)
        else:
            return repr(self)


def find(x):
    """
    x may be a sort object or a SortVar
    """
    if type(x) is not SortVar or x.instance is None:
        return x
    else:
        # collapse the path and return the root
        x.instance = find(x.instance)
        return x.instance


def occurs_in(s1, s2):
    """
    Checks if s1 occurs in s2
    """
    s1 = find(s1)
    s2 = find(s2)
    return (s1 == s2 or (
        type(s2) is FunctionSort and
        any(occurs_in(s1, x) for x in s2)
    ))


def unify(s1, s2):
    """
    Unify s1 and s2.

    s1 and s2 may be sorts or SortVar objects.

    This raises SortError if they cannot be unified.
    """
    s1 = find(s1)
    s2 = find(s2)

    if (s1 == s2 or
        type(s1) is TopSort or
        type(s2) is TopSort):
        pass

    elif type(s1) is SortVar:
        assert s1.instance is None
        if occurs_in(s1, s2):
            raise SortError("Recursive unification: {}, {}".format(s1, s2))
        else:
            s1.instance = s2

    elif type(s2) is SortVar:
        unify(s2, s1)

    elif (type(s1) is FunctionSort and
          type(s2) is FunctionSort and
          s1.arity == s2.arity):
        for x, y in zip(s1, s2):
            unify(x, y)

    else:
        raise SortError("Cannot unify sorts: {}, {}".format(s1, s2))


def convert_from_sortvars(s):
    """
    Convert sort vars to TopSort
    """
    s = find(s)
    if type(s) is SortVar:
        return TopSort()
    elif type(s) is FunctionSort:
        return FunctionSort(*(
            convert_from_sortvars(x) for x in s
        ))
    else:
        return s


def insert_sortvars(s,env):
    """
    Convert each named TopSort to a new SortVar
    """
    if type(s) is TopSort and s.is_sort_variable():
        if s not in env:
            env[s] = SortVar()
        return env[s]
    elif type(s) is FunctionSort:
        return FunctionSort(*(
            insert_sortvars(x,env) for x in s
        ))
    else:
        return s

def infer_sorts(t, env=None):
    """
    Infer the sort of term t in environment env.

    env maps symbol names to sort variables.

    The result is a pair: (s, tt) where s is a sort or sort variable
    with the sort of t in env, and tt is a closure that, when called,
    will concretize t according to inferred sort information at its
    call time.

    If env is not None, it must contain all the free variables and
    constants used in t.
    """

    if env is None:
        names = free_variables(t, by_name=True).union(
            x.name for x in used_constants(t)
        )
        env = dict((name, SortVar()) for name in names)

    if type(t) in (Var, Const):
        if is_polymorphic(t):  # each instance can have different sort
            s = insert_sortvars(t.sort,{})
        else:
            s = env[t.name]
            unify(s, t.sort)
        return s, lambda: type(t)(t.name, convert_from_sortvars(s))

    elif type(t) is Apply:
        func_s, func_t = infer_sorts(t.func, env)
        xys = [infer_sorts(tt, env) for tt in t.terms]
        terms_s = [x for x, y in xys]
        terms_t = [y for x, y in xys]
        sorts = terms_s + [SortVar()]
        unify(func_s, FunctionSort(*sorts))
        return sorts[-1], lambda: Apply(func_t(), *(
            x() for x in terms_t
        ))

    elif type(t) is Eq:
        s1, t1 = infer_sorts(t.t1, env)
        s2, t2 = infer_sorts(t.t2, env)
        unify(s1, s2)
        return Boolean, lambda: Eq(t1(), t2())

    elif type(t) is Ite:
        s_cond, t_cond = infer_sorts(t.cond, env)
        s_then, t_then = infer_sorts(t.t_then, env)
        s_else, t_else = infer_sorts(t.t_else, env)
        unify(s_cond, Boolean)
        unify(s_then, s_else)
        return s_then, lambda: Ite(t_cond(), t_then(), t_else())

    elif type(t) in (Not, And, Or, Implies, Iff):
        xys = [infer_sorts(tt, env) for tt in t]
        terms_s = [x for x, y in xys]
        terms_t = [y for x, y in xys]
        for s in terms_s:
            unify(s, Boolean)
        return Boolean, lambda: type(t)(*[
            x() for x in terms_t
        ])

    elif type(t) in (ForAll, Exists):
        # create a copy of the environment and shadow that quantified
        # variables
        env = env.copy()
        env.update((v.name, SortVar()) for v in t.variables)
        vars_t = [infer_sorts(v, env)[1] for v in t.variables]
        body_s, body_t = infer_sorts(t.body, env)
        unify(body_s, Boolean)
        return Boolean, lambda: type(t)(
            [x() for x in vars_t],
            body_t(),
        )

    elif hasattr(t,'clone'):
        xys = [infer_sorts(tt, env) for tt in t.args]
        terms_t = [y for x, y in xys]
        return TopSort(), lambda: t.clone([
            x() for x in terms_t
        ])
        
    else:
        assert False, type(t)


def concretize_sorts(t, sort=None):
    """
    Retrun a term obtained from t by replacing TopSort's with concrete
    terms. If sort is given, then an additional constraint is added
    that the sort of t should unify with sort.
    """
    s, tt = infer_sorts(t)
    if sort is not None:
        unify(s, sort)
    return tt()


if __name__ == '__main__':
    S = UninterpretedSort('S')
    T = TopSort()
    UnaryRelationS = FunctionSort(S, Boolean)
    BinaryRelationS = FunctionSort(S, S, Boolean)
    UnaryRelationT = FunctionSort(T, Boolean)
    BinaryRelationT = FunctionSort(T, T, Boolean)

    XS, YS = (Var(n, S) for n in ['X', 'Y'])
    XT, YT = (Var(n, T) for n in ['X', 'Y'])

    xs, ys = (Const(n, S) for n in ['x', 'y'])
    xt, yt = (Const(n, T) for n in ['x', 'y'])

    rs = Const('r', BinaryRelationS)
    ps = Const('p', UnaryRelationS)
    rt = Const('r', BinaryRelationT)
    pt = Const('p', UnaryRelationT)
    tt = Const('tt', T)
    TT = Var('TT', T)

    f1 = And(ps(XS), ps(xs))
    cf1 = concretize_sorts(f1)
    print repr(f1)
    print repr(cf1)
    assert f1 == cf1
    print

    f2 = And(ps(XT), pt(xs))
    cf2 = concretize_sorts(f2)
    print repr(f2)
    print repr(cf2)
    print

    f3 = Exists([TT], And(ps(XT), TT(xs)))
    cf3 = concretize_sorts(f3)
    print repr(f3)
    print repr(cf3)
    print

    f4 = Iff(xt, Ite(yt, xt, XT))
    cf4 = concretize_sorts(f4)
    print repr(f4)
    print repr(cf4)
    print


    # TODO: add more tests, specifically a test that checks
    # unification across different quantified bodies



    """
    c10 = Concept([X], And(p(X), Not(q(X))))
    c01 = Concept([X], And(Not(p(X)), q(X)))
    c00 = Concept([X], And(Not(p(X)), Not(q(X))))

    crn = Concept([X, Y], Or(r(X,Y), n(X,Y)))

    X, Y, _ = (Var(n, T) for n in ['X', 'Y', 'Z'])
    U = Var('U', UnaryRelationT)
    U1 = Var('U1', UnaryRelationT)
    U2 = Var('U2', UnaryRelationT)
    B = Var('B', BinaryRelationT)
    B1 = Var('B1', BinaryRelationT)
    B2 = Var('B2', BinaryRelationT)

    notexists = ConceptCombiner([U], Not(Exists([X], U(X))))
    exists = ConceptCombiner([U], Exists([X], U(X)))
    singleton = ConceptCombiner([U], ForAll([X,Y], Implies(And(U(X), U(Y)), Eq(X,Y))))
    mutually_exclusive = ConceptCombiner(
        [U1, U2],
        ForAll([X, Y], Not(And(U1(X), U2(Y))))
    )
    all_to_all = ConceptCombiner(
        [U1, U2, B],
        ForAll([X,Y], Implies(And(U1(X), U2(Y)), B(X,Y)))
    )
    total = ConceptCombiner(
        [U1, U2, B],
        ForAll([X], Implies(U1(X), Exists([Y], And(U2(Y), B(X,Y)))))
    )
    injective = ConceptCombiner(
        [U1, U2, B],
        ForAll([X, Y, Z], Implies(And(U1(X), U2(Y), U2(Z), B(X,Y), B(X,Z)), Eq(Y,Z)))
    )

    """

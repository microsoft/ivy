#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
"""

from itertools import product, chain
from functools import partial

from logic import (Var, Const, Apply, Eq, Ite, Not, And, Or, Implies,
                   Iff, ForAll, Exists)
from logic import contains_topsort


def union(*sets):
    if len(sets) == 0:
        return frozenset()
    else:
        return frozenset.union(*sets)


def used_variables(*terms):
    """
    Returns a frozenset of variables used in given terms.

    Note that this returns all used variables, not just free ones.
    """

    t = terms[0] if len(terms) == 1 else terms

    if type(t) is Var:
        return frozenset((t,))

    elif type(t) in (tuple, Const, Apply, Eq, Ite, Not, And, Or,
                     Implies, Iff):
        return union(*(used_variables(x) for x in t))

    elif type(t) in (ForAll, Exists):
        return union(used_variables(t.body), t.variables)

    elif hasattr(t,'args'):
        return union(*(used_variables(x) for x in t.args))

    else:
        assert False, type(t)


def free_variables(*terms, **kwargs):
    """
    Returns a frozenset of variables free in given terms.

    kwargs: by_name , False by default.
    If by_name=True, the result is a set of variable names, and
    binding occurs by name. Otherwise, the result is a set of Var
    objects, and ForAll X:s1 does not bind X:s2.
    """
    by_name = kwargs.get('by_name', False)
    _free_variables = partial(free_variables, by_name=by_name)

    t = terms[0] if len(terms) == 1 else terms

    if type(t) is Var:
        return frozenset((t.name if by_name else t,))

    elif type(t) in (tuple, Const, Apply, Eq, Ite, Not, And, Or,
                     Implies, Iff):
        return union(*(_free_variables(x) for x in t))

    elif type(t) in (ForAll, Exists):
        return _free_variables(t.body) - _free_variables(*t.variables)

    elif hasattr(t,'args'):
        return union(*(_free_variables(x) for x in t.args))

    else:
        assert False, type(t)


def used_constants(*terms):
    """
    Returns a frozenset of constants used in given terms.
    """

    t = terms[0] if len(terms) == 1 else terms

    if type(t) is Const:
        return frozenset((t,))

    elif type(t) in (tuple, Var, Apply, Eq, Ite, Not, And, Or,
                     Implies, Iff, ForAll, Exists):
        return union(*(used_constants(x) for x in t))

    elif hasattr(t,'args'):
        return union(*(used_constants(x) for x in t.args))

    else:
        assert False, type(t)


def substitute(t, subs):
    """
    Return the term obtained from t by simultaneous substitution given
    by subs

    subs is either a dictionary or a mapping given by an iterable of
    (key, value) pairs

    Both keys and values in subs can be either Var or Const.
    All keys in subs will be substituted by their values in subs.

    For variables, only free occurances will be substituted.

    If the substitution will create capturing of a free variable, the
    substitution will fail with an error.
    """

    if not isinstance(subs, dict):
        subs = dict(subs)

    if type(t) in (Var, Const):
        if t in subs:
            return subs[t]
        else:
            return t

    elif type(t) in (Apply, Eq, Ite, Not, And, Or, Implies, Iff):
        return type(t)(*(substitute(x, subs) for x in t))

    elif type(t) in (ForAll, Exists):
        forbidden_variables = free_variables(*subs.values())
        if forbidden_variables.isdisjoint(t.variables):
            return type(t)(t.variables, substitute(t.body, (
                (k, v) for k, v in subs.iteritems()
                if k not in t.variables
            )))
        else:
            assert False, (t, subs) # capturing would be created

    else:
        assert False, type(e)


def substitute_apply(t, subs, by_name=False):
    """
    Return the term obtained from t by simultaneous substitution given
    by subs

    subs is either a dictionary or a mapping given by an iterable of
    (key, value) pairs

    Both keys and values in subs can be either Var or Const, but must
    be 2nd order. For any key, value in subs, Apply(key, *terms) is
    substituted by value(*terms'), so the values in subs should be
    python functions (terms' is the result of recursively substituting
    terms according to subs).

    For variables, only free occurances will be substituted.

    To avoid capturing, the free variables of value(*terms) should be
    a subset of the free variables of terms, for any value in
    subs. This is checked, and an error occurs if this is not the
    case, even if it does not lead to capturing. If by_name=True, then
    this check is done by name and not by the Var object.

    Note that non-application occurances of keys from subs in t are
    not substituted (these should generally not occur).
    """

    if not isinstance(subs, dict):
        subs = dict(subs)

    _substitute_apply = partial(substitute_apply, subs=subs, by_name=by_name)

    if type(t) in (Var, Const):
        return t

    if type(t) is Apply and t.func in subs:
        terms = tuple(_substitute_apply(x) for x in t.terms)
        result = subs[t.func](*terms)
        fvr = free_variables(result, by_name=by_name)
        fvt = free_variables(*terms, by_name=by_name)
        assert fvr <= fvt, "New free variables!? {}, {}".format(fvr, fvt)
        return result

    elif type(t) in (Apply, Eq, Ite, Not, And, Or, Implies, Iff):
        return type(t)(*(_substitute_apply(x) for x in t))

    elif type(t) in (ForAll, Exists):
        return type(t)(t.variables, _substitute_apply(t.body, subs=dict(
            (k, v) for k, v in subs.iteritems()
            if k not in t.variables
        )))
    else:
        assert False, type(e)


def normalize_quantifiers(t):
    """
    Push universals inside conjunctions and existentials inside
    disjunctions, and flatten conjunctions and disjunctions
    """

    if type(t) in (Var, Const):
        return t

    elif type(t) in (Apply, Eq, Ite, Not, Implies, Iff):
        return type(t)(*(normalize_quantifiers(x) for x in t))

    elif type(t) in (And, Or):
        return type(t)(*(
            z
            for x in t
            for y in [normalize_quantifiers(x)]
            for z in (y if type(y) is type(t) else [y])
        ))

    elif ((type(t) is ForAll and type(t.body) is And) or
          (type(t) is Exists and type(t.body) is Or)):
        return normalize_quantifiers(type(t.body)(*(
            type(t)(t.variables, x)
            for x in t.body
        )))

    elif type(t) in (ForAll, Exists):
        return type(t)(free_variables(t.body) & frozenset(t.variables),
                       normalize_quantifiers(t.body))

    else:
        assert False, type(t)


def is_tautology_equality(t):
    """Returns True if t is Eq(x,x) for some x"""
    return type(t) is Eq and t.t1 == t.t2


if __name__ == '__main__':
    from logic import *
    s1 = UninterpretedSort('s1')
    s2 = UninterpretedSort('s2')
    X1 = Var('X', s1)
    X2 = Var('X', s2)
    f = ForAll([X1], Eq(X2,X2))
    assert free_variables(f) == {X2}
    assert free_variables(f, by_name=True) == set()
    assert free_variables(f.body) == {X2}
    assert free_variables(f.body, by_name=True) == {'X'}

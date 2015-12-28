#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_logic import *
from ivy_logic_utils import *

def env_find(env, t):
    v = t
    while isinstance(v, Variable) and v.rep in env:
        v = env[v.rep]
    return v

def terms_mgu(terms1, terms2):
    if len(terms1) != len(terms2):
        return False, dict()

    env = dict()
    for t1, t2 in zip(terms1, terms2):
        if t1.sort != t2.sort:
            return False, dict()
        v1 = env_find(env, t1)
        v2 = env_find(env, t2)

        if is_constant(v1):
            if is_constant(v2):
                if v1.rep != v2.rep:
                    return False, dict()
            else:
                assert v2.rep not in env
                env[v2.rep] = v1
        else:
            assert v1.rep not in env
            if is_constant(v2) or v1.rep != v2.rep:
                env[v1.rep] = v2

    #print env

    subs = dict( (rep, env_find(env, env[rep])) for rep in env.iterkeys() )
    return True, subs

def test_terms_mgu():
    V = Variable
    C = Constant
    x = V('x')
    y = V('y')
    z = V('z')
    a = C('a')
    b = C('b')
    match, subs = terms_mgu([x, y, x, b, y],
                            [a, z, a, z, b])
    assert match and (
        repr(sorted(subs.items())) ==
        "[('x', Constant {rep: a}), ('y', Constant {rep: b}), ('z', Constant {rep: b})]"
    )



def mgu(atom1, atom2):
    if atom1.relname != atom2.relname:
        return False, dict()
    else:
        return terms_mgu(atom1.args, atom2.args)


def terms_mgu_eq(terms1, terms2):
    if len(terms1) != len(terms2):
        return False, dict(), []

    eqs = []
    env = dict()
    for t1, t2 in zip(terms1, terms2):
        if t1.sort != t2.sort:
            return False, dict(), []
        v1 = env_find(env, t1)
        v2 = env_find(env, t2)

        if is_constant(v1):
            if is_constant(v2):
                if v1.rep != v2.rep:
                    eqs.append(Atom(equals,[v1,v2]))
            else:
                assert v2.rep not in env
                env[v2.rep] = v1
        else:
            assert v1.rep not in env
            if is_constant(v2) or v1.rep != v2.rep:
                env[v1.rep] = v2

    #print env

    subs = dict( (rep, env_find(env, env[rep])) for rep in env.iterkeys() )
    return True, subs, eqs


def mgu_eq(atom1, atom2):
    if atom1.relname != atom2.relname:
        return False, dict(), []
    else:
        return terms_mgu_eq(atom1.args, atom2.args)


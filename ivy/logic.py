#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
"""

from operator import itemgetter

from general import IvyError
from utils.recstruct_object import recstruct

# Exceptions

class SortError(IvyError):
    pass


# Sorts


class UninterpretedSort(recstruct('UninterpretedSort', ['name'], [])):
    __slots__ = ()
    def __str__(self):
        return self.name


class BooleanSort(recstruct('BooleanSort', [], [])):
    __slots__ = ()
    def __str__(self):
        return 'Boolean'

Boolean = BooleanSort()


class FunctionSort(recstruct('FunctionSort', [], ['*sorts'])):
    __slots__ = ()
    @classmethod
    def _preprocess_(cls, *sorts):
        if len(sorts) == 0:
            raise IvyError("Must have range sort")
        if any(not first_order_sort(s) for s in sorts):
            raise IvyError("No high order functions")
        return sorts
    def __str__(self):
        return ' * '.join(str(s) for s in self.domain) + ' -> ' + str(self.range)
    domain = property(itemgetter(slice(None,-1)), doc='tuple of sorts')
    range = property(itemgetter(-1))
    arity = property(lambda self: len(self.domain))


class TopSort(recstruct('TopSort', ['name="TopSort"'], [])):
    """
    An unknown sort. Either 1st order or 2nd order.
    """
    __slots__ = ()
    @classmethod
    def _preprocess_(cls, name):
        return (name,)
    def __str__(self):
        return self.name
    def is_sort_variable(self):
        return self.name != 'TopSort'

TopS = TopSort()


def first_order_sort(s):
    return type(s) is not FunctionSort


def contains_topsort(x):
    """
    x can be a term or a sort
    """
    return (
        x == TopS or
        hasattr(x, 'sort') and contains_topsort(x.sort) or
        any(contains_topsort(y) for y in x)
    )

def is_polymorphic(x):
    """
    x can be a term or a sort
    """
    return (
        type(x) == TopSort and x.is_sort_variable() or
        hasattr(x, 'sort') and is_polymorphic(x.sort) or
        any(is_polymorphic(y) for y in x)
    )


# Terms

class Var(recstruct('Var', ['name', 'sort'], [])):
    __slots__ = ()
    @classmethod
    def _preprocess_(cls, name, sort):
        if name and not name[0].isupper():
            raise IvyError("Bad variable name: {!r}".format(name))
        return name, sort
    def __str__(self):
        return self.name
    def __call__(self, *terms):
        return Apply(self, *terms)


class Const(recstruct('Const', ['name', 'sort'], [])):
    __slots__ = ()
    @classmethod
    def _preprocess_(cls, name, sort):
#        if not name or name[0].isupper():
#            raise IvyError("Bad constant name: {!r}".format(name))
        return name, sort
    def __str__(self):
        return self.name
    def __call__(self, *terms):
        return Apply(self, *terms)


class Apply(recstruct('Apply', [], ['func', '*terms'])):
    __slots__ = ()

    @classmethod
    def _preprocess_(cls, func, *terms):
        if type(func.sort) is TopSort:
            pass
        elif type(func.sort) is not FunctionSort:
            raise SortError("Tried to apply a non-function: {}".format(func))
        elif func.sort.arity != len(terms):
            print func.sort.arity
            print func.sort
            raise SortError("Bad arity in: {}({})".format(
                str(func),
                ', '.join(str(t) for t in terms)
            ))
        else:
            bad_sorts = [i for i in range(func.sort.arity) if
                         terms[i].sort != func.sort.domain[i] and
                         not any(type(t) is TopSort for t in (terms[i].sort, func.sort.domain[i]))]
            if len(bad_sorts) > 0:
                raise SortError("Bad sorts in: {}({}) (positions: {})".format(
                    str(func),
                    ', '.join(repr(t) for t in terms),
                    bad_sorts,
                ))
        return (func, ) + terms

    def __str__(self):
        if len(self.terms) == 0:
            return str(self.func)
        else:
            return '{}({})'.format(
                str(self.func),
                ', '.join(str(t) for t in self.terms)
            )

    sort = property(lambda self: TopS if self.func.sort == TopS else
                    self.func.sort.range)


class Eq(recstruct('Eq', [], ['t1', 't2'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, t1, t2):
        if TopS in (t1.sort, t2.sort):
            pass
        elif t1.sort != t2.sort:
            raise SortError("Cannot compare different sorts: {}:{} == {}:{}".format(t1,t1.sort,t2,t2.sort))
        elif not first_order_sort(t1.sort):
            raise SortError("Cannot compare high order sorts: {} == {}".format(t1, t2))
        return t1, t2
    def __str__(self):
        return '({} == {})'.format(self.t1, self.t2)


class Ite(recstruct('Ite', [], ['cond', 't_then', 't_else'])):
    __slots__ = ()
    @classmethod
    def _preprocess_(cls, cond, t_then, t_else):
        if cond.sort not in (Boolean, TopS):
            raise SortError("Ite condition must be Boolean: {}".format(body))
        elif TopS in (t_then.sort, t_else.sort):
            pass
        elif t_then.sort != t_else.sort:
            raise SortError("Ite then and else terms must have same sort: {}, {}".format(t_then, t_else))
        elif not first_order_sort(t_then.sort):
            pass # TODO: should we raise the following exception?
            #raise SortError("Cannot apply Ite to high order sorts: {}, {}".format(t_then, t_else))
        return cond, t_then, t_else
    def __str__(self):
        return 'Ite({}, {}, {})'.format(self.cond, self.t_then, self.t_else)
    sort = property(lambda self: self.t_then.sort if self.t_then.sort != TopS else self.t_else.sort)


class Not(recstruct('Not', [], ['body'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, body):
        if body.sort not in (Boolean, TopS):
            raise SortError("Negation body must be Boolean: {}".format(body))
        return (body,)
    def __str__(self):
        if type(self.body) is Eq:
            return '({} != {})'.format(self.body.t1, self.body.t2)
        else:
            return 'Not({})'.format(self.body)


class And(recstruct('And', [], ['*terms'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, *terms):
        bad_sorts = [i for i, t in enumerate(terms)
                     if t.sort not in (Boolean, TopS)]
        if len(bad_sorts) > 0:
            raise SortError("Bad sorts in: And({}) (positions: {})".format(
                ', '.join(str(t) for t in terms),
                bad_sorts,
            ))
        return sorted(set(terms))
    def __str__(self):
        return 'And({})'.format(
            ', '.join(str(t) for t in self)
        )


class Or(recstruct('Or', [], ['*terms'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, *terms):
        bad_sorts = [i for i, t in enumerate(terms)
                     if t.sort not in (Boolean, TopS)]
        if len(bad_sorts) > 0:
            raise SortError("Bad sorts in: Or({}) (positions: {})".format(
                ', '.join(str(t) for t in terms),
                bad_sorts,
            ))
        return sorted(set(terms))
    def __str__(self):
        return 'Or({})'.format(
            ', '.join(str(t) for t in self)
        )


class Implies(recstruct('Implies', [], ['t1', 't2'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, t1, t2):
        bad_sorts = [i for i, t in enumerate([t1, t2])
                     if t.sort not in (Boolean, TopS)]
        if len(bad_sorts) > 0:
            raise SortError("Bad sorts in: Implies({}, {}) (positions: {})".format(
                t1, t2, bad_sorts,
            ))
        return t1, t2
    def __str__(self):
        return 'Implies({}, {})'.format(self.t1, self.t2)


class Iff(recstruct('Iff', [], ['t1', 't2'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, t1, t2):
        bad_sorts = [i for i, t in enumerate([t1, t2])
                     if t.sort not in (Boolean, TopS)]
        if len(bad_sorts) > 0:
            raise SortError("Bad sorts in: Iff({}, {}) (positions: {})".format(
                t1, t2, bad_sorts,
            ))
        return t1, t2
    def __str__(self):
        return 'Iff({}, {})'.format(self.t1, self.t2)


class ForAll(recstruct('ForAll', ['variables'], ['body'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, variables, body):
        if not all(type(v) is Var for v in variables):
            raise IvyError("Can only quantify over variables")
        if body.sort not in (Boolean, TopS):
            raise SortError("Quantified body must be Boolean: {}", body)
        return frozenset(variables), body
    def __str__(self):
        return '(ForAll {}. {})'.format(
            ', '.join('{}:{}'.format(v.name, v.sort) for v in sorted(self.variables)),
            self.body)


class Exists(recstruct('Exists', ['variables'], ['body'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, variables, body):
        if not all(type(v) is Var for v in variables):
            raise IvyError("Can only quantify over variables")
        if body.sort not in (Boolean, TopS):
            raise SortError("Quantified body must be Boolean: {}", body)
        return frozenset(variables), body
    def __str__(self):
        return '(Exists {}. {})'.format(
            ', '.join('{}:{}'.format(v.name, v.sort) for v in sorted(self.variables)),
            self.body)


true = Const('true', Boolean)
false = Const('false', Boolean)


if __name__ == '__main__':
    S = UninterpretedSort('S')
    X, Y, Z = (Var(n, S) for n in ['X', 'Y', 'Z'])
    BinRel = FunctionSort(S, S, Boolean)
    leq = Const('leq', BinRel)

    transitive1 = ForAll((X, Y, Z), Implies(And(leq(X,Y), leq(Y,Z)), leq(X,Z)))
    transitive2 = ForAll((X, Y, Z), Or(Not(leq(X,Y)), Not(leq(Y,Z)), leq(X,Z)))
    transitive3 = Not(Exists((X, Y, Z), And(leq(X,Y), leq(Y,Z), Not(leq(X,Z)))))

    antisymmetric = ForAll((X, Y), Implies(And(leq(X,Y), leq(Y,X)), Eq(Y,X)))

    assert Eq(X,Y) == Eq(Y,X)

    X, Y = (Var(n, TopS) for n in ['X', 'Y']) # note that Z remains Z:S
    f = Const('f', FunctionSort(TopS, TopS, Boolean))
    g = Const('g', FunctionSort(S, S, Boolean))
    h = Const('h', TopS)
    partial_function1 = ForAll([X, Y, Z], Implies(And(f(X,Y), f(X,Z)), Eq(Y,Z)))
    partial_function2 = ForAll([X, Y, Z], Implies(And(g(X,Y), g(X,Z)), Eq(Y,Z)))
    partial_function3 = ForAll([X, Y, Z], Implies(And(h(X,Y), h(X,Z)), Eq(Y,Z)))

    assert contains_topsort(X)
    assert not contains_topsort(Z)
    assert contains_topsort(f)
    assert not contains_topsort(g)
    assert contains_topsort(h)


    # TODO: add more tests, add tests for errors

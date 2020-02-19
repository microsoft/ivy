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


class EnumeratedSort(recstruct('EnumeratedSort', ['name','extension'], [])):
    __slots__ = ()
    @classmethod
    def _preprocess_(cls, name, extension):
        extension = tuple(extension)
        return name,extension
    def __str__(self):
        return '{' + ','.join(self.extension) + '}'
    @property
    def constructors(self):
        return [Const(n,self) for n in self.extension]
    @property
    def card(self):
        return len(self.extension)

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
        type(x) == Const and not x.name[0].islower() or
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
        return Apply(self, *terms) if len(terms) > 0 else self


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
        return Apply(self, *terms) if len(terms) > 0 else self


def report_bad_sort(op,position,expected,got):
    raise SortError("in application of {}, at position {}, expected sort {}, got sort {}" 
                    .format(op,position+1,expected,got))

class Apply(recstruct('Apply', [], ['func', '*terms'])):
    __slots__ = ()

    @classmethod
    def _preprocess_(cls, func, *terms):
        if type(func.sort) is TopSort:
            pass
        elif type(func.sort) is not FunctionSort:
            raise SortError("Tried to apply a non-function: {}".format(func))
        elif func.sort.arity != len(terms):
            raise SortError("Bad arity in: {}({})".format(
                str(func),
                ', '.join(str(t) for t in terms)
            ))
        else:
            bad_sorts = [i for i in range(func.sort.arity) if
                         terms[i].sort != func.sort.domain[i] and
                         not any(type(t) is TopSort for t in (terms[i].sort, func.sort.domain[i]))]
            for i in bad_sorts:
                print 'terms = {}'.format(terms)
                report_bad_sort(func,i,func.sort.domain[i],terms[i].sort)
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
        if type(t1.sort) == TopSort or type(t2.sort) == TopSort:
            pass
        elif t1.sort != t2.sort:
            raise SortError("Cannot compare different sorts: {}:{} == {}:{}".format(t1,t1.sort,t2,t2.sort))
        elif not first_order_sort(t1.sort):
            raise SortError("Cannot compare high order sorts: {} == {}".format(t1, t2))
        return t1, t2
    def __str__(self):
        return '({} == {})'.format(self.t1, self.t2)


# Ite expressions must be given a sort, as otherwise contructing trees of
# Ite's is quadratic.


class Ite(recstruct('Ite', ['sort'], ['cond', 't_then', 't_else'])):
    __slots__ = ()
    def __init__(self, cond, t_then, t_else):
        super(Ite, self).__init__(t_then.sort,cond,t_then,t_else)
    @classmethod
    def _preprocess_(cls, sort, cond, t_then, t_else):
        if cond.sort not in (Boolean, TopS):
            raise SortError("Ite condition must be Boolean: {}".format(body))
        elif isinstance(t_then.sort,TopSort) or isinstance(t_else.sort,TopSort):
            pass
        elif t_then.sort != t_else.sort:
            raise SortError("Ite then and else terms must have same sort: {}, {}".format(t_then, t_else))
        elif not first_order_sort(t_then.sort):
            pass # TODO: should we raise the following exception?
            #raise SortError("Cannot apply Ite to high order sorts: {}, {}".format(t_then, t_else))
        return sort, cond, t_then, t_else
    def __str__(self):
        return 'Ite({}, {}, {})'.format(self.cond, self.t_then, self.t_else)


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


class Globally(recstruct('Globally', ['environ'], ['body'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, environ, body):
        assert environ is None or isinstance(environ,str)
        if body.sort not in (Boolean, TopS):
            raise SortError("Globally body must be Boolean: {}".format(body))
        return environ,body
    def __str__(self):
        environ = self.environ
        return 'globally{}({})'.format('' if environ is None else '['+str(environ)+']',self.body)


class Eventually(recstruct('Eventually', ['environ'], ['body'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, environ, body):
        assert environ is None or isinstance(environ,str)
        if body.sort not in (Boolean, TopS):
            raise SortError("Eventually body must be Boolean: {}".format(body))
        return environ,body
    def __str__(self):
        environ = self.environ
        return 'eventually{}({})'.format('' if environ is None else '['+str(environ)+']',self.body)


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
        return tuple(terms)
#        return sorted(set(terms))
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
        return tuple(terms)
#        return sorted(set(terms))
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
        if len(variables) == 0:
            raise IvyError("Must quantify over at least one variable")
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
        if len(variables) == 0:
            raise IvyError("Must quantify over at least one variable")
        if not all(type(v) is Var for v in variables):
            raise IvyError("Can only quantify over variables")
        if body.sort not in (Boolean, TopS):
            raise SortError("Quantified body must be Boolean: {}", body)
        return frozenset(variables), body
    def __str__(self):
        return '(Exists {}. {})'.format(
            ', '.join('{}:{}'.format(v.name, v.sort) for v in sorted(self.variables)),
            self.body)


class Lambda(recstruct('Lambda', ['variables'], ['body'])):
    __slots__ = ()
    sort = Boolean
    @classmethod
    def _preprocess_(cls, variables, body):
        if not all(type(v) is Var for v in variables):
            raise IvyError("Can only abstract over variables")
        return tuple(variables), body
    def __str__(self):
        return '(Lambda {}. {})'.format(
            ', '.join('{}:{}'.format(v.name, v.sort) for v in sorted(self.variables)),
            self.body)


class NamedBinder(recstruct('NamedBinder', ['name', 'variables', 'environ'], ['body'])):
    __slots__ = ()
    @classmethod
    def _preprocess_(cls, name, variables, environ, body):
        assert environ is None or isinstance(environ,str)
        if not all(type(v) is Var for v in variables):
            raise IvyError("Can only abstract over variables")
        # TODO: check the name after we decide on valid names
        return name, tuple(variables), environ, body
    def __str__(self):
        environ = self.environ
        return '(${}{} {}. {})'.format( # TODO: change after we decide on the syntax for this
            self.name,
            '' if environ is None else '['+str(environ)+']',
            ', '.join('{}:{}'.format(v.name, v.sort) for v in sorted(self.variables)),
            self.body)
    def __call__(self, *terms):
        return Apply(self, *terms) if len(terms) > 0 else self
    sort = property(
        lambda self:
        FunctionSort(*([v.sort for v in self.variables] + [self.body.sort]))
        if len(self.variables) > 0 else
        self.body.sort
    )


# true = Const('true', Boolean)
# false = Const('false', Boolean)
true = And()
false = Or()

if __name__ == '__main__':
    S = UninterpretedSort('S')
    X, Y, Z = (Var(n, S) for n in ['X', 'Y', 'Z'])
    BinRel = FunctionSort(S, S, Boolean)
    leq = Const('leq', BinRel)

    transitive1 = ForAll((X, Y, Z), Implies(And(leq(X,Y), leq(Y,Z)), leq(X,Z)))
    transitive2 = ForAll((X, Y, Z), Or(Not(leq(X,Y)), Not(leq(Y,Z)), leq(X,Z)))
    transitive3 = Not(Exists((X, Y, Z), And(leq(X,Y), leq(Y,Z), Not(leq(X,Z)))))

    antisymmetric = ForAll((X, Y), Implies(And(leq(X,Y), leq(Y,X)), Eq(Y,X)))

    # assert Eq(X,Y) == Eq(Y,X)

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

    b = NamedBinder('mybinder', [X,Y,Z], None, Implies(And(f(X,Y), f(X,Z)), Eq(Y,Z)))
    print b
    print b.sort
    print

    b = NamedBinder('mybinder', [X,Y,Z], None, Z)
    print b
    print b.sort


    # TODO: add more tests, add tests for errors

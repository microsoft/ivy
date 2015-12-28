#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""

"""


import sys as _sys
from operator import itemgetter as _itemgetter
from keyword import iskeyword as _iskeyword
from collections import OrderedDict


class Test(object):
    """A test class with:
    metadata: x,y
    sub: a,b,*args

    This does not have hash-consing, isn't really immutable, isn't
    optimized, and just explores the interface

    I also didn't worry about pickling here, assuming I will add this
    later

    """

    _meta_fields = ('x', 'y')
    _sub_fields = ('a', 'b', '*args')

    @property
    def x(self):
        return self._meta[0]
    @property
    def y(self):
        return self._meta[1]
    @property
    def a(self):
        return self._sub[0]
    @property
    def b(self):
        return self._sub[1]
    @property
    def args(self):
        return self._sub[2:]

    def __init__(self, x, y, a, b, *args):
        super(Test, self).__setattr__('_meta', (x, y))
        super(Test, self).__setattr__('_sub', (a, b) + tuple(args))

    def __repr__(self):
        """Return a nicely formatted representation string"""
        return type(self).__name__ + repr(self._meta + self._sub)

    def __eq__(self, other):
        return type(self) is type(other) and (self._meta + self._sub) == (other._meta + other._sub)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __lt__(self, other):
        return ((type(self), ) + self._meta + self._sub).__lt__(other)

    def __le__(self, other):
        return ((type(self), ) + self._meta + self._sub).__le__(other)

    def __gt__(self, other):
        return ((type(self), ) + self._meta + self._sub).__gt__(other)

    def __ge__(self, other):
        return ((type(self), ) + self._meta + self._sub).__ge__(other)

    def __hash__(self):
        return hash((type(self), ) + self._meta + self._sub)

    def __getslice__(self, i, j):
        return self._sub.__getslice__(i, j)

    def __getitem__(self, i):
        return self._sub.__getitem__(i)

    def __iter__(self):
        return self._sub.__iter__()

    def __contains__(self, x):
        return self._sub.__contains__(x)

    def __len__(self):
        return self._sub.__len__()

    def __setattr__(self, name, value):
        raise AttributeError("can't set attribute")


    """
    The following can be implemented by delegation to self._sub:
    count
    index
    """

    """
    Could add namedtuple's _make and _replace, but don't see a need now
    """

    """
    For pickling support, should check:
    __getnewargs__
    __getinitargs__
    __getstate__
    __setstate__
    """

_class_template = '''\
class {typename}(object):

    __slots__ = ('_meta_fields', '_sub_fields')

    _meta_fields = {meta_field_names!r}
    _sub_fields = {sub_field_names!r}

    def __init__(self, {meta_arg_list}{sub_arg_list}):        
        #super({typename}, self).__setattr__('_meta', _tupler({meta_arg_list}))
        #super({typename}, self).__setattr__('_sub', _tupler({sub_arg_list}))
        object.__setattr__(self, '_meta', _tupler({meta_arg_list}))
        object.__setattr__(self, '_sub', _tupler({sub_arg_list}))

    def __repr__(self):
        """Return a nicely formatted representation string"""
        return type(self).__name__ + repr(self._meta + self._sub)

    def __eq__(self, other):
        return type(self) is type(other) and (self._meta + self._sub) == (other._meta + other._sub)

    def __ne__(self, other):
        return not self.__eq__(other)

    """
    def __lt__(self, other):
        return ((type(self), ) + self._meta + self._sub).__lt__(((type(other), ) + other._meta + other._sub))

    def __le__(self, other):
        return ((type(self), ) + self._meta + self._sub).__le__(((type(other), ) + other._meta + other._sub))

    def __gt__(self, other):
        return ((type(self), ) + self._meta + self._sub).__gt__(((type(other), ) + other._meta + other._sub))

    def __ge__(self, other):
        return ((type(self), ) + self._meta + self._sub).__ge__(((type(other), ) + other._meta + other._sub))
    """

    def __lt__(self, other):
        if hasattr(other, '_meta'):
            other = other._meta + other._sub
        return (self._meta + self._sub).__lt__(other)

    def __le__(self, other):
        if hasattr(other, '_meta'):
            other = other._meta + other._sub
        return (self._meta + self._sub).__le__(other)

    def __gt__(self, other):
        if hasattr(other, '_meta'):
            other = other._meta + other._sub
        return (self._meta + self._sub).__gt__(other)

    def __ge__(self, other):
        if hasattr(other, '_meta'):
            other = other._meta + other._sub
        return (self._meta + self._sub).__ge__(other)

    def __hash__(self):
        #return hash((type(self), ) + self._meta + self._sub)
        return hash(self._meta + self._sub)

    def __getslice__(self, i, j):
        return self._sub.__getslice__(i, j)

    def __getitem__(self, i):
        return self._sub.__getitem__(i)

    def __iter__(self):
        return self._sub.__iter__()

    def __contains__(self, x):
        return self._sub.__contains__(x)

    def __len__(self):
        return self._sub.__len__()

    def __setattr__(self, name, value):
        raise AttributeError("can't set attribute")

{field_defs}
'''

_meta_field_template = '''\
    @property
    def {name}(self):
        return self._meta[{index}]
'''

_sub_field_template = '''\
    @property
    def {name}(self):
        return self._sub[{index}]
'''

_variadic_field_template = '''\
    @property
    def {name}(self):
        return self._sub[{index}:]
'''

def rectagtuple(typename,
                meta_field_names, 
                sub_field_names,
                verbose=False):

    # currently no validation of field names
    assert (type(meta_field_names) is tuple and
            all(type(x) is str for x in meta_field_names))
    assert (type(sub_field_names) is tuple and
            all(type(x) is str for x in sub_field_names))

    if len(sub_field_names) > 0 and sub_field_names[-1][0] == '*':
        variadic = sub_field_names[-1][1:]
    else:
        variadic = None

    # Fill-in the class template
    meta_arg_list = ''.join(
        '{}, '.format(x) for x in meta_field_names
    )
    sub_arg_list = ', '.join(sub_field_names)
    field_defs = '\n'.join(
        [_meta_field_template.format(index=index, name=name)
         for index, name in enumerate(meta_field_names)] +
        [_sub_field_template.format(index=index, name=name)
         for index, name in enumerate(sub_field_names)
         if name[0] != '*'] +
        [_variadic_field_template.format(index=index, name=name[1:])
         for index, name in enumerate(sub_field_names)
         if name[0] == '*']
     )
    class_definition = _class_template.format(
        typename=typename,
        meta_field_names=meta_field_names,
        sub_field_names=sub_field_names,
        meta_arg_list=meta_arg_list,
        sub_arg_list=sub_arg_list,
        field_defs=field_defs,
    )

    if verbose:
        print class_definition

    # Execute the template string in a temporary namespace and support
    # tracing utilities by setting a value for
    # frame.f_globals['__name__']
    namespace = dict(__name__='rectagtuple_{}'.format(typename),
                     _tupler=lambda *x: x)
    try:
        exec class_definition in namespace
    except SyntaxError as e:
        raise SyntaxError(e.message + ':\n' + class_definition)
    result = namespace[typename]

    # For pickling to work, the __module__ variable needs to be set to the frame
    # where the named tuple is created.  Bypass this step in environments where
    # sys._getframe is not defined (Jython for example) or sys._getframe is not
    # defined for arguments greater than 0 (IronPython).
    try:
        result.__module__ = _sys._getframe(1).f_globals.get('__name__', '__main__')
    except (AttributeError, ValueError):
        pass

    return result

def test_combos():
    for meta in [(), ('m0',), ('m0', 'm1')]:
        for sub in [(), ('s0',), ('s0', 's1')]:
            for args in [(), ('*args',)]:
                rectagtuple('Test', 
                            meta,
                            sub + args,
                            verbose=True)

tagtuple = rectagtuple('tagtuple', (), ('*args',), verbose=False)

def rectuple(typename, field_names, verbose=False):
    return rectagtuple(typename, (), field_names, verbose=verbose)
    # return rectagtuple(typename, field_names, (), verbose=verbose)


if __name__ == '__main__':
    import pickle
    from itertools import chain, product

    print "Testing tagtuple:"
    print

    class A(tagtuple):
        __slots__ = ()

    class B(tagtuple):
        __slots__ = ()

    a = A(1, 2, 3)
    b = B(1, 2, 3)
    t = (1, 2, 3)

    print "a: ", a
    print "b: ", b
    print "t: ", t
    print
    print "a == b: ", a == b
    print "a != b: ", a != b
    print "hash(a) == hash(b): ", hash(a) == hash(b)
    print "a <= b: ", a <= b
    print "b <= a: ", b <= a
    print
    print "a == t: ", a == t
    print "a != t: ", a != t
    print "hash(a) == hash(t): ", hash(a) == hash(t)
    print "a <= t: ", a <= t
    print "t <= a: ", t <= a
    print
    d = {}
    d[a] = 1
    d[b] = 2
    d[t] = 3
    print "d: ", d
    s = set()
    s.add(a)
    s.add(b)
    s.add(t)
    print "s: ", s
    print
    print "tuple(x for x in a): ", tuple(x for x in a)
    print "list(a): ", list(a)
    print "tuple(a): ", tuple(a)
    print

    a0 = pickle.loads(pickle.dumps(a, 0))
    a1 = pickle.loads(pickle.dumps(a, 1))
    a2 = pickle.loads(pickle.dumps(a, 2))
    print "a0: ", a0
    print "a1: ", a1
    print "a2: ", a2
    print "a0 == a, hash(a0) == hash(a): ", a0 == a, hash(a0) == hash(a)
    print "a1 == a, hash(a1) == hash(a): ", a1 == a, hash(a1) == hash(a)
    print "a2 == a, hash(a2) == hash(a): ", a2 == a, hash(a2) == hash(a)
    print

    print "a[:]: ", a[:]
    print "a[1:-1]: ", a[1:-1]
    """
    print "a + a: ", a + a
    print "a + b: ", a + b
    print "(0, ) + a: ", (0, ) + a
    print "a + (0, ): ", a + (0, )
    print "2 * a: ", 2 * a
    print "a * 2: ", a * 2
    print
    """
    print "A(*chain((x**2 for x in range(10)), a)): ", A(*chain((x**2 for x in range(10)), a))
    print "A(*product(range(3), repeat=2)): ", A(*product(range(3), repeat=2))
    print


    print "Testing rectuple:"
    print

    A = rectuple('A', ('x', 'y'), verbose=True)
    B = rectuple('B', ('x', 'y'), verbose=True)

    a = A(1,2)
    b = B(1,2)
    t = (1,2)

    print "a: ", a
    print "b: ", b
    print "t: ", t
    print
    print "a == b: ", a == b
    print "a != b: ", a != b
    print "hash(a) == hash(b): ", hash(a) == hash(b)
    print "a <= b: ", a <= b
    print "b <= a: ", b <= a
    print
    print "a == t: ", a == t
    print "a != t: ", a != t
    print "hash(a) == hash(t): ", hash(a) == hash(t)
    print "a <= t: ", a <= t
    print "t <= a: ", t <= a
    print
    d = {}
    d[a] = 1
    d[b] = 2
    d[t] = 3
    print "d: ", d
    s = set()
    s.add(a)
    s.add(b)
    s.add(t)
    print "s: ", s
    print
    print "tuple(x for x in a): ", tuple(x for x in a)
    print "list(a): ", list(a)
    print "tuple(a): ", tuple(a)
    print
    a0 = pickle.loads(pickle.dumps(a, 0))
    a1 = pickle.loads(pickle.dumps(a, 1))
    a2 = pickle.loads(pickle.dumps(a, 2))
    print "a0: ", a0
    print "a1: ", a1
    print "a2: ", a2
    print "a0 == a, hash(a0) == hash(a): ", a0 == a, hash(a0) == hash(a)
    print "a1 == a, hash(a1) == hash(a): ", a1 == a, hash(a1) == hash(a)
    print "a2 == a, hash(a2) == hash(a): ", a2 == a, hash(a2) == hash(a)

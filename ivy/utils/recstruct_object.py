#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This module contains recstruct - an immutable recursive data
structure (inspired by namedtuple). This implementation is based on
inheriting from Python's object.

A recstruct is defined by two lists of fields: meta_fields and
sub_fields. The meta fields contain meta-data, and the sub_fields
contain sub structures. The last sub_field can be variadic (denoted by
a name that starts with '*').

Iterating over a recstruct iterates only over its sub-structures.

Subclasses of recstruct's can set __slots__ = () to save memory.

Hash-consing can be added later as an option.

"""

import sys as _sys
from keyword import iskeyword as _iskeyword


def _init(self, *args):
    self._tup = args


def _itemgetter(x):
    return lambda self: self._tup.__getitem__(x)


_class_template = '''\
class {typename}(object):

    __slots__ = ('_tup')

    _meta_fields = {meta_field_names!r}
    _sub_fields = {sub_field_names!r}

    @classmethod
    def _preprocess_(self, *args):
        """
        Override this in subclasses to preprocess the arguments to the
        constructor.

        This is here so that code using this class doesn't care if
        it's initialized using __init__ or using __new__ (as is
        recstruct_tuple).

        """
        return args

    def __init__(self, {meta_arg_list_with_defaults}{sub_arg_list}):
        self._tup = tuple(type(self)._preprocess_({meta_arg_list}{sub_arg_list}))

    def __repr__(self):
        """Return a nicely formatted representation string"""
        return type(self).__name__ + repr(self._tup)

    def __eq__(self, other):
        return type(self) is type(other) and (self._tup) == (other._tup)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __lt__(self, other):
        return (({typename},) + self._tup) < other

    def __le__(self, other):
        return (({typename},) + self._tup) <= other

    def __gt__(self, other):
        return (({typename},) + self._tup) > other

    def __ge__(self, other):
        return (({typename},) + self._tup) >= other

    def __hash__(self):
        #return hash((type(self), ) + self._tup)
        return self._tup.__hash__()

    def _subs(self):
        return self._tup[{n_meta}:]

    def __getslice__(self, i, j):
        return self._subs().__getslice__(i, j)

    def __getitem__(self, i):
        return self._subs().__getitem__(i)

    def __iter__(self):
        return self._subs().__iter__()

    def __contains__(self, x):
        return self._subs().__contains__(x)

    def __len__(self):
        return self._subs().__len__()

    def __nonzero__(self):
        raise TypeError("recstruct should not be converted to bool")

    def __getstate__(self):
        return {{'_tup': self._tup}}

    def __setstate__(self, state):
        self._tup = state['_tup']

{field_defs}
'''

_meta_field_template = '''\
    {name} = _property(_itemgetter({index}))
'''

_sub_field_template = '''\
    {name} = _property(_itemgetter({index}))
'''

_variadic_field_template = '''\
    {name} = _property(_itemgetter(slice({index}, None)))
'''

def _preprocess_names(names):
    if isinstance(names, basestring):
        names = names.replace(',', ' ').split()
    return [str(x) for x in names]


def recstruct(typename, meta_field_names, sub_field_names, verbose=False):
    """
    Returns a new recstruct class with the requested fields.
    """

    # Validate the field names.

    meta_field_names = _preprocess_names(meta_field_names)
    meta_arg_list_with_defaults = ''.join(x + ', ' for x in meta_field_names)
    meta_field_names = [s.split('=')[0] for s in meta_field_names] #strip off default values
    meta_arg_list = ''.join(x + ', ' for x in meta_field_names)
    sub_field_names = _preprocess_names(sub_field_names)
    names = [typename] + meta_field_names
    if len(sub_field_names) > 0 and sub_field_names[-1][0] == '*':
        names += sub_field_names[:-1] + [sub_field_names[-1][1:]]
    else:
        names += sub_field_names
    for name in names:
        if not all(c.isalnum() or c=='_' for c in name):
            raise ValueError('Type names and field names can only contain '
                             'alphanumeric characters and underscores: %r' % name)
        if _iskeyword(name):
            raise ValueError('Type names and field names cannot be a '
                             'keyword: %r' % name)
        if name[0].isdigit():
            raise ValueError('Type names and field names cannot start with '
                             'a number: %r' % name)
    seen = set()
    for name in names[1:]:
        if name.startswith('_'):
            raise ValueError('Field names cannot start with an underscore: '
                             '%r' % name)
        if name in seen:
            raise ValueError('Encountered duplicate field name: %r' % name)
        seen.add(name)

    # Fill-in the class template

    n_meta = len(meta_field_names)
    sub_arg_list = ', '.join(sub_field_names)
    field_defs = '\n'.join(
        [_meta_field_template.format(index=index, name=name)
         for index, name in enumerate(meta_field_names)] +
        [_sub_field_template.format(index=index + n_meta, name=name)
         for index, name in enumerate(sub_field_names)
         if name[0] != '*'] +
        [_variadic_field_template.format(index=index + n_meta, name=name[1:])
         for index, name in enumerate(sub_field_names)
         if name[0] == '*']
     )
    class_definition = _class_template.format(
        typename=typename,
        meta_field_names=meta_field_names,
        sub_field_names=sub_field_names,
        n_meta=n_meta,
        meta_arg_list=meta_arg_list,
        meta_arg_list_with_defaults=meta_arg_list_with_defaults,
        sub_arg_list=sub_arg_list,
        field_defs=field_defs,
    )

    if verbose:
        print class_definition

    # Execute the template string in a temporary namespace and support
    # tracing utilities by setting a value for
    # frame.f_globals['__name__']

    namespace = dict(
        __name__='{}__{}'.format(__name__, typename),
        _tuple=tuple,
        _itemgetter=_itemgetter,
        _property=property,
        _init=_init,
    )
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


def record(typename, field_names, verbose=False):
    """
    Create a record like class with given field names.

    Imlemented as a recstruct with no sub-structures.
    """
    return recstruct(typename, field_names, [], verbose)


if __name__ == '__main__':
    import pickle
    from itertools import chain, product
    from os.path import isfile

    print "Testing recstruct:"
    print

    A = recstruct('A', ('x', 'y'), ('a', 'b', '*args'), verbose=True)
    class B(recstruct('B', ('x', 'y'), ('a', 'b', '*args'), verbose=False)):
        __slots__ = ()
        @classmethod
        def _preprocess_(cls, x, y, a, b, *args):
            return range(10)

    a = A(*range(10))
    b = B(None, None, None, None)
    t = tuple(range(10))

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
    print "len(a): ", len(a)
    print "0 in a: ", 0 in a
    print "10 in a: ", 10 in a
    print "5 in a: ", 5 in a
    print "a[:]: ", a[:]
    print "a[1:]: ", a[1:]
    print "a[1:-1]: ", a[1:-1]
    print "a.x: ", a.x
    print "a.y: ", a.y
    print "a.a: ", a.a
    print "a.b: ", a.b
    print "a.args: ", a.args
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

    b0 = pickle.loads(pickle.dumps(b, 0))
    b1 = pickle.loads(pickle.dumps(b, 1))
    b2 = pickle.loads(pickle.dumps(b, 2))
    b3 = pickle.loads(pickle.dumps(b))
    print "b0: ", b0, repr(b0), b0._tup
    print "b1: ", b1, repr(b1), b1._tup
    print "b2: ", b2, repr(b2), b2._tup
    print "b3: ", b3, repr(b3), b3._tup
    print "b0 == b, hash(b0) == hash(b): ", b0 == b, hash(b0) == hash(b)
    print "b1 == b, hash(b1) == hash(b): ", b1 == b, hash(b1) == hash(b)
    print "b2 == b, hash(b2) == hash(b): ", b2 == b, hash(b2) == hash(b)
    print "b3 == b, hash(b3) == hash(b): ", b3 == b, hash(b3) == hash(b)

    fn = 'test_pickle.txt'
    if isfile(fn):
        f = open(fn)
        bf = pickle.load(f)
        f.close()
        print "bf: ", bf, repr(bf), bf._tup

    f = open(fn, 'w')
    pickle.dump(b, f)
    f.close()


    class E(recstruct('E', (), (), verbose=False)):
        __slots__ = ()

    e = E()
    e0 = pickle.loads(pickle.dumps(e, 0))
    e1 = pickle.loads(pickle.dumps(e, 1))
    e2 = pickle.loads(pickle.dumps(e, 2))
    print "e0: ", e0, repr(e0), e0._tup
    print "e1: ", e1, repr(e1), e1._tup
    print "e2: ", e2, repr(e2), e2._tup

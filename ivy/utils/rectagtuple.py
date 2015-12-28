#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Immutable data structures based on Python's tuple (and inspired by
namedtuple).

Defines:
tagtuple -- A tagged variant of tuple
rectuple -- A record with named fields (a'la namedtuple)

"""


import sys as _sys
from operator import itemgetter as _itemgetter
from keyword import iskeyword as _iskeyword
from collections import OrderedDict


################################################################################
### tagtuple
################################################################################

class tagtuple(tuple):
    """
    tagtuple -- A variant of tuple that acts as a tagged immutable
    container for a sequence of elements. Instances of different
    tagtuple subclasses are are never equal. tagtuples are constracted
    from a sequence of arguments, and not from an iterable (i.e.:
    tagtuple(*range(10)) instead of tagtuple(range(10)).

    Subclasses should set __slots__ = ()
    """

    __slots__ = ()

    def __new__(cls, *args):
        """
        Create new instance of tagtuple

        tagtuples are constracted from a sequence of arguments, and
        not from an iterable. This means:

        tagtuple(range(10)) --> tagtuple with 1 element that is a list
        tagtuple(*range(10)) --> tagtuple with 10 int elements
        """
        return super(tagtuple, cls).__new__(cls, args)

    def __repr__(self):
        """Return a nicely formatted representation string"""
        return type(self).__name__ + super(tagtuple, self).__repr__()

    def __getnewargs__(self):
        """Return self as a plain tuple.  Used by copy and pickle."""
        return tuple(self)

    def __eq__(self, other):
        return type(self) is type(other) and super(tagtuple, self).__eq__(other)

    def __ne__(self, other):
        return not self.__eq__(other)

    # no need for a custom hash, as set and dict also use __eq__
    # def __hash__(self):
    #     return hash((type(self), ) + self)

    def __getslice__(self, i, j):
        return type(self)(*super(tagtuple, self).__getslice__(i, j))

    # disable many tuple methods
    __add__ = property()
    __contains__ = property() # can be implemented
    #__eq__ = property()
    #__ge__ = property()
    #__getitem__ = property()
    #__getnewargs__ = property()
    #__getslice__ = property()
    #__gt__ = property()
    #__iter__ = property()
    #__le__ = property()
    #__len__ = property()
    #__lt__ = property()
    __mul__ = property()
    #__ne__ = property()
    __rmul__ = property()
    count = property()
    index = property()


################################################################################
### rectuple
################################################################################

_class_template = '''\
class {typename}(tuple):
    '{typename}({arg_list})'

    __slots__ = ()

    _fields = {field_names!r}

    def __new__(_cls, {arg_list}):
        'Create new instance of {typename}({arg_list})'
        return _tuple.__new__(_cls, ({arg_list}))

    @classmethod
    def _make(cls, iterable, new=tuple.__new__, len=len):
        'Make a new {typename} object from a sequence or iterable'
        result = new(cls, iterable)
        if len(result) != {num_fields:d}:
            raise TypeError('Expected {num_fields:d} arguments, got %d' % len(result))
        return result

    def __repr__(self):
        'Return a nicely formatted representation string'
        return '{typename}({repr_fmt})' % self

    def _asdict(self):
        'Return a new OrderedDict which maps field names to their values'
        return OrderedDict(zip(self._fields, self))

    def _replace(_self, **kwds):
        'Return a new {typename} object replacing specified fields with new values'
        result = _self._make(map(kwds.pop, {field_names!r}, _self))
        if kwds:
            raise ValueError('Got unexpected field names: %r' % kwds.keys())
        return result

    def __getnewargs__(self):
        'Return self as a plain tuple.  Used by copy and pickle.'
        return tuple(self)

    __dict__ = _property(_asdict)

    def __getstate__(self):
        'Exclude the OrderedDict from pickling'
        pass

{field_defs}

    # the part below is different from collections.namedtuple

    __add__ = property()
    __contains__ = property()
    #__eq__ = property()
    #__ge__ = property()
    #__getitem__ = property()
    #__getnewargs__ = property()
    __getslice__ = property()
    #__gt__ = property()
    #__iter__ = property()
    #__le__ = property()
    __len__ = property()
    #__lt__ = property()
    __mul__ = property()
    #__ne__ = property()
    __rmul__ = property()
    count = property()
    index = property()

    def __eq__(self, other):
        return type(self) is type(other) and _tuple.__eq__(self, other)
    def __ne__(self, other):
        return not self.__eq__(other)
    # no real need for a custom hash, as set and dict also use __eq__
    #def __hash__(self):
    #    return hash((type(self), ) + self)

'''

_repr_template = '{name}=%r'

_field_template = '''\
    {name} = _property(_itemgetter({index:d}), doc='Alias for field number {index:d}')
'''

def rectuple(typename, field_names, verbose=False, rename=False):
    """
    Returns a new subclass of tuple that acts like a record.

    Used to represent an immutable record with named fields. Compared
    to namedtuple, it behaves less like a tuple and more like a
    record. rectuples from different classes are never equal, and they
    cannot be added or multiplied like tuples.
    """

    # Validate the field names.  At the user's option, either generate an error
    # message or automatically replace the field name with a valid name.
    if isinstance(field_names, basestring):
        field_names = field_names.replace(',', ' ').split()
    field_names = map(str, field_names)
    if rename:
        seen = set()
        for index, name in enumerate(field_names):
            if (not all(c.isalnum() or c=='_' for c in name)
                or _iskeyword(name)
                or not name
                or name[0].isdigit()
                or name.startswith('_')
                or name in seen):
                field_names[index] = '_%d' % index
            seen.add(name)
    for name in [typename] + field_names:
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
    for name in field_names:
        if name.startswith('_') and not rename:
            raise ValueError('Field names cannot start with an underscore: '
                             '%r' % name)
        if name in seen:
            raise ValueError('Encountered duplicate field name: %r' % name)
        seen.add(name)

    # Fill-in the class template
    class_definition = _class_template.format(
        typename = typename,
        field_names = tuple(field_names),
        num_fields = len(field_names),
        arg_list = repr(tuple(field_names)).replace("'", "")[1:-1],
        repr_fmt = ', '.join(_repr_template.format(name=name)
                             for name in field_names),
        field_defs = '\n'.join(_field_template.format(index=index, name=name)
                               for index, name in enumerate(field_names))
    )
    if verbose:
        print class_definition

    # Execute the template string in a temporary namespace and support
    # tracing utilities by setting a value for frame.f_globals['__name__']
    namespace = dict(_itemgetter=_itemgetter, __name__='rectuple_%s' % typename,
                     OrderedDict=OrderedDict, _property=property, _tuple=tuple)
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
    print "a + a: ", a + a
    print "a + b: ", a + b
    print "(0, ) + a: ", (0, ) + a
    print "a + (0, ): ", a + (0, )
    print "2 * a: ", 2 * a
    print "a * 2: ", a * 2
    print
    print "A(*chain((x**2 for x in range(10)), a)): ", A(*chain((x**2 for x in range(10)), a))
    print "A(*product(range(3), repeat=2)): ", A(*product(range(3), repeat=2))
    print


    print "Testing rectuple:"
    print

    A = rectuple('A', 'x y', verbose=True)
    B = rectuple('B', 'x y', verbose=True)

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

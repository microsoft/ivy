#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import string
import operator
import functools
import collections
import re
import os
import platform

# some useful combinators

def apply_func_to_list(func):
    """ return a function that applies func to a list """
    return lambda l,*args: [func(x,*args) for x in l]

def gen_list(gen,l,*args):
    """ return a generator that applies a generator to a list """
    for x in l:
        for y in gen(x,*args):
            yield y

def apply_gen_to_list(gen):
    """ return a function that returns a generator that applies a generator to a list """
    return lambda l,*args: gen_list(gen,l,*args)

def gen_list_list(gen,l,*args):
    """ return a generator that applies a generator to a list of lists"""
    for x in l:
        for z in x:
            for y in gen(z,*args):
                yield y

def apply_gen_to_list_list(gen):
    """ return a function that returns a generator that applies a generator to a list of lists """
    return lambda l,*args: gen_list_list(gen,l,*args)

def gen_to_set(gen):
    """ return a function that applies generator and returns result as a set """
    return lambda *args: set(gen(*args))

def gen_to_dict(gen):
    """ return a function that applies generator and returns result as a dict """
    return lambda *args: dict(gen(*args))

def unique(gen):
    """ given a generator, returns a generator of unique elements in
    sequence.  elements of sequence must be hashable. """
    memo = set()
    for x in gen:
        if x not in memo:
            memo.add(x)
            yield x

def gen_unique(func):
    """ Given a function returning a generator, return a function returning
    a generator of unique elements"""
    return lambda *args: unique(func(*args))

def unique2(gen):
    """ given a generator of pairs (x,y), generate one x for each value of y """
    memo = set()
    for x,y in gen:
        if y not in memo:
            memo.add(y)
            yield x

def filter2(func):
    """ Given a function of one argument returning a generator of
    pairs, return a function returning a generator of the first
    elements whose second elements match the second argument"""
    return lambda arg,value2: set(x for (x,y) in func(arg) if y == value2)

def any_in(func):
    """ Returns a function that takes set,args and returns true when func(args) contains an element of set """
    return lambda a_set,*args: any(x in a_set for x in func(*args))

# misc list funcitona

def concat(args):
    return functools.reduce(operator.add,args,[])

def unzip_append(tups):
    """ turn a list of tuples of lists into a tuple of lists """
    return (concat(x) for x in zip(*tups))

def unzip_pairs(tups):
    """ turn a list of pairs into a pair of lists """
    return zip(*tups) if tups else ([],[])

def flatten(l):
    """ flatten a generator """
    if isinstance(l,list) or isinstance(l,tuple):
        return functools.reduce(operator.add, (flatten(x) for x in l), [])
    return [l]

def union_of_list(sets):
    res = set()
    for s in sets:
        res.update(s)
    return res
    

def union_to_list(to_list,from_list):
    used = set(to_list)
    to_list += [x for x in from_list if x not in used]

def list_union(l1,l2):
    res = list(l1)
    union_to_list(res,l2)
    return res

def list_diff(l1,l2):
    """ Return set difference l1\l2. Assumes l1 and l2 are generators
    of hashable things """
    sl2 = set(l2) 
    return [s for s in l1 if s not in sl2]

def distinct_unordered_pairs(l):
    for i in range(len(l)-1):
        for j in range(i+1,len(l)):
            yield (l[i],l[j])

def inverse_map(m):
    return dict((y,x) for x,y in m.iteritems())

def compose_maps(m1,m2):
    """ compose two maps as functions. a map is assumed to be the identity for keys not present """
    res = m2.copy()
    res.update((x,m2.get(y,y)) for x,y in m1.iteritems())
    return res

def partition(things,key):
    res = collections.defaultdict(list)
    for t in things:
        res[key(t)].append(t)
    return res

# split a l list into a pair of lists (lp,1n) such that lp has the
# elements of l satisfying predicate p and ln has the rest.

def split_list(l,p):
    pl = [p[x] for x in l]
    return ([x for x,c in zip(l,pl) if c],
            [x for x,c in zip(l,pl) if not c])

# unique name generation

def constant_name_generator():
    """ generate names begining with lowercase latters """
    for c in string.ascii_lowercase:
        yield c
    i = 0
    while True:
        for c in string.ascii_lowercase:
            yield c + str(i)
        i += 1


def unused_name_with_base(base,used_names):
    """Return an unused name starting with "base"
    """
    for suffix in constant_name_generator():
        name = base + '_' + suffix
        if name not in used_names:
            return name
    

class UniqueRenamer(object):
    def __init__(self,prefix='',used=[]):
        self.prefix, self.used = prefix, set(str(s) for s in used)
    def __call__(self,name = ''):
        thing = self.prefix+name
        if name != '' and thing not in self.used:
            res = thing
        else:
            res = unused_name_with_base(thing,self.used)
        self.used.add(res)
        return res

def distinct_renaming(names1,names2):
    rn = UniqueRenamer('',names2)
    return dict((s,rn(s)) for s in names1)

def distinct_obj_renaming(names1,names2):
    rn = UniqueRenamer('',names2)
    return dict((s,s.rename(rn)) for s in names1)

class VariableGenerator(object):
    def __init__(self):
        self.used = set()
    def __call__(self,name = ''):
        nchars = 1
        firstchar = name[0].upper() if name else 'A'
        while True:
            while firstchar <= 'Z':
                guess = nchars * firstchar
                if firstchar != 'O' and guess not in self.used:
                    self.used.add(guess)
                    return guess
                firstchar = chr(ord(firstchar) + 1)
            firstchar = 'A'
            nchars += 1


class SourceFile(object):
    """ Context Manager that temporarily sets values of parameters by
    name.  See class "Parameter".
    """

    def __init__(self,fname):
        self.fname = fname

    def __enter__(self):
        global filename
        self.oldf = filename
        filename = self.fname
        return self

    def __exit__(self,exc_type, exc_val, exc_tb):
        global filename
        filename = self.oldf
        return False # don't block any exceptions

filename = None

class WorkingDir(object):
    """ Context Manager that temporarily sets the working directory.
    """

    def __init__(self,fname):
        self.fname = fname

    def __enter__(self):
        self.oldf = os.getcwd()
        os.chdir(self.fname)
        return self

    def __exit__(self,exc_type, exc_val, exc_tb):
        os.chdir(self.oldf)
        return False # don't block any exceptions


def Location(filename=None,line=None):
    return LocationTuple([filename,line])

class LocationTuple(tuple):
    @property
    def filename(self):
        return self[0]
    @property
    def line(self):
        return self[1]
    def __str__(self):
        if platform.system() == 'Windows':
            res =  (((str(self.filename)) if self.filename else '')
                    + ('(' + str(self.line) + ')') if self.line else '')
            if res:
                res += ': '
        else:
            res = ''
            if self.filename:
                res += str(self.filename) + ': '
            if self.line:
                res += 'line ' + str(self.line) + ': '
        return res

def lineno_str(ast):
    if not hasattr(ast,'lineno'):
        return ''
    r = str(ast.lineno)
    if r.endswith(': '):
        r = r[:-2]
    return r

class IvyError(Exception):
    def __init__(self,ast,msg):
        self.lineno = ast.lineno if hasattr(ast,'lineno') else Location()
        self.msg = msg
        if not catch.get():
            print str(self)
            assert False
    def __str__(self):
        return str(self.lineno) + 'error: ' + self.msg
    def __repr__(self):
        return str(self)

class IvyUndefined(IvyError):
    def __init__(self,ast,name):
#        assert False
        super(IvyUndefined,self).__init__(ast,"undefined: " + name)

def warn(ast,msg):
    print str(IvyError(ast,msg)).replace('error: ','warning: ')

# This module provides a generic parameter mechanism similar to
# "parameterize" in racket. 
#
# A parameter is an object with set and get methods. Modules register
# their parameters with string names, like this:
#
# >>> my_param = Parameter("my_param",default_value)
#
# The initial value of "my_param" can be overriden in config.py.
#
# To set the values of some parameters during execution of function foo,
# do this:
#
# >>> with parameterize.parameterize({param1:value1, param2:value2,...}):
# >>>     foo()
#
# Values of the parameters will be returned to their original values on
# termination of foo, even by an exception. Currently this is not
# thread-safe, however.
#
# To set the value of a parameter permanently, do this:
#
# >>> parameterize.set_parameters({param1:value1, param2:value2,...})
#
# This should only be done when initializing the program, for example,
# when reading command line options. Elsewhere you should always use
# "parameterize" to avoid side effects on later computations.
#
# A module gets the value of a parameter like this:
#
# >>> current_param_value = my_param.get()
#

registry = dict()

class Parameter(object):
    """ A named object holding a value that can be set temporarily by
    "parameterize". 

    >>> foo = Parameter("foo",True)
    >>> print foo.get()
    True
    >>> with parameterize({"foo":False}):
    >>>    print foo.get()
    False
    >>> print foo.get()
    True

    """

    def __init__(self,key,init_val=None,check=lambda s:True,process=lambda s:s):
        global registry
        self.value = init_val
        self.check = check
        self.process = process
        self.key = key
        self.callback = lambda x:None
        assert key not in registry
        registry[key] = self

    def get(self):
        return self.value

    def set(self,new_val):
        if not self.check(new_val):
            raise IvyError(None,"bad parameter value: {}={}".format(self.key,new_val))
        self.value = self.process(new_val)
        self.callback(self.value)

    def __nonzero__(self):
        return True if self.value else False

    def set_callback(self,callback):
        self.callback = callback

class BooleanParameter(Parameter):
    """ Parameter that takes "true" for True and "false" for False """
    def __init__(self,key,init_val=None):
        Parameter.__init__(self,key,init_val,
                           check = lambda s: (s == "true" or s == "false"),
                           process = lambda s: s == "true")

class EnumeratedParameter(Parameter):
    """ Parameter that takes "true" for True and "false" for False """
    def __init__(self,key,vals,init_val=None):
        Parameter.__init__(self,key,init_val,
                           check = lambda s, vals=vals: (s in vals),
                           process = lambda s: s)
    


def set_parameters(values):
    global registry
    for key in values:
        if key not in registry:
            raise IvyError(None,"parameter {} undefined".format(key))
        param = registry[key]
        param.set(values[key])

class parameterize(object):
    """ Context Manager that temporarily sets values of parameters by
    name.  See class "Parameter".
    """

    def __init__(self,values):
        self.new_values = values

    def __enter__(self):
        global registry
        self.old_values = dict()
        for key in self.new_values:
            assert key in registry
            param = registry[key]
            self.old_values[key] = param.get()
            param.set(self.new_values[key])
        return self

    def __exit__(self,exc_type, exc_val, exc_tb):
        global registry
        for key in self.old_values:
            param = registry[key]
            param.set(self.old_values[key])
        return False # don't block any exceptions

def pairs_to_dict(pairs,key=lambda x:x):
    d = collections.defaultdict(list)
    for x,y in pairs:
        d[key(x)].append(y)
    return d

def dict_to_pairs(d):
    return [(x,y) for x,l in d.iteritems() for y in l]

def topological_sort(items,order,key=lambda x:x):
    """ items is a list, key maps list elements to hashable keys,
    order is a set of pairs of items representing a pre-order.  Returns a
    permutation of items respecting the order."""
    m,s,l,d = pairs_to_dict(order,key),list(items),[],set()
    while len(s) > 0:
        i = s.pop()
        k = key(i)
        if not k in d:
            if k in m:
                s.append(i)
                s.extend(x for x in m[k] if key(x) != k)
                del m[k]
            else:
                d.add(k)
                l.append(i)
    return list(reversed(l))

def reachable(items,iter_succ,key=lambda x:x):
    """ items is a list, key maps list elements to hashable keys,
    order is a set of pairs of items representing a pre-order.  Returns a
    list of descendants of items."""
    m,s,l,d = set(),list(items),[],set()
    while len(s) > 0:
        i = s.pop()
        k = key(i)
        if not k in d:
            if k not in m:
                s.append(i)
                s.extend(x for x in iter_succ(k) if key(x) != k)
                m.add(k)
            else:
                d.add(k)
                l.append(i)
    return list(reversed(l))


def cycle(arcs,first=lambda x:x[0],second=lambda x:x[1]):
    """ finds a cycle of arcs in a graph. first maps arcs to
    hashable tails, second maps arcs to hashable heads.
    returns a list of arcs forming a cycle, or None. """
    m = collections.defaultdict(set)
    for arc in arcs:
        m[first(arc)].add(arc)
    heap = set()
    stack = set()
    path = []
    def dfs(node):
        if node not in heap:
            if node in stack:
                return True
            stack.add(node)
            for arc in m[node]:
                if dfs(second(arc)):
                    path.append(arc)
                    return True
            stack.remove(node)
            heap.add(node)
            return False
    for arc in arcs:
        if dfs(first(arc)):
            end = second(path[0])
            fpath = []
            for arc in path:
                fpath.append(arc)
                if first(arc) == end:
                    return reversed(fpath)
            assert False
    return None


class ErrorPrinter(object):
    """ Context Manager that handles exceptions and reports errors. """
    def __init__(self):
        pass
    def __enter__(self):
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        if exc_type == IvyError or isinstance(exc_val,IvyError):
            print str(exc_val)
            exit(1)
            return True
        return False # don't block any other exceptions

# handling parsing errors


class ErrorList(IvyError):
    def __init__(self,errors):
        self.errors = errors
    def __repr__(self):
        pre = (self.filename + ': ') if hasattr(self,'filename') else ''
        return '\n'.join((repr(e) if hasattr(e,'filename') else pre + str(e)) for e in self.errors)
    __str__ = __repr__


def parse_with(s,parser,lexer):
    global error_list
    error_list = []
    res = parser.parse(s,lexer=lexer)
    if error_list:
        raise ParseErrorList(error_list)
    return res

def p_error(token):
    if token is not None:
        report_error(ParseError(token.lineno,token.value,"syntax error"))
    else:
        report_error(ParseError(None,None,'unexpected end of input'));

# the default language version is the latest
ivy_latest_language_version = '1.7'
ivy_language_version = ivy_latest_language_version
ivy_compose_character = '.'
ivy_have_polymorphism = True
ivy_use_polymorphic_macros = False
ivy_forbid_ghost_init = False

def set_string_version(version):
    global ivy_language_version
    global ivy_compose_character
    global ivy_have_polymorphism
    global ivy_use_polymorphic_macros
    ivy_language_version = version
    ivy_compose_character = ':' if get_numeric_version() <= [1,1] else '.'
    ivy_have_polymorphism = not get_numeric_version() <= [1,2]
    ivy_use_polymorphic_macros = not get_numeric_version() <= [1,5]
    ivy_forbid_ghost_init = not get_numeric_version() <= [1,6]
    
def get_string_version():
    return ivy_language_version

def string_version_to_numeric_version(v):
    return map(int,string.split(v,'.'))

def get_numeric_version():
    return string_version_to_numeric_version(ivy_language_version)

def version_le(v1,v2):
    return string_version_to_numeric_version(v1) <= string_version_to_numeric_version(v2)

inc_dir_pat = re.compile(r'[0-9]*\.[0-9]*')

def get_std_include_dir():
    inc_base_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)),'include')
    inc_dir = None
    for d in os.listdir(inc_base_dir):
        m = inc_dir_pat.match(d)
        if (m and m.end() == len(d) and
              version_le(ivy_language_version,d) and (inc_dir is None or version_le(d,inc_dir))):
            inc_dir = d
    if inc_dir is None:
        raise IvyError(None,'cannot find standard library for language version {}'.format(ivy_language_version))
    return os.path.join(inc_base_dir,inc_dir)

def compose_names(*names):
    if names[0] == 'this':
        return ivy_compose_character.join(names[1:])
    return ivy_compose_character.join(names)

def split_name(name):
    return name.split(ivy_compose_character)

def base_name(name):
    return split_name(name)[0]

def parent_child_name(name):
    parts = name.rsplit(ivy_compose_character,1)
    if len(parts) == 2:
        return parts
    return ['this',name]

def extract_parameters_name(name):
    parms = []
    pos = len(name) - 1
    while pos >= 0 and name[pos] == ']':
        end = pos
        pos -= 1
        count = 1
        while pos >= 0 and count > 0:
            if name[pos] == '[':
                count -= 1
            elif name[pos] == ']':
                count += 1
            pos -= 1
        if pos >= 0:
            parms.append(name[pos+2:end])
    if pos >= 0:
        parms.reverse()
        return (name[:pos+1],parms)
    # name is malformed, just return it
    return (name,[])

def add_params_name(name,parms):
    return name + ''.join(('[' + p + ']') for p in parms) 

def pretty(s,max_lines=None):
    lines = s.replace(';',';\n').replace('{','{\n').replace('}','\n}').split('\n')
    lines = [s.strip() for s in lines]
    if max_lines != None and len(lines) > max_lines:
        lines = lines[0:max_lines-1]
        lines.append('...')
    indent = 0
    res = []
    for line in lines:
        if '}' in line:
            indent -= 1
        res.append(indent * '    ' + line)
        if '{' in line:
            indent += 1
    return '\n'.join(res) + indent * '}'

polymorphic_symbols = set(
    ['<',
    '<=',
    '>',
    '>=',
    '+',
    '*',
    '-',
    '/',
    '*>',
     'bvand',
     'bvor',
     'bvnot',
    ]
)

use_numerals = BooleanParameter("use_numerals",True)
use_new_ui = BooleanParameter("new_ui",False)
catch = BooleanParameter("catch",True)

default_ui = Parameter("ui","art")

def get_default_ui_module():
    defui = default_ui.get()
    if defui == "art":
        defui = 'ivy_ui'
#        return sys.modules[__name__]
    else:
        defui = 'ivy_ui_' + defui
    prefix = ''.join(x + '.' for x in __name__.split('.')[:-1])
    module = __import__(prefix+defui)
    return module.__dict__[defui] if prefix else module
    
def get_default_ui_class():
    mod = get_default_ui_module()
    return mod.IvyUI

def get_default_ui_compile_kwargs():
    mod = get_default_ui_module()
    return mod.compile_kwargs
    

enable_debug = BooleanParameter("debug",False)

def dbg(*exprs):
    """Print expressions evaluated in the caller's frame."""
    assert enable_debug,"must use debug=true to enable debug output"
    import inspect
    frame = inspect.currentframe()
    try:
        locs = frame.f_back.f_locals
        globs = frame.f_back.f_globals
        for e in exprs:
            print "{}:{}".format(e,eval(e,globs,locs))
    finally:
        del frame


def parse_int_subscripts(name):
    things = name.split('[')
    thy = things[0]
    things = things[1:]
    if not all(t.endswith(']') for t in things):
        raise iu.IvyError(None,'bad subscript syntax: {}'.format(name))
    prms = [int(t[:-1]) for t in things]
    return thy,prms

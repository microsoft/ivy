#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This module is a wrapper around ivy2's logic representation for
copmpatibility with ivy1 code.

Ivy1 uses a sorted first-order logic.

Constants (both first and second-order) are represented by class
Symbol. Variables are represented by class Variable. Instances of both
classes are distinguished by string names. Note: in the surface syntax
of Ivy, variables are distinguished from constants by having initial
capitals, but there is no such distinction made in AST's.

A Symbol of Variables has a Sort. Symbols and Variables of distinct
sorts are considered distinct (TODO: hashing and equalit testing on
symbols will be faster if names are required to be
unique). First-order sorts are subclasses of ConstantSort, while
second-order sorts are subclasses of FunctionSort.  Relation sorts
have range sort BooleanSort. There is a distinction between a
ConstantSort S and a 0-ary FunctionSort of range S. The first-order
sorts are uniquely identified by string names.

TODO: ivy used a separate RelationSort class. All occurrences of the
pattern isinstance(X,[RelationSort,FunctionSort]) will need attention.

Symbols whose names begin with a digit are *numerals*. Numerals always
have a sort of class ConstantSort, but are not declared in the
signature. In the surface syntax, a numeral without a sort field is
given the default numeric sort, which is fixed in the signature.

A *term* is represented by class Term and is either a constant, a
variable or a second-order constant applied to zero or more term
arguments. All AST nodes have a property "args" that is a list of AST
nodes. For constants and variables, args is empty, while for
applications (class App) args is the list of arguments the constant
symbol is applied to (but does not include the applied symbol itself).

TODO: extracting "args" is linear time for applications, since we must
extract all but the first element of ivy2's term list. We should
either cache it, or fix the code to expect ivy2's represenation.

Terms have a method get_sort that computes the term's sort (for an
application, the range of the applied symbol's sort).

TODO: Symbols of sort TopSort in Ivy1 were represented using str. This
has to change.

TODO: There is no longer any sort Atom for applications of
relation. The constructor can be aliased to App, but we must fix any
other uses of type Atom.

An *enumerated* sort S is a ConsantSort with a set of constants of
sort S that act as its constructors (in other words, distinct
constructors are never equal).

Since logical terms and sorts must act as Ivy AST nodes, the must also
implement the "clone" method which copys the objeect replacing
args. This is a bit tricky since for Apps, clone must replace ony the
args and not applied symbol.

"""

from ivy_utils import flatten, IvyError
import ivy_utils as iu
import logic as lg
import logic_util as lu
from logic import And,Or,Not,Implies,Iff,Ite,ForAll,Exists
from type_inference import concretize_sorts
from collections import defaultdict
from itertools import chain

allow_unsorted = False
repr = str

class UnsortedContext(object):
    """ Allow unsorted symbols. Useful for parsing.
    """
    def __init__(self):
        pass
    def __enter__(self):
        global allow_unsorted
        self.old_allow_unsorted = allow_unsorted
        allow_unsorted = True
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global allow_unsorted
        allow_unsorted = self.old_allow_unsorted
        return False # don't block any exceptions

class top_sort_as_default(object):
    """ Context in which TopSort is the default sort
    """
    def __init__(self):
        pass
    def __enter__(self):
        global sig
#        print "setting topsort as default"
        self.old_default_sort = sig.sorts.get('S',None)
        sig.sorts['S'] = lg.TopS
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global sig
        if self.old_default_sort is not None:
            sig.sorts['S'] = self.old_default_sort
        else:
            del sig.sorts['S']
        return False # don't block any exceptions

Symbol = lg.Const

Symbol.rep = property(lambda self: self)
Symbol.relname = property(lambda self: self)

# this is just not needed, as it is implemented exactly the same
# in logic.py
#Symbol.__str__ = lambda self: self.name

# the following two lines cause bugs when converting to Z3 and
# when caching in general, since they make constants with the same
# name but with different sorts equal, and the code relies on the fact
# that they are different. Do we really need this behavior?
#Symbol.__hash__ = lambda self: hash(self.name)
#Symbol.__eq__ = lambda self,other: (type(self) == type(other) and self.name == other.name)

Symbol.rename = lambda self,rn: Symbol(rn(self.name),self.sort)
Symbol.prefix = lambda self,s:  Symbol(s+self.name,self.sort)
Symbol.startswith = lambda self,s: self.name.startswith(s)
Symbol.suffix = lambda self,s: Symbol(self.name+s,self.sort)
Symbol.endswith = lambda self,s: self.name.endswith(s)
Symbol.drop_prefix = lambda self,s: Symbol(self.name[len(s):],self.sort)
Symbol.drop_suffix = lambda self,s: Symbol(self.name[0,-len(s)],self.sort)
Symbol.contains = lambda self,s: (s in self.name)
Symbol.skolem = lambda self: self.prefix('__')
Symbol.is_skolem = lambda self: self.contains('__')
Symbol.deskolem = lambda self,s: self.drop_prefix('__')
Symbol.__call__ = lambda self,*args: App(self,*args) if len(args) > 0 or isinstance(self.sort,FunctionSort) else self
Symbol.is_relation = lambda self: isinstance(self.sort.rng,lg.BooleanSort)
Symbol.args = property(lambda self : [])
Symbol.is_numeral  = lambda self : self.name[0].isdigit() or self.name[0] == '"'
Symbol.clone = lambda self,args : self

BooleanSort = lg.BooleanSort

class AST(object):
    """
    Base class for abstract syntax.
    """
    def clone(self,args):
       return type(self)(*args)
#
#    def __eq__(self,other):
#        return type(self) == type(other) and self.args == other.args

def nary_repr(op,args):
    res = (' ' + op + ' ').join([repr(a) for a in args])
    return ('(' + res + ')') if len(args) > 1 else res

class Let(AST):
    """
    Formula of the form let p(X,...,Z) <-> fmla[X,...,Z], ... in fmla
    """
    def __init__(self,*args):
        assert len(args) >= 1
        self.args = args
    def __str__(self):
        res = str(self.args[-1])
        if len(self.args) > 1:
            res = 'let ' + ', '.join([str(x) for x in self.args[0:-1]]) + ' in ' + res
        return res

class Some(AST):
    def __init__(self,*args):
        assert len(args) >= 2
        self.args = args
    def __str__(self):
        res = 'some ' + str(self.args[0]) + '. ' + str(self.args[1])
        if len(self.args) >= 3:
            res += ' in ' + str(self.args[2])
        if len(self.args) >= 4:
            res += ' else ' + str(self.args[3])
        return res
    def params(self):
        return [self.args[0]]
    def fmla(self):
        return self.args[1]
    def if_value(self):
        return self.args[2] if len(self.args) == 4 else None
    def else_value(self):
        return self.args[3] if len(self.args) == 4 else None


class Definition(AST):
    """
    Formula of the form p(X,...,Z) <-> fmla[X,...,Z]
    """
    def __init__(self,*args):
        assert len(args) == 2
        self.args = args
    def __str__(self):
        return ' = '.join([repr(x) for x in self.args])
    def defines(self):
        return self.args[0].rep
    def to_constraint(self):
        if isinstance(self.args[1],Some):
            if self.args[1].if_value() != None:
                return And(Implies(self.args[1].args[1],
                                   lg.Exists([self.args[1].args[0]],
                                             And(self.args[1].args[1],Equals(self.args[0],self.args[1].if_value())))),
                           Or(lg.Exists([self.args[1].args[0]],self.args[1].args[1]),
                              Equals(self.args[0],self.args[1].else_value())))
            return lg.ForAll([self.args[1].args[0]],
                             Implies(self.args[1].args[1],
                                     lu.substitute(self.args[1].args[1],{self.args[1].args[0]:self.args[0]})))
        if is_individual(self.args[0]):
            return Equals(*self.args)
        return Iff(*self.args)
    @property
    def sort(self):
        return lg.Boolean


                

lg_ops = [lg.Eq, lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff, lg.Ite, lg.ForAll, lg.Exists]

for cls in lg_ops:
    cls.args = property(lambda self: [ a for a in self])
    cls.clone = lambda self,args: type(self)(*args)

for cls in [lg.ForAll, lg.Exists]:
    cls.clone = lambda self,args: type(self)(self.variables,*args)

lg.Apply.clone = lambda self,args: type(self)(self.func, *args)
lg.Apply.args = property(lambda self: self.terms)
lg.Apply.rep = property(lambda self: self.func)
lg.Apply.relname = property(lambda self: self.func)

for cls in [lg.Apply] + lg_ops:
    cls.is_numeral = lambda self: False

def is_numeral(term):
    return isinstance(term,Symbol) and term.is_numeral()

for cls in [lg.Const, lg.Var, lg.Apply]:
    cls.get_sort = lambda self: self.sort

lg.Eq.rep = property(lambda self: equals)

App = lg.Apply
def Atom(rel,args):
    return Equals(*args) if rel == equals else lg.Apply(rel,*args) if args else rel

def is_atom(term):
    return (isinstance(term,App) or isinstance(term,Symbol)) and term.sort == lg.Boolean or isinstance(term,lg.Eq)

# note: ivy1 treats instances of a constant in a formula as an app
def is_app(term):
    return isinstance(term,App) or isinstance(term,lg.Const)

def is_rel_app(term):
    return isinstance(term,App) and term.rep.is_relation()

def _find_sort(type_name):
    if allow_unsorted:
        if type_name == 'S': return lg.TopS
        return lg.UninterpretedSort(type_name)
    try:
        return sig.sorts[type_name]
    except KeyError:
        if type_name == 'S':
            if iu.get_numeric_version() <= [1,2]:
                return default_sort()
            raise IvyError(None,"unspecified type")
        raise IvyError(None,"unknown type: {}".format(type_name))

def find_sort(type_name):
    res = _find_sort(type_name)
#    print "sort {!r} = {!r}".format(type_name,res)
    return res

def add_sort(sort):
    if sort.name in sig.sorts:
        IvyError(None,"redefinition of sort {}".format(sort_name))
    sig.sorts[sort.name] = sort

def find_symbol(symbol_name):
    if allow_unsorted:
        return Symbol(symbol_name,lg.TopS)
    try:
#        print "find symbol: {!r}".format(symbol_name)
        s = sig.symbols[symbol_name]
#        print "find symbol: {} : {}".format(s,s.sort)
        return sig.symbols[symbol_name]
    except KeyError:
        if symbol_name == '=':
            return equals
        raise IvyError(None,"unknown symbol: {}".format(symbol_name))

def find_polymorphic_symbol(symbol_name):
    if iu.ivy_have_polymorphism and symbol_name in polymorphic_symbols:
        return polymorphic_symbols[symbol_name]
    if symbol_name[0].isdigit() or symbol_name[0] == '"':
        return Symbol(symbol_name,alpha)
    return find_symbol(symbol_name)

def normalize_symbol(symbol):
    if iu.ivy_use_polymorphic_macros and symbol.name in polymorphic_macros_map:
        return Symbol(polymorphic_macros_map[symbol.name],symbol.sort)
    return symbol

class UnionSort(object):
    def __init__(self):
        self.sorts = []
    def __str__(self):
        return "UnionSort(" + ','.join(map(str,self.sorts)) + ")"

def add_symbol(symbol_name,sort):
#    print "add symbol: {} : {}".format(symbol_name,sort)
    if iu.ivy_have_polymorphism and symbol_name in polymorphic_symbols:
        if symbol_name not in sig.symbols:
            sig.symbols[symbol_name] = Symbol(symbol_name,UnionSort())
        u = sig.symbols[symbol_name].sort
        if sort not in u.sorts:
            u.sorts.append(sort)
        return Symbol(symbol_name,sort)
    elif symbol_name in sig.symbols:
        if sort != sig.symbols[symbol_name].sort:
            raise IvyError(None,"redefining symbol: {}".format(symbol_name))
    else:
        sig.symbols[symbol_name] = Symbol(symbol_name,sort)
    return sig.symbols[symbol_name]

def remove_symbol(symbol):
    sig.remove_symbol(symbol)

def all_symbols():
    return sig.all_symbols()

def get_sort_term(term):
    if hasattr(term,'sort'):
        return term.sort
    return term.rep.sort.rng

def is_qf(term):
    if is_quantifier(term):
        return False
    return all(is_qf(t) for t in term.args)

def is_prenex_universal(term):
    if isinstance(term,lg.ForAll):
        return is_prenex_universal(term.body)
    if isinstance(term,lg.Not):
        return is_prenex_existential(term.args[0])
    return is_qf(term)

def is_prenex_existential(term):
    if isinstance(term,lg.Exists):
        return is_prenex_existential(term.body)
    if isinstance(term,lg.Not):
        return is_prenex_universal(term.args[0])
    return is_qf(term)

def drop_universals(term):
    if isinstance(term,lg.ForAll):
        return drop_universals(term.body)
    if isinstance(term,lg.Not):
        return lg.Not(drop_existentials(term.args[0]))
    if isinstance(term,lg.And) and len(term.args) == 1:
        return drop_universals(term.args[0])
    return term

def drop_existentials(term):
    if isinstance(term,lg.Exists):
        return drop_existentials(term.body)
    if isinstance(term,lg.Not):
        return lg.Not(drop_universals(term.args[0]))
    return term

def is_alternation_free(term):
    return is_prenex_universal(term) or is_prenex_existential(term) and not lu.free_variables(term)

def is_ae(term):
    if isinstance(term,lg.ForAll):
        return is_ae(term.body)
    if isinstance(term,lg.Exists):
        return is_prenex_existential(term.body)
    if isinstance(term,lg.Not):
        return is_ea(term.args[0])
    return is_qf(term)

def is_ea(term):
    if isinstance(term,lg.Exists):
        return is_ea(term.body)
    if isinstance(term,lg.ForAll):
        return is_prenex_universal(term.body)
    if isinstance(term,lg.Not):
        return is_ae(term.args[0])
    return is_qf(term)

logics = ["epr","qf"]

def subterms(term):
    yield term
    for a in term.args:
        for b in subterms(a):
            yield b

def seg_var_pat(t):
    return ((x if isinstance(x,lg.Var) else None) for x in t.args)

def is_segregated(fmla):
    fmla = drop_existentials(fmla)
    vs = lu.used_variables(fmla)
    apps = list(t for t in subterms(fmla) if isinstance(t,lg.Apply) and lu.used_variables(t))
    byname = iu.partition(apps,lambda self:self.func.name)
    for name,terms in byname.iteritems():
        pat = seg_var_pat(terms[0])
        pvs = set(x for x in pat if x != None)
        if pvs != vs:
            reason_text = "{} is not segrated (not all variables appear)".format(name)
            return False
        for t in terms[1:]:
            if seg_var_pat(t) != pat:
                reason_text = "{} is not segrated (variable positions differ)".format(name)
                return False
    return True
            
def reason():
    global reason_text
    return reason_text

def is_in_logic(term,logic,unstrat = False):
    global reason_text
    assert logic in logics
    if logic == "epr":
        # ok = (is_prenex_universal(term)
        #       if lu.free_variables(term) else is_ea(term))
        # if not ok:
        #     reason_text = "of quantifier alternation"
        #     return False
        cs = lu.used_constants(term)
        for s in cs:
            if s.name in sig.interp:
                reason_text = "'{}' is iterpreted".format(s)
                return False
        if unstrat:
            reason_text = "functions are not stratified"
            return False
            
            if not is_segregated(term):
                reason_text = "formula is unsegregated"
                return False
        return True
    elif logic == "qf":
        return is_qf(term)


def Constant(sym):
    return sym # first-order constants are not applied in ivy2

def is_forall(term):
    return isinstance(term,lg.ForAll)

def is_exists(term):
    return isinstance(term,lg.Exists)

def is_quantifier(term):
    return isinstance(term,lg.ForAll) or isinstance(term,lg.Exists)

def quantifier_vars(term):
    return term.variables

def quantifier_body(term):
    return term.body

def is_epr_rec(term,uvars):
    if is_forall(term):
        return is_epr_rec(term.body,frozenset.union(uvars,term.variables))
    if is_exists(term):
        if frozenset.intersection(lu.free_variables(term),uvars):
            return False
        return is_epr_rec(term.body,frozenset())
    return all(is_epr_rec(a,uvars) for a in term.args)

def is_epr(term):
    return is_epr_rec(term,lu.free_variables(term))

def variables(sorts):
    return [Variable('V'+str(idx),s) for idx,s in enumerate(sorts)]

def extensionality(destrs):
    if not destrs:
        return Or()
    c = []
    sort = destrs[0].sort.dom[0]
    x,y = Variable("X",sort),Variable("Y",sort)
    for d in destrs:
        vs = variables(d.sort.dom[1:])
        eqn = Equals(d(*([x]+vs)),d(*([y]+vs)))
        if vs:
            eqn = lg.ForAll(vs,eqn)
        c.append(eqn)
    res = Implies(And(*c),Equals(x,y))
    return res
    
Variable = lg.Var
Variable.args = property(lambda self: [])
Variable.clone = lambda self,args: self
Variable.rep = property(lambda self: self.name)
Variable.__call__ = lambda self,*args: App(self,*args) if isinstance(self.sort,FunctionSort) else self
Variable.rename = lambda self,name: Variable(name,self.sort)

    
class Literal(AST):
    """
    Either a positive or negative atomic formula. Literals are not
    formulas! Use Not(Atom(...)) to get a formula.
    """
    def __init__(self, polarity, atom):
#        assert isinstance(atom,Atom) or isinstance(atom,And) and len(atom.args) == 0
        self.polarity = polarity
        self.atom = atom
    def __repr__(self):
        return "Literal({!r},{!r})".format(self.polarity,self.atom)
    def __str__(self):
        return ('~' if self.polarity == 0 else '') + str(self.atom)
    def __invert__(self):
        """
        x.__invert__() <==> ~x
        Used to negate the a literal.
        """
        return Literal(1 - self.polarity, self.atom)
    def clone(self,args):
        return Literal(self.polarity,*args)
    def __eq__(self,other):
        return type(self) == type(other) and self.polarity == other.polarity and self.args == other.args
    @property
    def args(self):
        return [self.atom]
    @args.setter
    def args(self,value):
        assert len(value) == 1
        self.atom = value[0]

def _eq_lit(x, y):
    return Literal(1, Atom(equals, (x, y)))
def _neq_lit(x, y):
    return Literal(0, Atom(equals, (x, y)))


class Predicate(object):
    """
    A predicate is a literal factory. It's not an AST object.
    """
    def __init__(self, name, arity):
        self.name = name
        self.arity = arity
    def __call__(self, *terms):
        assert len(terms) == self.arity
        return Literal(1, Atom(self.name, terms))


ConstantSort = lg.UninterpretedSort
ConstantSort.rng = property((lambda self: self))
ConstantSort.dom = property((lambda self: []))
ConstantSort.defines = lambda self: []
ConstantSort.rep = property(lambda self: self.name)

UninterpretedSort = ConstantSort
UninterpretedSort.is_relational = lambda self: False

EnumeratedSort = lg.EnumeratedSort

EnumeratedSort.defines = lambda self: self.extension
EnumeratedSort.is_relational = lambda self: False
EnumeratedSort.dom = property(lambda self: [])
EnumeratedSort.rng = property(lambda self: self)

# class EnumeratedSort(object):
#     def __init__(self,name,extension):
#         self.name = name
#         self.extension = extension
#         self.rng = self
#         self.dom = []
#     def __str__(self):
#         return '{' + ','.join(self.extension) + '}'
#     def __hash__(self):
#         return hash(tuple(self.extension))
#     def defines(self):
#         return self.extension
#     @property
#     def constructors(self):
#         return [Symbol(n,self) for n in extension]
#     def __iter__(self):  # make it iterable so it pretends to be an actual sort
#         return self
#     def next(self): # Python 3: def __next__(self)
#         raise StopIteration
#     @property
#     def card(self):
#         return len(self.extension)
#     def is_relational(self):
#         return False

FunctionSort = lg.FunctionSort
FunctionSort.rng = FunctionSort.range
FunctionSort.dom = FunctionSort.domain
FunctionSort.defines = lambda self: []
FunctionSort.is_relational = lambda self: self.rng == lg.Boolean

lg.BooleanSort.is_relational = lambda self: True
lg.BooleanSort.rng = property(lambda self: self)
lg.BooleanSort.dom = property(lambda self: [])


def is_enumerated_sort(s):
    return isinstance(s,EnumeratedSort)

def is_boolean_sort(s):
    return s == lg.Boolean

def is_boolean(term):
    return term.sort == lg.Boolean

# TODO: arguably boolean and enumerated are first-order sorts
def is_first_order_sort(s):
    return isinstance(s,UninterpretedSort)

def RelationSort(dom):
    return FunctionSort(*(list(dom) + [lg.Boolean])) if len(dom) else lg.Boolean

def TopFunctionSort(arity):
    if arity == 0:
        return lg.TopSort('alpha')
    res = FunctionSort(*[lg.TopSort('alpha{}'.format(idx)) for idx in range(arity+1)])
    return res
    
TopS = lg.TopS

def apply(symbol,args):
    return App(symbol,*args)

def sortify(ast):
    args = [sortify(arg) for arg in ast.args]
    if (isinstance(ast,App)) and isinstance(ast.rep.sort,lg.TopSort):
        return apply(find_symbol(ast.rep),args)
    return ast.clone(args)

# Signatures

class Sig(object):
    """ First-order signature """
    def __init__(self):
        self.sorts = {}
        self.symbols = dict()
        self.constructors = set()
        self.interp = {}
        self._default_sort = None
        self.default_numeric_sort = ConstantSort("int")
        self.sorts["bool"] = RelationSort([])
    def __enter__(self):
        global sig
        self.old_sig = sig
        sig = self
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global sig
        sig = self.old_sig
        return False # don't block any exceptions
    def copy(self):
        res = Sig()
        res.sorts = dict(self.sorts)
        res.symbols = dict(self.symbols)
        res.constructors = set(self.constructors)
        res.interp = dict(self.interp)
        res._default_sort = self._default_sort
        res.default_numeric_sort = self.default_numeric_sort
        return res
    def all_symbols(self):
        for name,sym in self.symbols.iteritems():
            if isinstance(sym.sort,UnionSort):
                for sort in sym.sort.sorts:
                    yield Symbol(sym.name,sort)
            else:
                yield sym
    def remove_symbol(self,symbol):
        assert symbol.name in self.symbols, symbol.name
        sort = self.symbols[symbol.name].sort
        if isinstance(sort,UnionSort):
            assert symbol.sort in sort.sorts
            sort.sorts.remove(symbol.sort)
            return
        del self.symbols[symbol.name]

    def contains_symbol(self,symbol):
        if symbol.name not in self.symbols:
            return False
        sort = self.symbols[symbol.name].sort
        if isinstance(sort,UnionSort):
            return symbol.sort in sort.sorts
        return True

    def __str__(self):
        return sig_to_str(self)

alpha = lg.TopSort('alpha')

lg.BooleanSort.name = 'bool'

polymorphic_symbols_list = [
    ('<' , [alpha,alpha,lg.Boolean]),
    ('<=' , [alpha,alpha,lg.Boolean]),
    ('>' , [alpha,alpha,lg.Boolean]),
    ('>=' , [alpha,alpha,lg.Boolean]),
    ('+' , [alpha,alpha,alpha]),
    ('*' , [alpha,alpha,alpha]),
    ('-' , [alpha,alpha,alpha]),
    ('/' , [alpha,alpha,alpha]),
]

polymorphic_symbols = dict((x,lg.Const(x,lg.FunctionSort(*y))) for x,y in polymorphic_symbols_list)

polymorphic_macros_map = {
    '<=' : '<',
    '>' : '<',
    '>=' : '<',
}

macros_expansions = {
    '<=' : lambda t: Or(normalize_symbol(t.func)(*t.args),Equals(*t.args)),
    '>' : lambda t: normalize_symbol(t.func)(t.args[1],t.args[0]),
    '>=' : lambda t: Or(normalize_symbol(t.func)(t.args[1],t.args[0]),Equals(*t.args)),
}

def is_macro(term):
    return isinstance(term,lg.Apply) and term.func.name in macros_expansions and iu.ivy_use_polymorphic_macros

def expand_macro(term):
    return macros_expansions[term.func.name](term)
    
def default_sort():
    ds = sig._default_sort
    if ds != None: return ds
    if not iu.get_numeric_version() <= [1,2]:
        raise IvyError(None,'unspecified type')
    ds = lg.UninterpretedSort('S')
    add_sort(ds)
    sig._default_sort = ds
    return ds

def is_default_sort(s):
    return s == sig._default_sort

def is_default_numeric_sort(s):
    return s == sig.default_numeric_sort

equals = Symbol('=',RelationSort([lg.TopSort(),lg.TopSort()]))

lg.Eq.relname = property(lambda self: equals)

def Equals(x,y):
    return lg.Eq(x,y)

def is_eq(ast):
    return isinstance(ast,lg.Eq)

def is_equals(symbol):
    return isinstance(symbol,Symbol) and symbol.name == '='

def is_enumerated(term):
    return isinstance(term.get_sort(),EnumeratedSort)

def is_individual(term):
    return term.sort != lg.Boolean
#    return isinstance(term,lg.Const) or (isinstance(term,App) and term.sort != lg.Boolean)

def is_constant(term):
    return isinstance(term,lg.Const)

def is_variable(term):
    return isinstance(term,lg.Var)
        
def sort_infer(term,sort=None):
    res = concretize_sorts(term,sort)
    for x in chain(lu.used_variables(res),lu.used_constants(res)):
        if lg.contains_topsort(x.sort) or lg.is_polymorphic(x.sort):
            raise IvyError(None,"cannot infer sort of {} in {}".format(x,term))
#    print "sort_infer: res = {!r}".format(res)
    return res

def sorts():
    return [s for n,s in sig.sorts.iteritems()]

def is_concretely_sorted(term):
    return not lg.contains_topsort(term) and not lg.is_polymorphic(term)

# TODO: this class doesn't belong here

def ast_match_lists(lx, ly, placeholders,subst):
##    print "ml: %s %s %s %s" % (lx,ly, placeholders,subst)
    if len(lx) != len(ly):
        return False
    for x,y in zip(lx,ly):
        if not ast_match(x,y, placeholders,subst):
            return False
    return True

def ast_match(x, y, placeholders, subst):
##    print "m: %s %s %s %s" % (x,y, placeholders,subst)
    if type(x) is not type(y):
        return False
    elif is_variable(y) or is_constant(y):
        if y in placeholders:
            if y in subst:
                return x == subst[y]
            else:
                subst[y] = x
                return True
        return x == y
    elif isinstance(y,lg.Apply):
        if x.rep != y.rep:
            return False
        return ast_match_lists(x.args,y.args,placeholders,subst)
    elif isinstance(y,Literal):
        if x.polarity != y.polarity:
            return False
        return ast_match(x.atom,y.atom,placeholders,subst)
    elif hasattr(y,'args'):
        return ast_match_lists(x.args,y.args,placeholders,subst)
    return False # shouldn't happen



Error = lg.IvyError

""" current signature """
sig = Sig()

# string conversions

infix_symbols = set(['<','<=','>','>=','+','-','*','/'])

show_variable_sorts = True
show_numeral_sorts = True

# This converts to string with all type decorations

def to_str_with_var_sorts(t):
    res = t.ugly()
    return res

# This converts to string with no type decorations

def fmla_to_str_ambiguous(term):
    global show_variable_sorts
    global show_numeral_sorts
    show_variable_sorts = False
    show_numeral_sorts = False
    res = term.ugly()
    show_variable_sorts = True
    show_numeral_sorts = True
    return res

def app_ugly(self):
    name = self.func.name
    args = [a.ugly() for a in self.args]
    if name in infix_symbols:
        return (' ' + name + ' ').join(args)
    if len(args) == 0:  # shouldn't happen
        return name
    return name + '(' + ','.join(args) + ')'
    
def nary_ugly(op,args,parens = True):
    res = (' ' + op + ' ').join([a.ugly() for a in args])
    return ('(' + res + ')') if len(args) > 1 and parens else res

lg.Var.ugly = (lambda self: (self.name+':'+self.sort.name)
                  if show_variable_sorts and not isinstance(self.sort,lg.TopSort) else self.name)
lg.Const.ugly = (lambda self: (self.name+':'+self.sort.name)
                    if show_numeral_sorts and self.is_numeral() and not isinstance(self.sort,lg.TopSort)
                 else self.name)
lg.Eq.ugly = lambda self: nary_ugly('=',self.args,parens=False)
lg.And.ugly = lambda self: nary_ugly('&',self.args) if self.args else 'true'
lg.Or.ugly = lambda self: nary_ugly('|',self.args) if self.args else 'false'
lg.Not.ugly = lambda self: (nary_ugly('~=',self.body.args,parens=False)
                               if type(self.body) is lg.Eq
                               else '~{}'.format(self.body.ugly()))
lg.Implies.ugly = lambda self: nary_ugly('->',self.args,parens=False)
lg.Iff.ugly = lambda self: nary_ugly('<->',self.args,parens=False)
lg.Ite.ugly = lambda self:  '{} if {} else {}'.format(*[self.args[idx].ugly() for idx in (1,0,2)])

lg.Apply.ugly = app_ugly

def quant_ugly(self):
    res = 'forall ' if isinstance(self,lg.ForAll) else 'exists '
    res += ','.join(v.ugly() for v in self.variables)
    res += '. ' + self.body.ugly()
    return res

for cls in [lg.ForAll,lg.Exists]:
    cls.ugly = quant_ugly


# Drop the type annotations of variables and polymorphic
# constants that can be inferred using the current signature. Here,
# "inferred_sort" is the sort of fmla that has been inferred, or
# None, and annotated_vars is the set of variable names that have
# already been annotated.

def var_drop_annotations(self,inferred_sort,annotated_vars):
    if inferred_sort or self.name in annotated_vars:
        annotated_vars.add(self.name)
        return lg.Var(self.name,lg.TopS)
    if not isinstance(self.sort,lg.TopSort):
        annotated_vars.add(self.name)
    return self

lg.Var.drop_annotations = var_drop_annotations

def const_drop_annotations(self,inferred_sort,annotated_vars):
    if inferred_sort and self.is_numeral():
        return lg.Const(self.name,lg.TopS)
    return self

lg.Const.drop_annotations = const_drop_annotations

def eq_drop_annotations(self,inferred_sort,annotated_vars):
    arg0 = self.args[0].drop_annotations(False,annotated_vars)
    arg1 = self.args[1].drop_annotations(True,annotated_vars)
    return lg.Eq(arg0,arg1)

lg.Eq.drop_annotations = eq_drop_annotations

def ite_drop_annotations(self,inferred_sort,annotated_vars):
    arg1 = self.args[1].drop_annotations(inferred_sort,annotated_vars)
    arg2 = self.args[2].drop_annotations(True,annotated_vars)
    arg0 = self.args[0].drop_annotations(True,annotated_vars)
    return lg.Ite(arg0,arg1,arg2)

lg.Ite.drop_annotations = ite_drop_annotations

def apply_drop_annotations(self,inferred_sort,annotated_vars):
    name = self.func.name
    if name in polymorphic_symbols:
        arg0 = self.args[0].drop_annotations(inferred_sort and self.sort != lg.Boolean,annotated_vars)
        rest = [arg.drop_annotations(True,annotated_vars) for arg in self.args[1:]]
        return self.clone([arg0]+rest)
    return self.clone([arg.drop_annotations(True,annotated_vars) for arg in self.args])

lg.Apply.drop_annotations = apply_drop_annotations

def quant_drop_annotations(self,inferred_sort,annotated_vars):
    body = self.body.drop_annotations(True,annotated_vars)
    return type(self)([v.drop_annotations(False,annotated_vars) for v in self.variables],body)

for cls in [lg.ForAll, lg.Exists]:
    cls.drop_annotations = quant_drop_annotations

def default_drop_annotations(self,inferred_sort,annotated_vars):
    return self.clone([arg.drop_annotations(True,annotated_vars) for arg in self.args])

for cls in [lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff]:
    cls.drop_annotations = default_drop_annotations
 
for cls in [lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff,]:
    cls.drop_annotations = default_drop_annotations

def pretty_fmla(self):
    d = self.drop_annotations(False,set())
    return d.ugly()

for cls in [lg.Eq, lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff, lg.Ite, lg.ForAll, lg.Exists,
            lg.Apply, lg.Var, lg.Const]:
    cls.__str__ = pretty_fmla

# end string conversion stuff

def close_formula(fmla):
    variables = list(lu.free_variables(fmla))
    if variables == []:
        return fmla
    else:
        return ForAll(variables,fmla)

free_variables = lu.free_variables

def uninterpreted_sorts():
    return [s for s in sig.sorts.values() if isinstance(s,UninterpretedSort) and s.name not in sig.interp]

def interpreted_sorts():
    return [s for s in sig.sorts.values() if is_interpreted_sort(s)]

def is_uninterpreted_sort(s):
    return isinstance(s,UninterpretedSort) and s.name not in sig.interp

def is_interpreted_sort(s):
    return (isinstance(s,UninterpretedSort) or isinstance(s,EnumeratedSort)) and s.name in sig.interp

def sort_interp(s):
    return sig.interp[s.name]

def is_numeral(term):
    return isinstance(term,Symbol) and term.is_numeral()

def sig_to_str(self):
    res = ''
    for name,sort in self.sorts.iteritems():
        if name == 'bool':
            continue
        res += 'type {}'.format(name)
        if not isinstance(sort,UninterpretedSort):
            res += ' = {}'.format(sort)
        res += '\n'
    for name,sym in self.symbols.iteritems():
        sorts = sym.sort.sorts if isinstance(sym.sort,UnionSort) else [sym.sort]
        for sort in sorts:
            res +=  'relation ' if sort.is_relational() else 'function ' if sort.dom else 'individual '
            res += name
            if sort.dom:
                res += '(' + ','.join('V{}:{}'.format(idx,s) for idx,s in enumerate(sort.dom)) + ')'
            if not sort.is_relational():
                res += ' : {}'.format(sort.rng)
            res += '\n'
    return res

if __name__ == '__main__':
    V1 = Variable('V1')
    V2 = Variable('V2')
    x = Constant('x')
    y = Constant('y')
    n = Predicate('n', 2)
    is_ = Predicate('is', 1)

    print [[~n(V1, V2), ~n(x, V1), n(x, y), is_(V2), is_(V1)],
           [V1 == x,V1 != x],
           [y == x, y != x],
           [V1 == V2, V1 != V2],
           [x == V2, x != V2],
    ]

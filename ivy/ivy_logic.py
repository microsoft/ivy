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
from logic import And,Or,Not,Globally,Eventually,Implies,Iff,Ite,ForAll,Exists,Lambda,NamedBinder
from type_inference import concretize_sorts, concretize_terms
from collections import defaultdict
from itertools import chain
import ivy_smtlib

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

class sort_as_default(object):
    """ Context in which a given sort is the default sort
    """
    def __init__(self,sort):
        self.sort = sort
    def __enter__(self):
        global sig
        self.old_default_sort = sig.sorts.get('S',None)
        sig.sorts['S'] = self.sort
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global sig
        if self.old_default_sort is not None:
            sig.sorts['S'] = self.old_default_sort
        else:
            del sig.sorts['S']
        return False # don't block any exceptions

class top_sort_as_default(sort_as_default):
    """ Context in which TopSort is the default sort
    """
    def __init__(self):
        self.sort = lg.TopS

class alpha_sort_as_default(sort_as_default):
    """ Context in which alpha is the default sort
    """
    def __init__(self):
        self.sort = lg.TopSort('alpha')

def is_numeral_name(s):
    return s[0].isdigit() or s[0] == '"'  or (s[0] == '-' and len(s) > 1 and s[1].isdigit)

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
Symbol.is_numeral  = lambda self : is_numeral_name(self.name)
Symbol.clone = lambda self,args : self
Symbol.resort = lambda self,sort : Symbol(self.name,sort)

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
    @property
    def variables(self):
        return [self.args[0]]
    def clone_binder(self,vs,body):
        return Some(*(vs+self.args[1:]))


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
    def lhs(self):
        return self.args[0]
    def rhs(self):
        return self.args[1]
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
    def __eq__(self,other):
        return type(self) is type(other) and all(x == y for (x,y) in zip(self.args,other.args))

class DefinitionSchema(Definition):
    pass


lg_ops = [lg.Eq, lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff, lg.Ite, lg.ForAll, lg.Exists, lg.Lambda, lg.NamedBinder]

for cls in lg_ops:
    cls.args = property(lambda self: [ a for a in self])
    cls.clone = lambda self,args: type(self)(*args)

for cls in [lg.ForAll, lg.Exists, lg.Lambda]:
    cls.clone = lambda self,args: type(self)(self.variables,*args)

for cls in [lg.Globally, lg.Eventually]:
    cls.args = property(lambda self: [ a for a in self])
    cls.clone = lambda self,args: type(self)(self.environ,*args)

lg.NamedBinder.clone = lambda self,args: lg.NamedBinder(self.name, self.variables, self.environ, *args)
lg.NamedBinder.rep = property(lambda self: self)

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

lg.Eq.rep = property(lambda self: Symbol('=',RelationSort([x.sort for x in self.args])))

App = lg.Apply
def Atom(rel,args):
    return Equals(*args) if rel == equals else lg.Apply(rel,*args) if args else rel

def is_atom(term):
    return (isinstance(term,App) or isinstance(term,Symbol)) and term.sort == lg.Boolean or isinstance(term,lg.Eq)

# note: ivy1 treats instances of a constant in a formula as an app
def is_app(term):
    return (
        isinstance(term,App) or
        isinstance(term,lg.Const) or
        isinstance(term,lg.NamedBinder) and len(term.variables) == 0
    )

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

def find_symbol(symbol_name,throw=True):
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
        if not throw:
            return None
        else:
            if symbol_name in sig.sorts:
                IvyError(None,"type {} used where a function or individual symbol is expected".format(symbol_name))
            raise IvyError(None,"unknown symbol: {}".format(symbol_name))

def find_polymorphic_symbol(symbol_name,throw=True):
    if iu.ivy_have_polymorphism and symbol_name in polymorphic_symbols:
        return polymorphic_symbols[symbol_name]
    if symbol_name[0].isdigit() or symbol_name[0] == '"':
        return Symbol(symbol_name,alpha)
    return find_symbol(symbol_name,throw)

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
    return sig.add_symbol(symbol_name,sort)

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

logics = ["epr","qf","fo"]
decidable_logics = ["epr","qf"]
default_logics = ["epr"]

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

class NotEssentiallyUninterpreted(Exception):
    pass

def check_essentially_uninterpreted(fmla):
    if is_variable(fmla):
        return False
    if is_binder(fmla):
        return check_essentially_uninterpreted(fmla.body) and len(fmla.variables) == 0
    argres = all([check_essentially_uninterpreted(a) for a in fmla.args])
    if is_app(fmla) and is_interpreted_symbol(fmla.rep):
        if not argres:
            raise NotEssentiallyUninterpreted()
    return argres

def symbols_over_universals_rec(fmla,syms,pos,univs):
    if is_variable(fmla):
        return fmla not in univs
    if is_quantifier(fmla):
        if pos == isinstance(fmla,lg.ForAll) or len(univs) > 0:
            univs.update(fmla.variables)
            res = symbols_over_universals_rec(fmla.body,syms,pos,univs)
            for v in fmla.variables:
                univs.remove(v)
            return res
    if isinstance(fmla,Not):
        pos = not pos
    argres = all([symbols_over_universals_rec(a,syms,pos,univs) for a in fmla.args])
    if is_app(fmla) and not is_eq(fmla) and not argres:
        syms.add(fmla.rep)
    return argres

def symbols_over_universals(fmlas):
    """ Return the set of function symbols that occur over universally
    quantified variables after skolemization.  In the formula 'forall
    X. exists Y. p(X)', p occurs over a universal, since this
    skolemizes to 'forall X. p(f(X))'. We don't count free variables,
    however. If you want free variabes to be considered quantified,
    you have to add a quantifier (see close_formula)."""

    syms = set()
    for fmla in fmlas:
        try:
            symbols_over_universals_rec(fmla,syms,True,set())
        except Exception as foo:
            print fmla
            raise foo
    return syms

def universal_variables_rec(fmla,pos,univs):
    if is_quantifier(fmla):
        if pos == isinstance(fmla,lg.ForAll):
            univs.update(fmla.variables)
            return
    if isinstance(fmla,Implies):
        universal_variables_rec(fmla.args[0],not pos,univs),
        universal_variables_rec(fmla.args[1],pos,univs)
        return
    if isinstance(fmla,Not):
        pos = not pos
    for a in fmla.args:
        universal_variables_rec(a,pos,univs)

def universal_variables(fmlas):
    """ Return the set of variables quantified universally after skolemization."""

    univs = set()
    for fmla in fmlas:
        universal_variables_rec(fmla,True,univs)
    return univs

# def check_essentially_uninterpreted(fmla):
#     syms = symbols_over_universals([fmla])
#     if any(is_interpreted_symbol(sym) for sym in syms):
#         raise NotEssentiallyUninterpreted()

def is_in_logic(term,logic,unstrat = False):
    global reason_text
    assert logic in logics
    if logic == "epr":
        # ok = (is_prenex_universal(term)
        #       if lu.free_variables(term) else is_ea(term))
        # if not ok:
        #     reason_text = "of quantifier alternation"
        #     return False
        try:
            check_essentially_uninterpreted(term)
        except NotEssentiallyUninterpreted:
            reason_text = "a variable occurs under an interpreted function symbol"
            return False
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
        reason_text = "a formula contains a quantifier"
        return is_qf(term)
    elif logic == "fo":
        cs = lu.used_constants(term)
        for s in cs:
            if s.name in sig.interp:
                reason_text = "'{}' is iterpreted".format(s)
                return False
        return True



def Constant(sym):
    return sym # first-order constants are not applied in ivy2

def is_forall(term):
    return isinstance(term,lg.ForAll)

def is_exists(term):
    return isinstance(term,lg.Exists)

def is_lambda(term):
    return isinstance(term,lg.Lambda)

def is_quantifier(term):
    return isinstance(term,lg.ForAll) or isinstance(term,lg.Exists)

def is_binder(term):
    return isinstance(term, (lg.ForAll, lg.Exists, lg.Lambda, lg.NamedBinder, Some))

for b in [lg.ForAll,lg.Exists,lg.Lambda]:
    b.clone_binder = lambda self, variables, body, b = b: b(variables,body)

lg.NamedBinder.clone_binder = lambda self, variables, body: lg.NamedBinder(self.name,variables,self.enrivon,body)

def is_named_binder(term):
    return isinstance(term, lg.NamedBinder)

def is_temporal(term):
    return isinstance(term, (lg.Globally, lg.Eventually))

def has_temporal(fmla):
    return is_temporal(fmla) or any(has_temporal(x) for x in fmla.args)

# A formula is a Gprop if it is of the form Globally(phi) where phi does not have temporal
# operators.
def is_gprop(fmla):
    return isinstance(fmla,lg.Globally) and not has_temporal(fmla.args[0])
    
def quantifier_vars(term):
    return term.variables

def binder_vars(term):
    return term.variables

def quantifier_body(term):
    return term.body

def binder_args(term):
    if isinstance(term,Some):
        return term.args[1:]
    return [term.body]

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

# Return a prediciate stating relation "rel" is a partial function
def partial_function(rel):
    lsort,rsort = rel.sort.dom
    x,y,z = [Variable(n,s) for n,s in [('X',lsort),('Y',rsort),('Z',rsort)]]
    return ForAll([x,y,z],Implies(And(rel(x,y),rel(x,z)),Equals(y,z)))

# Return a prediciate stating the an element of "sort" can point to
# only one variant of "sort". This is sadly quadratic.  TODO: maybe
# use a function to an enumerated type to express this constraint.
# We also include here extensionality for variants, that is to values
# that point to the same value are the equal. A sore point, however, is that
# null values may not be equal.

def exclusivity(sort,variants):
    # partial funciton
    def pto(s):
        return Symbol('*>',RelationSort([sort,s]))
    excs = [partial_function(pto(s)) for s in variants]
    for s in variants:
        x,y,z = [Variable(n,s) for n,s in [('X',sort),('Y',sort),('Z',s)]]
        excs.append(Implies(And(pto(s)(x,z),pto(s)(y,z)),Equals(x,y)))
    for i1,s1 in enumerate(variants):
        for s2 in variants[:i1]:
            x,y,z = [Variable(n,s) for n,s in [('X',sort),('Y',s1),('Z',s2)]]
            excs.append(Not(And(pto(s1)(x,y),pto(s2)(x,z))))
    return And(*excs)

Variable = lg.Var
Variable.args = property(lambda self: [])
Variable.clone = lambda self,args: self
Variable.rep = property(lambda self: self.name)
Variable.__call__ = lambda self,*args: App(self,*args) if isinstance(self.sort,FunctionSort) else self
Variable.rename = lambda self,name: Variable(name if isinstance(name,str) else name(self.name),self.sort)
Variable.resort = lambda self,sort : Variable(self.name,sort)


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
UninterpretedSort.rename = lambda self,rn: UninterpretedSort(rn(self.name))

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

def is_function_sort(s):
    return isinstance(s,FunctionSort)

def FuncConstSort(*sorts):
    return FunctionSort(*sorts) if len(sorts) > 1 else sorts[0]

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

def is_topsort(sort):
    return isinstance(sort,lg.TopSort)

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
        self.old_sigs = []
    def __enter__(self):
        global sig
        self.old_sigs.append(sig)
        sig = self
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global sig
        sig = self.old_sigs[-1]
        self.old_sigs = self.old_sigs[:-1]
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
    def add_symbol(self,symbol_name,sort):
        #    print "add symbol: {} : {}".format(symbol_name,sort)
        if iu.ivy_have_polymorphism and symbol_name in polymorphic_symbols:
            if symbol_name not in self.symbols:
                self.symbols[symbol_name] = Symbol(symbol_name,UnionSort())
            u = self.symbols[symbol_name].sort
            if sort not in u.sorts:
                u.sorts.append(sort)
            return Symbol(symbol_name,sort)
        elif symbol_name in self.symbols:
            if sort != self.symbols[symbol_name].sort:
                raise IvyError(None,"redefining symbol: {}".format(symbol_name))
        else:
            self.symbols[symbol_name] = Symbol(symbol_name,sort)
        return self.symbols[symbol_name]

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

    def contains(self,sort_or_symbol):
        if isinstance(sort_or_symbol,Symbol):
            return self.contains_symbol(sort_or_symbol)
        return self.sorts.get(sort_or_symbol.name,None) == sort_or_symbol

    def all_symbols_named(self,name):
        if name not in self.symbols:
            return []
        sort = self.symbols[name].sort
        if isinstance(sort,UnionSort):
            return [Symbol(name,s) for s in sort.sorts]
        return [Symbol(name,sort)]

    def __str__(self):
        return sig_to_str(self)

# Environment that temporarily adds symbols to a signature.

class WithSymbols(object):
    def __init__(self,symbols):
        self.symbols = list(symbols)
    def __enter__(self):
        global sig
        self.saved = []
        for sym in self.symbols:
            if sym.name in sig.symbols:
                self.saved.append((sym.name,sig.symbols[sym.name]))
                del sig.symbols[sym.name]
            sig.symbols[sym.name] = sym
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global sig
        for sym in self.symbols:
            del sig.symbols[sym.name]
        for name,sym in self.saved:
            sig.symbols[name] = sym
        return False # don't block any exceptions

class WithSorts(object):
    def __init__(self,sorts):
        self.sorts = list(sorts)
    def __enter__(self):
        global sig
        self.saved = []
        for sym in self.sorts:
            if sym.name in sig.sorts:
                self.saved.append(sym)
            sig.sorts[sym.name] = sym
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global sig
        for sym in self.sorts:
            del sig.sorts[sym.name]
        for sym in self.saved:
            sig.sorts[sym.name] = sym
        return False # don't block any exceptions

class BindSymbols(object):
    def __init__(self,env,symbols):
        self.env, self.symbols = env, list(symbols)
    def __enter__(self):
        self.saved = []
        for sym in self.symbols:
            if sym in self.env:
                self.saved.append(sym)
                self.env.remove(sym)
            self.env.add(sym)
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        for sym in self.symbols:
            self.env.remove(sym)
        for sym in self.saved:
            self.env.add(sym)
        return False # don't block any exceptions

class BindSymbolValues(object):
    def __init__(self,env,bindings):
        self.env, self.bindings = env, list(bindings)
    def __enter__(self):
        self.saved = []
        for sym,val in self.bindings:
            if sym in self.env:
                self.saved.append((sym,env[sym]))
                del self.env[sym]
            self.env[sym] = val
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        for sym,val in self.bindings:
            del self.env[sym]
        for sym,val in self.saved:
            self.env[sym] = val
        return False # don't block any exceptions


alpha = lg.TopSort('alpha')
beta = lg.TopSort('beta')

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
    ('*>' , [alpha,beta,lg.Boolean]),
    ('bvand' , [alpha,alpha,alpha]),
    ('bvor' , [alpha,alpha,alpha]),
    ('bvnot' , [alpha,alpha]),
    # for liveness to safety reduction:
    ('l2s_waiting', [lg.Boolean]),
    ('l2s_frozen', [lg.Boolean]),
    ('l2s_saved', [lg.Boolean]),
    ('l2s_d', [alpha, lg.Boolean]),
    ('l2s_a', [alpha, lg.Boolean]),
]

# Tricky: since the bfe operator is parameterized, we add instances of it to
# the polymorphic_symbols table on demand.

class PolySymsDict(dict):
    def __contains__(self,name):
        return dict.__contains__(self,name) or name.startswith('bfe[')
    def __getitem__(self,name):
        if name.startswith('bfe[') and not dict.__contains__(self,name):
            dict.__setitem__(self,name,lg.Const(name,lg.FunctionSort(alpha,beta)))
        return dict.__getitem__(self,name)

polymorphic_symbols = PolySymsDict((x,lg.Const(x,lg.FunctionSort(*y) if len(y) > 1 else y[0]))
                           for x,y in polymorphic_symbols_list)

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

def is_inequality_symbol(sym):
    return sym.name in ['<','<=','>','>=']

def is_strict_inequality_symbol(sym,pol=0):
    """ Determine whether an inequality symbol is strict under a given
    number of negations, where pol == 0 indicates an even number, pol
    == 1 an odd number and None indicates neither even nor odd."""

    return sym.name in ['<','>'] if pol == 0 else sym.name in ['<=','>='] if pol == 1 else False

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

def is_ite(ast):
    return isinstance(ast,lg.Ite)

def is_enumerated(term):
    return is_app(term) and isinstance(term.get_sort(),EnumeratedSort)

def is_individual(term):
    assert hasattr(term,'sort'),term
    return term.sort != lg.Boolean
#    return isinstance(term,lg.Const) or (isinstance(term,App) and term.sort != lg.Boolean)

def is_constant(term):
    return isinstance(term,lg.Const)

def is_variable(term):
    return isinstance(term,lg.Var)


def all_concretely_sorted(*terms):
    return True

def check_concretely_sorted(term,no_error=False,unsorted_var_names=()):
    for x in chain(lu.used_variables(term),lu.used_constants(term)):
        if lg.contains_topsort(x.sort) or lg.is_polymorphic(x.sort):
            if x.name not in unsorted_var_names:
                if no_error:
                    raise lg.SortError
                raise IvyError(None,"cannot infer sort of {} in {}".format(x,repr(term)))


def sort_infer(term,sort=None,no_error=False):
    res = concretize_sorts(term,sort)
    check_concretely_sorted(res,no_error)
    return res

def sort_infer_list(terms,sorts=None,no_error=False,unsorted_var_names=()):
    res = concretize_terms(terms,sorts)
    for term in res:
        check_concretely_sorted(term,no_error,unsorted_var_names)
    return res

def sorts():
    return [s for n,s in sig.sorts.iteritems()]

def is_ui_sort(s):
    return type(s) is lg.UninterpretedSort


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

prec_symbols = {'<':7,'<=':7,'>':7,'>=':7,'+':12,'-':13,'*':14,'/':15}


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
    res = term.ugly(0)
    show_variable_sorts = True
    show_numeral_sorts = True
    return res

def app_ugly(self,prec):
    if type(self.func) is lg.NamedBinder:
        name = str(self.func)
    else:
        name = self.func.name
    myprec = prec_symbols.get(name,1)
    infix = name in infix_symbols
    if infix and len(self.args) == 2:
        args = [self.args[0].ugly(myprec-1), self.args[1].ugly(myprec)]
    else:
        args = [a.ugly(myprec) for a in self.args]
    if infix:
        if len(args) == 1 and name == '-':
            res = name + args[0]
        else:
            res = (' ' + name + ' ').join(args)
        if myprec <= prec:
            res = '(' + res + ')'
        return res
    if len(args) == 0:  # shouldn't happen
        return name
    return name + '(' + ','.join(args) + ')'

def nary_ugly(op,args,myprec,prec):
    if len(args) == 2:
        uargs = [args[0].ugly(myprec-1), args[1].ugly(myprec)]
    else:
        uargs = [a.ugly(myprec) for a in args]
    res = (' ' + op + ' ').join(uargs)
    return ('(' + res + ')') if len(args) > 1 and myprec <= prec else res

lg.Var.ugly = (lambda self,prec: (self.name+':'+self.sort.name)
                  if show_variable_sorts and not isinstance(self.sort,lg.TopSort) else self.name)
lg.Const.ugly = (lambda self,prec: (self.name+':'+self.sort.name)
                    if show_numeral_sorts and self.is_numeral() and not isinstance(self.sort,lg.TopSort)
                 else self.name)
lg.Eq.ugly = lambda self,prec: nary_ugly('=',self.args,7,prec)
lg.And.ugly = lambda self,prec: nary_ugly('&',self.args,5,prec) if self.args else 'true'
lg.Or.ugly = lambda self,prec: nary_ugly('|',self.args,4,prec) if self.args else 'false'
lg.Not.ugly = lambda self,prec: (nary_ugly('~=',self.body.args,8,prec)
                               if type(self.body) is lg.Eq
                               else '~{}'.format(self.body.ugly(6)))
lg.Globally.ugly = lambda self,prec: ('globally{} {}'.format(ugly_environ(self),self.body.ugly(2)))
lg.Eventually.ugly = lambda self,prec: ('eventually{} {}'.format(ugly_environ(self),self.body.ugly(2)))
lg.Implies.ugly = lambda self,prec: nary_ugly('->',self.args,3,prec)
lg.Iff.ugly = lambda self,prec: nary_ugly('<->',self.args,3,prec)
lg.Ite.ugly = lambda self,prec:  '({} if {} else {})'.format(*[self.args[idx].ugly(9) for idx in (1,0,2)])
Definition.ugly = lambda self,prec: nary_ugly('=',self.args,7,prec)

def ugly_environ(self):
    environ = self.environ
    return '' if environ is None else '['+str(environ)+']'

lg.Apply.ugly = app_ugly

def quant_ugly(self,prec):
    res = ('forall ' if isinstance(self,lg.ForAll) else
           'exists ' if isinstance(self,lg.Exists) else
           'lambda ' if isinstance(self,lg.Lambda) else
           '$' + self.name + ' ')
    res += ','.join(v.ugly(1) for v in self.variables)
    res += '. ' + self.body.ugly(1)
    if prec >= 1:
        res = '(' + res + ')'
    return res

for cls in [lg.ForAll,lg.Exists, lg.Lambda, lg.NamedBinder]:
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
        rest = [arg.drop_annotations(name != '*>',annotated_vars) for arg in self.args[1:]]
        return self.clone([arg0]+rest)
    return self.clone([arg.drop_annotations(True,annotated_vars) for arg in self.args])

lg.Apply.drop_annotations = apply_drop_annotations

def symbol_is_polymorphic(func):
    return func.name in polymorphic_symbols

# convert symbol to string with its type
def typed_symbol(func):
    return func.name + ' : ' + str(func.sort)

def quant_drop_annotations(self,inferred_sort,annotated_vars):
    body = self.body.drop_annotations(True,annotated_vars)
    return type(self)([v.drop_annotations(False,annotated_vars) for v in self.variables],body)

for cls in [lg.ForAll, lg.Exists, lg.Lambda]:
    cls.drop_annotations = quant_drop_annotations

lg.NamedBinder.drop_annotations = lambda self,inferred_sort,annotated_vars: lg.NamedBinder(
    self.name,
    [v.drop_annotations(False,annotated_vars) for v in self.variables],
    self.environ,
    self.body.drop_annotations(True,annotated_vars)
)

def default_drop_annotations(self,inferred_sort,annotated_vars):
    return self.clone([arg.drop_annotations(True,annotated_vars) for arg in self.args])

for cls in [lg.Not, lg.Globally, lg.Eventually, lg.And, lg.Or, lg.Implies, lg.Iff, Definition]: # should binder be here?
    cls.drop_annotations = default_drop_annotations


def pretty_fmla(self):
    d = self.drop_annotations(False,set())
    return d.ugly(0)

for cls in [lg.Eq, lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff, lg.Ite, lg.ForAll, lg.Exists,
            lg.Apply, lg.Var, lg.Const, lg.Lambda, lg.NamedBinder]:
    cls.__str__ = pretty_fmla

# end string conversion stuff

def close_formula(fmla):
    variables = list(lu.free_variables(fmla))
    if variables == []:
        return fmla
    else:
        return ForAll(variables,fmla)

free_variables = lu.free_variables

def implement_type(sort1,sort2):
    sig.interp[sort1.name] = sort2

def is_canonical_sort(sort):
    if isinstance(sort,UninterpretedSort):
        s = sig.interp.get(sort.name,None)
        return not isinstance(s,UninterpretedSort)
    return True

def canonize_sort(sort):
    if isinstance(sort,UninterpretedSort):
        s = sig.interp.get(sort.name,None)
        if isinstance(s,UninterpretedSort):
            return canonize_sort(s)
    return sort

def sort_refinement():
    return dict((s,canonize_sort(s)) for s in sig.sorts.values() if not is_canonical_sort(s))

# This returns only the *canonical* uninterpreted sorts

def uninterpreted_sorts():
    return [s for s in sig.sorts.values() if isinstance(s,UninterpretedSort) and s.name not in sig.interp]

def interpreted_sorts():
    return [s for s in sig.sorts.values() if is_interpreted_sort(s)]

def is_uninterpreted_sort(s):
    s = canonize_sort(s)
    return isinstance(s,UninterpretedSort) and s.name not in sig.interp

# For now, int is the only infinite interpreted sort
def has_infinite_interpretation(s):
    s = canonize_sort(s)
    return s.name in sig.interp and not ivy_smtlib.quantifiers_decidable(sig.interp[s.name])

def is_interpreted_sort(s):
    s = canonize_sort(s)
    return (isinstance(s,UninterpretedSort) or isinstance(s,EnumeratedSort)) and s.name in sig.interp

def sort_interp(s):
    return sig.interp.get(canonize_sort(s).name,None)

def is_numeral(term):
    return isinstance(term,Symbol) and term.is_numeral()

def is_interpreted_symbol(s):
#    if symbol_is_polymorphic(s) and len(s.sort.dom) == 0:
#        print s
    return is_numeral(s) and is_interpreted_sort(s.sort) or symbol_is_polymorphic(s) and len(s.sort.dom) > 0 and is_interpreted_sort(s.sort.dom[0])

def is_deterministic_fmla(f):
    if isinstance(f,Some) and len(f.args) < 4:
        return False
    return all(is_deterministic_fmla(a) for a in f.args)


def sym_decl_to_str(sym):
    sort = sym.sort
    res =  'relation ' if sort.is_relational() else 'function ' if sort.dom else 'individual '
    res += sym.name
    if sort.dom:
        res += '(' + ','.join('V{}:{}'.format(idx,s) for idx,s in enumerate(sort.dom)) + ')'
    if not sort.is_relational():
        res += ' : {}'.format(sort.rng)
    return res

def typed_sym_to_str(sym):
    return str(sym.name) + ':' + str(sym.sort)

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

def is_true(ast):
    return isinstance(ast,And) and not ast.args

def is_false(ast):
    return isinstance(ast,Or) and not ast.args

def simp_and(x,y):
    if is_true(x):
        return y
    if is_false(x):
        return x
    if is_true(y):
        return x
    if is_false(y):
        return y
    return And(x,y)

def simp_or(x,y):
    if is_false(x):
        return y
    if is_true(x):
        return x
    if is_false(y):
        return x
    if is_true(y):
        return y
    return Or(x,y)

def simp_not(x):
    if isinstance(x,Not):
        return x.args[0]
    if is_true(x):
        return Or()
    if is_false(x):
        return And()
    return Not(x)

def simp_ite(i,t,e):
    if t == e:
        return t
    if is_true(i):
        return t
    if is_false(i):
        return e
    if is_true(t):
        return simp_or(i,e)
    if is_false(t):
        return simp_and(simp_not(i),e)
    if is_true(e):
        return simp_or(simp_not(i),t)
    if is_false(e):
        return simp_and(i,t)
    return Ite(i,t,e)

def pto(*asorts):
    return Symbol('*>',RelationSort(asorts))

CaptureError = lu.CaptureError

def lambda_apply(self,args):
    assert len(args) == len(self.variables)
    return lu.substitute(self.body,dict(zip(self.variables,args)))

lg.Lambda.__call__ = lambda self,*args: lambda_apply(self,args)

substitute = lu.substitute

def rename_vars_no_clash(fmlas1,fmlas2):
    """ Rename the free variables in formula list fmlas1
    so they occur nowhere in fmlas2, avoiding capture """
    uvs = lu.used_variables(*fmlas2)
    iu.dbg('uvs')
    uvs = lu.union(uvs,lu.bound_variables(*fmlas1))
    iu.dbg('uvs')
    rn = iu.UniqueRenamer('',(v.name for v in uvs))
    vs = lu.free_variables(*fmlas1)
    vmap = dict((v,Variable(rn(v.name),v.sort)) for v in vs)
    iu.dbg('vmap')
    return [lu.substitute(f,vmap) for f in fmlas1]

class VariableUniqifier(object):
    """ An object that alpha-converts formulas so that all variables are unique. """
    def __init__(self):
        self.rn = iu.UniqueRenamer()
        self.invmap = dict()
    def __call__(self,fmla):
        vmap = dict()
        res = self.rec(fmla,vmap)
        return res
    def rec(self,fmla,vmap):
        if is_binder(fmla):
            # save the old bindings
            obs = [(v,vmap[v]) for v in fmla.variables if v in vmap]
            newvars = tuple(Variable(self.rn(v.name),v.sort) for v in fmla.variables)
            vmap.update(zip(fmla.variables,newvars))
            self.invmap.update(zip(newvars,fmla.variables))
            try:
                res = fmla.clone_binder(newvars,self.rec(fmla.body,vmap))
            except TypeError:
                assert False,fmla
            for v in fmla.variables:
                del vmap[v]
            vmap.update(obs)
            return res
        if is_variable(fmla):
            if fmla not in vmap:
                newv = Variable(self.rn(fmla.name),fmla.sort)
                vmap[fmla] = newv
                self.invmap[newv] = fmla
            return vmap[fmla]
        args = [self.rec(f,vmap) for f in fmla.args]
        return fmla.clone(args)
    def undo(self,fmla):
        return lu.substitute(fmla,self.invmap)

def alpha_avoid(fmla,vs):
    """ Alpha-convert a formula so that bound variable names do not clash with vs. """
    vu = VariableUniqifier()
    freevars = set(vs)
    freevars.update(lu.free_variables(fmla))  # avoid capturing free variables
    vmap = dict()
    for v in freevars:
        vu.rn(v.name)  # reserve the name
        vmap[v] = v    # preserve the variable in formula
    res = vu.rec(fmla,vmap)
    return res
        
def equal_mod_alpha(t,u):
    if isinstance(t,Definition):
        return isinstance(t,Definition) and all(equal_mod_alpha(x,y) for (x,y) in zip(t.args,u.args))
    return lu.equal_mod_alpha(t,u)


def alpha_rename(nmap,fmla):
    """ alpha-rename a formula using a map from variable names to
    variable names.  assumes the map is one-one.
    """
    vmap = dict()
    def rec(fmla):
        if is_binder(fmla):
            newvars = tuple(v.rename(nmap.get(v.name,v.name)) for v in fmla.variables)
            forbidden = frozenset(vmap.get(v,v) for v in lu.free_variables(fmla))
            if not forbidden.isdisjoint(newvars):
                raise CaptureError(forbidden.intersection(newvars))
            bndgs = [(v,v.rename(nmap[v.name])) for v in fmla.variables if v.name in nmap]
            with BindSymbolValues(vmap,bndgs):
                return fmla.clone_binder(newvars,rec(fmla.body))
        if is_variable(fmla):
            return vmap.get(fmla,fmla)
        return fmla.clone([rec(f) for f in fmla.args])
    return rec(fmla)

def normalize_ops(fmla):
    """Convert conjunctions and disjunctions to binary ops and quantifiers
    to single-variable quantifiers. """
    args = map(normalize_ops,fmla.args)
    def mkbin(op,first,rest):
        if len(rest) == 0:
            return first
        return mkbin(op,op(first,rest[0]),rest[1:])
    def mkquant(op,vs,body):
        if len(vs) == 0:
            return body
        return op(vs[0:1],mkquant(op,vs[1:],body))
    if isinstance(fmla,And) or isinstance(fmla,Or):
        return fmla.clone([]) if len(args) == 0 else mkbin(type(fmla),args[0],args[1:])
    if is_quantifier(fmla):
        return mkquant(type(fmla),list(fmla.variables),args[0])
    return fmla.clone(args)

def negate_polarity(pol):
    return 1 - pol if pol is not None else None

def polar(fmla,pos,pol):
    """ Return the polarity of the `pos` argument of `fmla` assuming the
    polarity of `fmla` is `pol`. The polarity indicates the
    number of negations under which the formula occurs. It is 0 for an
    even number, one for an odd number and None if the formula occurs
    under both an even number and an odd number of negations. """
    if isinstance(fmla,Not):
        return negate_polarity(pol)
    if isinstance(fmla,Implies):
        return pol if pos == 1 else negate_polarity(pol) 
    if is_quantifier(fmla) or isinstance(fmla,And) or isinstance(fmla,Or):
        return pol
    if isinstance(fmla,Ite):
        return None if pos == 0 else pol
    return None

def label_temporal(fmla,label):
    if is_temporal(fmla):
        return type(fmla)(label,label_temporal(fmla.body,label))
    elif is_named_binder(fmla):
        return type(fmla)(fmla.name,fmla.variables,label,label_temporal(fmla.body,label))
    args = [label_temporal(x,label) for x in fmla.args]
    if type(fmla) == lg.Apply:
        func = label_temporal(fmla.func, label)
        return type(fmla)(func, *args)
    return fmla.clone(args)

            

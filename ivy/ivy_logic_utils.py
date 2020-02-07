#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
""" This module contains various utility functions supporting ivy_logic, including:

1) parsing
2) substitution, renaming, supports
3) clausal form
   a) conversion (including Tseiting encoding)
   b) matching, unification, subsumption
   a) simplification
4) construction/destruction
5) miscellaneous utilities

"""

from ivy_utils import *
from ivy_logic import *
import string
from ivy_lexer import *
import ply.yacc as yacc
from functools import partial
import ivy_logic
from itertools import chain
from ivy_logic_parser_gen import formula_parser,term_parser
from collections import defaultdict

class LogicParseError(Exception):
    """ Exception raised on parser error """
    def __init(token,msg):
        self.token,self.msg = token,msg

def coerce_clause_to_formula(c):
    if isinstance(c,list):
        return clause_to_formula(c)
    return drop_universals(c)

class Clauses(object):
    def __init__(self,fmlas=[],defs=[],annot=None):
        assert isinstance(fmlas,list)
        self.defs = defs
        self.defidx = dict((d.defines(),d) for d in defs)
        self.fmlas = list(collect_and_list([coerce_clause_to_formula(c) for c in fmlas]))
        self.annot = annot
        
    @property
    def clauses(self):
        res = tseitin_encode(self.to_open_formula())
#        print "defs: {} fmlas: {} ".format(self.defs,self.fmlas)
#        print "cnf: {}".format(res)
        return res
    def triv_clauses(self):
        res = formula_to_clauses_aux(self.to_open_formula())
#        print "defs: {} fmlas: {} ".format(self.defs,self.fmlas)
#        print "cnf: {}".format(res)
        return res
    def is_false(self):
        return any(is_false(f) for f in self.fmlas)
    def is_true(self):
        return all(is_true(f) for f in self.fmlas)
    def conjuncts(self):
        assert self.defs == []
        return [close_epr(c) for c in self.fmlas]
    # TODO: this should not be needed
    def copy(self):
        return Clauses(list(self.fmlas),list(self.defs))
#    def define(self,dfn):
#        assert dfn.defines() not in self.defidx
#        self.defs.append(dfn)
#        self.defidx[dfn.defines()] = dfn
    def gen(self,fun,*args):
        """ return an iterator that applies an iterator to all subformulas"""
        return chain(gen_list(fun,self.fmlas,*args),
                     gen_list(fun,self.defs,*args))
    def apply(self,fun,*args,**kwargs):
        """ apply a function to all subformulas"""
        fmlas = [fun(f,*args) for f in self.fmlas]
        defs = [fun(dfn,*args) for dfn in self.defs]
        annot_fun = kwargs.pop('annot_fun',lambda x,*args:x)
        annot = annot_fun(self.annot,*args)
        res = Clauses(fmlas,defs,annot)
        return res
    def symbols(self):
        return self.gen(symbols_ast)
    def to_let(self):
        return Let(*(self.defs+[And(*self.fmlas)]))
    def __repr__(self):
        return repr(self.to_let())
    def to_open_formula(self):
        conjuncts = [dfn.to_constraint() for dfn in self.defs] + self.fmlas
        return And(*conjuncts)
        # if len(conjuncts) == 1:
        #     return conjuncts[0]
        # else:
        #     return And(*conjuncts)
    def to_formula(self):
        return close_epr(self.to_open_formula())
    def is_universal_first_order(self):
        return not self.defs and not any(sym.is_skolem() for sym in self.symbols())
    def __hash__(self):
        return hash((tuple(self.fmlas), tuple(self.defs)))
    def __eq__(self,other):
        return type(other) == type(self) and self.fmlas == other.fmlas and self.defs == other.defs

def close_epr(fmla):
    """ Convert fmla to E X. A Y. fmla, where X are the skolems in fmla and Y are the variables. """
    if isinstance(fmla,And):
        return And(*[close_epr(f) for f in fmla.args])
    skolems = [s for s in used_symbols_ast(fmla) if not s.is_skolem()]
    variables = list(used_variables_ast(fmla))
    # TODO: avoid variable name clashes (shouldn't happen, but just to be safe)
    skvars = [Variable('V' + s.name,s.sort) for s in skolems]
#    fmla2 = rename_ast(fmla,dict(zip(skolems,skvars)))
#    return Exists(skvars,ForAll(variables,fmla2))
    if variables == []:
        return fmla
    else:
        return ForAll(variables,fmla)

for op in lg_ops:
    op.clauses = property(lambda self: formula_to_clauses(self).clauses)
    op.symbols = lambda self: symbols_ast(self)
    op.is_universal_first_order = lambda self: is_prenex_universal(self) and not any(sym.is_skolem() for sym in self.symbols())
    op.to_formula = lambda self: self


def apply_gen_to_clauses(gen):
    """ return a function that returns a generator that applies a generator to a Clauses """
    return lambda cls,*args: cls.gen(gen,*args) if isinstance(cls,Clauses) else gen(cls,*args)

def apply_func_to_clauses(func,annot_fun = lambda x,*args: x):
    """ return a function that applies func to a Clauses """
    return lambda cls,*args: cls.apply(func,*args,annot_fun=annot_fun) if isinstance(cls,Clauses) else func(cls,*args)

def to_formula(s):
    return formula_parser.parse(s,lexer=lexer).compile_with_sort_inference()

def to_term(s):
    return term_parser.parse(s,lexer=lexer)

def to_clause(s):
    return formula_to_clause(to_formula(s))

def to_clauses(s):
    return formula_to_clauses(to_formula(s))

def to_literal(s):
    return formula_to_lit(to_formula(s))

to_atom = to_formula

#Parser for clauses

#Parser for lists of clauses

# substitutions

def substitute_ast(ast,subs):
    """
    Substitute terms for variables in an ast. Here, subs is
    a dict from string names of variables to terms.
    """
    if isinstance(ast, Variable):
        return subs.get(ast.rep,ast)
    if is_quantifier(ast):
        bounds = set(x.name for x in quantifier_vars(ast))
        subs = dict((x,y) for x,y in subs.iteritems() if x not in bounds)
    return ast.clone(substitute_ast(x,subs) for x in ast.args)

def substitute_constants_ast(ast,subs):
    """
    Substitute terms for *constants*. Here, subs is
    a dict from string names of constants to terms.
    """
    if is_constant(ast):
        return subs.get(ast.rep,ast)
    else:
        return ast.clone(substitute_constants_ast(x,subs) for x in ast.args)


def rename_ast(ast,subs):
    """
    Substitute names for names in ast. Here, subs is a dict from
    string names to string names. Variables are not renamed. New names
    are give the same sort as old names. Exception is thrown in case of
    a sort conflict.
    """
    args = [rename_ast(x,subs) for x in ast.args]
    if is_app(ast) and not is_named_binder(ast):
        return subs.get(ast.rep,ast.rep)(*args)
    return ast.clone(args)

def normalize_free_variables(ast):
    """
    Transforms (p(X,Y) & r(X)) or (p(A,B) & r(A)) to p(V0,V1) & r(V0).
    The order of the variables is determined by the order they are
    generated by variables_ast(ast).
    Returns (old_vars, new_vars, normalized_ast)
    Where old_vars and new_vars are tuples of variables.
    normalized_ast(p(X,Y) & r(X)) returns (X,Y), (V0, V1), (p(V0,V1) & r(V0))
    normalized_ast(p(A,B) & r(A)) returns (A,B), (V0, V1), (p(V0,V1) & r(V0))
    """
    subs = dict()
    vs = []
    nvs = []
    for v in variables_ast(ast):
        if v not in subs:
            nv = lg.Var('V{}'.format(len(subs)), v.sort)
            subs[v.name] = nv
            vs.append(v)
            nvs.append(nv)
    nast = substitute_ast(ast, subs)
    return vs, nvs, nast

def normalize_named_binders(ast,names=None):
    """
    Normalize the variables bound by named binders, whose names are in
    names, or all named binders if names is None.

    Note: also recurs into formulas bound by named binders
    """
    if is_constant(ast):
        return ast
    if (is_named_binder(ast) and
        (names is None or ast.name in names)):
        vs = ast.variables
        nvs = [lg.Var('V{}'.format(i), v.sort)
               for i,v in enumerate(vs)]
        free = set(variables_ast(ast))
        assert all(nv not in free for nv in nvs)
        subs = dict((v.name,nv) for v,nv in zip(vs,nvs))
        b = normalize_named_binders(ast.body, names)
        b = substitute_ast(b, subs)
        return type(ast)(ast.name, nvs, ast.environ, b)
    args = [normalize_named_binders(x, names) for x in ast.args]
    if is_app(ast):
        return normalize_named_binders(ast.rep,names)(*args)
    else:
        return ast.clone(args)

def default_globally_binder(vs, t, env):
    name = 'g['+str(env)+']' if env is not None else 'g'
    return lg.NamedBinder(name, vs, t)

def replace_temporals_by_named_binder_g_ast(ast, g=default_globally_binder):
    """
    Replace temporal operators globally and eventually by a named
    binder g. Note that temporal operators inside formulas bound by
    named binders are also altered.
    """
    if type(ast) == lg.Globally:
        body = replace_temporals_by_named_binder_g_ast(ast.body, g)
        vs, nvs, body = normalize_free_variables(body)
        return g(nvs,body,ast.environ)(*vs)
    elif type(ast) == lg.Eventually:
        notbody = lg.Not(ast.body) #if type(ast.body) != lg.Not else ast.body.body
        return replace_temporals_by_named_binder_g_ast(lg.Not(lg.Globally(ast.environ,notbody)), g)
    else:
        args = [replace_temporals_by_named_binder_g_ast(x, g) for x in ast.args]
        if type(ast) == lg.Apply:
            func = replace_temporals_by_named_binder_g_ast(ast.func, g)
            return type(ast)(func, *args)
        else:
            return ast.clone(args)


def replace_named_binders_ast(ast,subs):
    """
    Replace named binders that are present in subs.  Here, subs is a
    dict from logic.NamedBinder objects to (usually) logic.Const
    objects. Exception is thrown in case of a sort conflict.

    Note: named binders do not get replaced in formulas bound by named binders!
    """
    if is_named_binder(ast):
        return subs.get(ast,ast)
    args = [replace_named_binders_ast(x, subs) for x in ast.args]
    if is_app(ast):
        return subs.get(ast.rep,ast.rep)(*args)
    return ast.clone(args)

def resort_sort(sort,subs):
    """
    Substitute sorts for sorts in a sort.
    """
    if isinstance(sort,UnionSort):
        res = UnionSort()
        res.sorts = [resort_sort(s,subs) for s in sort.sorts]
        return res
    if sort in subs:
        return subs[sort]
    if isinstance(sort,FunctionSort):
        return FunctionSort(*[resort_sort(s,subs) for s in (sort.dom+(sort.rng,))])
    return sort

def resort_symbol(sym,subs):
    return Symbol(sym.name,resort_sort(sym.sort,subs))

def resort_var(sym,subs):
    return Var(sym.name,resort_sort(sym.sort,subs))

def resort_ast(ast,subs):
    """
    Substitute sorts for sorts in an ast.
    """
    args = [resort_ast(x,subs) for x in ast.args]
    if is_app(ast):
        return resort_symbol(ast.rep)(*args)
    if is_quantifier(ast):
        return type(ast)([resort_var(x,subs) for x in quantifier_vars(ast)],resort_ast(quantifier_body(ast)))
    if is_variable(ast):
        return resort_var(ast,subs)
    return ast.clone(args)


def resort_sig(subs):
    ivy_logic.sig.symbols = dict((n,resort_symbol(s,subs)) for n,s in ivy_logic.sig.symbols.iteritems())
    refd = set(s.name for s in subs)
    ivy_logic.sig.sorts = dict((n,resort_sort(s,subs)) for n,s in ivy_logic.sig.sorts.iteritems() if n not in refd)
    ivy_logic.sig.interp = dict((n,s) for n,s in ivy_logic.sig.interp.iteritems() if n not in refd)


# aliases for backward compat
substitute_term = substitute_lit = substitute_ast
substitute_constants_term = substitute_constants_lit = substitute_constants_ast
rename_term = rename_lit = substitute_ast

# clauses and cubes are represented as lists of Literal (i.e., they
# are *not* formulas). here we extend the above functions to
# clauses, cubes and lists of these

substitute_clause = substitute_cube = apply_func_to_list(substitute_ast)
substitute_clauses = substitute_cubes = apply_func_to_clauses(substitute_ast)
substitute_constants_clause = substitute_constants_cube = apply_func_to_list(substitute_constants_ast)
substitute_constants_clauses = substitute_constants_cubes = apply_func_to_clauses(substitute_constants_ast)
rename_clause = rename_cube = apply_func_to_list(rename_ast)
def rename_clauses_annot_fun(annot,map):
    return None if annot is None else annot.rename(map)
rename_clauses = rename_cubes = apply_func_to_clauses(rename_ast, annot_fun = rename_clauses_annot_fun)
resort_clauses = resort_cubes = apply_func_to_clauses(resort_ast)


# get free variables

def variables_ast(ast):
    if isinstance(ast,Variable):
        yield ast
    elif is_binder(ast):
        bounds = set(binder_vars(ast))
        for a in binder_args(ast):
            for x in variables_ast(a):
                if x not in bounds:
                    yield x
    else:
        for arg in ast.args:
            for x in variables_ast(arg):
                yield x

# extend to clauses, etc...

variables_clause = variables_cube = used_variables_asts = apply_gen_to_list(variables_ast)
variables_clauses = variables_cubes = apply_gen_to_clauses(variables_ast)

# get set of variables occurring

used_variables_ast = gen_to_set(variables_ast)
used_variables_clause = gen_to_set(variables_clause)
used_variables_clauses = gen_to_set(variables_clauses)

# generate variables in order of first occurrence

used_variables_in_order_ast = gen_unique(variables_ast)
used_variables_in_order_clause = used_variables_in_order_cube = gen_unique(variables_clause)
used_variables_in_order_clauses = used_variables_in_order_cubes = gen_unique(variables_clauses)

# check if some variable occurs

uses_variables_ast = any_in(variables_ast)
uses_variables_clause = uses_variables_cube = any_in(variables_clause)
uses_variables_clauses = uses_variables_cubes = any_in(variables_clauses)

# same as above but for constants

def constants_ast(ast):
    if is_constant(ast):
        yield ast.rep
    else:
        for arg in ast.args:
            for x in constants_ast(arg):
                yield x

# extend to clauses, etc...

constants_clause = constants_cube = apply_gen_to_list(constants_ast)
constants_clauses = constants_cubes = apply_gen_to_clauses(constants_ast)

# get set of constants occurring

used_constants_ast = gen_to_set(constants_ast)
used_constants_clause = gen_to_set(constants_clause)
used_constants_clauses = gen_to_set(constants_clauses)

# generate constants in order of first occurrence

used_constants_in_order_ast = gen_unique(constants_ast)
used_constants_in_order_clause = used_constants_in_order_cube = gen_unique(constants_clause)
used_constants_in_order_clauses = used_constants_in_order_cubes = gen_unique(constants_clauses)

# check if some constant occurs

uses_constants_ast = any_in(constants_ast)
uses_constants_clause = uses_constants_cube = any_in(constants_clause)
uses_constants_clauses = uses_constants_cubes = any_in(constants_clauses)

# same as above but for symbols

def symbols_ast(ast):
    if is_app(ast):
        if is_binder(ast.rep):
            for x in symbols_ast(ast.rep.body):
                yield x
        else:
            yield ast.rep
    for arg in ast.args:
        for x in symbols_ast(arg):
            yield x

def named_binders_ast(ast):
    if is_named_binder(ast):
        yield ast
    elif is_app(ast):
        if is_named_binder(ast.rep):
            yield ast.rep
            for x in named_binders_ast(ast.rep.body):
                yield x
    for arg in ast.args:
        for x in named_binders_ast(arg):
            yield x

def temporals_ast(ast):
    if is_temporal(ast):
        yield ast
    elif is_app(ast):
        if is_named_binder(ast.rep):
            for x in temporals_ast(ast.rep.body):
                yield x
    for arg in ast.args:
        for x in temporals_ast(arg):
            yield x

def sorts_ast(ast):
    if is_app(ast):
        if is_binder(ast.rep):
            for x in sorts_ast(ast.rep.body):
                yield x
        else:
            yield ast.rep.sort.rng
            for s in ast.rep.sort.dom:
                yield s
    elif is_variable(ast):
        yield ast.sort
    for arg in ast.args:
        for x in sorts_ast(arg):
            yield x

# extend to clauses, etc...


symbols_asts = symbols_clause = symbols_cube = apply_gen_to_list(symbols_ast)
symbols_clauses = symbols_cubes = apply_gen_to_clauses(symbols_ast)

named_binders_asts = apply_gen_to_list(named_binders_ast)

temporals_asts = apply_gen_to_list(temporals_ast)

# get set of symbols occurring

used_symbols_ast = gen_to_set(symbols_ast)
used_symbols_asts = used_symbols_clause = gen_to_set(symbols_clause)
used_symbols_clauses = gen_to_set(symbols_clauses)

# get set of symbols occurring

used_sorts_ast = gen_to_set(sorts_ast)

# generate symbols in order of first occurrence

used_symbols_in_order_ast = gen_unique(symbols_ast)
used_symbols_in_order_clause = used_symbols_in_order_cube = gen_unique(symbols_clause)
used_symbols_in_order_clauses = used_symbols_in_order_cubes = gen_unique(symbols_clauses)

# check if some symbol occurs

uses_symbols_ast = any_in(symbols_ast)
uses_symbols_clause = uses_symbols_cube = any_in(symbols_clause)
uses_symbols_clauses = uses_symbols_cubes = any_in(symbols_clauses)

# similar to above but for relations. returns sequence of (name,arity) pairs. excludes =

def relations_ast(ast):
    if is_rel_app(ast):
        yield (ast.rep,len(ast.args))
    else:
        for arg in ast.args:
            for x in relations_ast(arg):
                yield x

# extend to clauses, etc...

relations_clause = relations_cube = apply_gen_to_list(relations_ast)
relations_clauses = relations_cubes = apply_gen_to_clauses(relations_ast)

# get dict of relations occurring with their arities

used_relations_ast = gen_to_dict(relations_ast)
used_relations_clause = gen_to_dict(relations_clause)
used_relations_clauses = gen_to_dict(relations_clauses)

# same as above, but for functions (includes constants). returns
# sequence of (name,arity) pairs

def functions_ast(ast):
    if is_app(ast) and is_individual(ast):
        yield (ast.rep,len(ast.args))
    else:
        for arg in ast.args:
            for x in functions_ast(arg):
                yield x

# extend to clauses, etc...

functions_clause = functions_cube = apply_gen_to_list(functions_ast)
functions_clauses = functions_cubes = apply_gen_to_clauses(functions_ast)

# get dict of functions occurring with their arities

used_functions_ast = gen_to_dict(functions_ast)
used_functions_clause = gen_to_dict(functions_clause)
used_functions_clauses = gen_to_dict(functions_clauses)


used_arity_relations_clause = used_arity_relations_cube = filter2(relations_clause)
used_arity_functions_clause = used_arity_functions_cube = filter2(functions_clause)
used_arity_relations_clauses = filter2(relations_clauses)
used_arity_functions_clauses = filter2(functions_clauses)

used_unary_relations_clause = used_unary_relations_cube = partial(used_arity_relations_clause,value2=1)
used_unary_functions_clause = used_unary_functions_cube = partial(used_arity_functions_clause,value2=1)
used_unary_relations_clauses = used_unary_relations_cubes = partial(used_arity_relations_clauses,value2=1)
used_unary_functions_clauses = used_unary_functions_cubes = partial(used_arity_functions_clauses,value2=1)

used_binary_relations_clause = used_binary_relations_cube = partial(used_arity_relations_clause,value2=2)
used_binary_functions_clause = used_binary_functions_cube = partial(used_arity_functions_clause,value2=2)
used_binary_relations_clauses = used_binary_relations_cubes = partial(used_arity_relations_clauses,value2=2)
used_binary_functions_clauses = used_binary_functions_cubes = partial(used_arity_functions_clauses,value2=2)

# get the atoms and apps (excluding equality atoms)

def apps_ast(ast):
    if is_app(ast):
        yield ast
    for arg in ast.args:
        for x in apps_ast(arg):
            yield x

# get the ground apps (excluding equality atoms)

def ground_apps_ast_rec(ast,res):
    if isinstance(ast,Variable) or is_quantifier(ast):
        return False
    ground = True
    for x in ast.args:
        ground &= ground_apps_ast_rec(x,res)
    if ground and is_app(ast):
        res.append(ast)
    return ground

def ground_apps_ast(ast):
    res = []
    ground_apps_ast_rec(ast,res)
    for x in res:
        yield x

# extend to clauses, etc...

apps_clause = apps_cube = apply_gen_to_list(apps_ast)
apps_clauses = apps_cubes = apply_gen_to_clauses(apps_ast)
ground_apps_clauses = ground_apps_cubes = apply_gen_to_clauses(ground_apps_ast)

# get the equality atoms

def eqs_ast(ast):
    if is_eq(ast):
        yield ast
    for arg in ast.args:
        for x in eqs_ast(arg):
            yield x

# extend to clauses, etc...

eqs_clause = eqs_cube = apply_gen_to_list(eqs_ast)
eqs_clauses = eqs_cubes = apply_gen_to_clauses(eqs_ast)


def is_equality_lit(lit):
    """ Returns true if lit is a positive equality """
    return lit.polarity == 1 and is_equals(lit.atom.rep)

def is_taut_equality_lit(lit):
    """ Returns true if lit is a positive equality """
    return lit.polarity == 1 and is_eq(lit.atom) and term_eq(lit.atom.args[0],lit.atom.args[1])

def is_vac_equality_lit(lit):
    """ Returns true if lit is a positive equality """
    return lit.polarity == 0 and is_eq(lit.atom) and term_eq(lit.atom.args[0],lit.atom.args[1])

def is_true(ast):
    return isinstance(ast,And) and not ast.args

def is_false(ast):
    return isinstance(ast,Or) and not ast.args

def is_true_lit(lit):
    return is_true(lit.atom) if lit.polarity == 1 else is_false(lit.atom)

def is_false_lit(lit):
    return is_true(lit.atom) if lit.polarity == 0 else is_false(lit.atom)

def is_taut_lit(lit):
    return is_true_lit(lit) or is_taut_equality_lit(lit)

def is_vac_lit(lit):
    return is_false_lit(lit) or is_vac_equality_lit(lit)

def is_disequality_lit(lit):
    """ Returns true if lit is a negative equality """
    return lit.polarity == 0 and is_equals(lit.atom.rep)

def is_ground_ast(ast):
    return not any(True for x in variables_ast(ast))

is_ground_atom = is_ground_lit = is_ground_ast

def is_ground_clause(clause):
    """ Returns true if clause is ground """
    return all(is_ground_lit(lit) for lit in clause)

def is_ground_equality_lit(lit):
    """ Returns true if lit is a positive ground equality """
    return is_equality_lit(lit) and is_ground_lit(lit)

# following for compat. use == instead

def term_eq(t1,t2):
    """ Returns true if terms are syntactically equal """
    return t1 == t2

def term_lists_eq(l1,l2):
    """ Returns true if terms lists syntactically equal """
    return l1 == l2

def atom_eq(at1,at2):
    """ Returns true lits are syntactically equal """
    return at1 == at2

def lit_eq(lit1,lit2):
    """ Returns true lits are syntactically equal """
    return lit1 == lit2

def swap_args_lit(lit):
    """ Swaps arguments of a binary literal """
    return Literal(lit.polarity,Atom(lit.atom.rep,[lit.atom.args[1],lit.atom.args[0]]))

def eq_lit(x,y):
    """ Returns literal x = y """
    return Literal(1,eq_atom(x,y))

def eq_atom(x,y):
    """ Returns atom x = y """
    return Equals(x,y)

def sym_placeholders(sym):
    """ Returns a list of n distinct variables """
    return [Variable('V'+str(i),t) for i,t in enumerate(sym.sort.dom)]

rel_placeholders = fun_placeholders = sym_placeholders

def rel_inst(relname):
    """ Apply relname to distinct variables """
    return Atom(relname,rel_placeholders(relname))

def fun_inst(funname):
    """ Apply function funname to distinct variables """
    return App(funname,*fun_placeholders(funname))

def fun_eq_inst(funname):
    return Equals(fun_inst(funname),Variable('W',funname.sort.rng))

def sym_inst(sym):
    if is_relational(sym):
        return Atom(sym,rel_placeholders(sym))
    return sym(*fun_placeholders(sym))

def is_relational(sym):
    return sym.is_relation()


tseitin_context = None

class TseitinContext(object):
    """ Context Manager that handles exceptions and reports errors. """
    def __init__(self,used = None):
        self.clauses = []
        self.used = used if used else {}
        self.fresh = UniqueRenamer('__ts',self.used)
    def __enter__(self):
        global tseitin_context
        self.save = tseitin_context
        tseitin_context = self
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global tseitin_context
        tseitin_context = self.save
    def add_defs(self,cls):
        return cls + self.clauses

def tseitin_encoding(f):
    global tseitin_context
    tc = tseitin_context
    if not tc:
        print f
        print type(f)
        raise ValueError()
    f = expand_abbrevs(f)
    if isinstance(f,And):
        args = [tseitin_encoding(g) for g in f.args]
##        print "args: %s" % args
        # TODO: this has to handle variables of different sorts and
        # must handle sort clashes for the Tseitin symbols
        vs = [v for v in used_variables_in_order_clause(args)]
        fname = tc.fresh(str(len(vs)))
        ty = RelationSort([v.get_sort() for v in vs])
        fn = Symbol(fname,ty)
##        print "fn = {}, ty = {}".format(fn,ty)
        res = Literal(1,Atom(fn,vs))
        tc.clauses += [[~res,arg] for arg in args]
        tc.clauses.append([res] + [~arg for arg in args])
        return res
    if isinstance(f,Or):
        return ~tseitin_encoding(And(*[Not(x) for x in f.args]))
    if isinstance(f,Not):
        return ~tseitin_encoding(f.args[0])
    if is_atom(f):
        return Literal(1,f)
#    print "bad formula: {} : {}".format(f,type(f))
    raise ValueError

def condition_conj(c,p):
    ps = p.args if isinstance(p,And) else [p]
    return [Or(c,q) for q in ps]

def expand_abbrevs(f):
    if isinstance(f,Implies):
        return Or(negate(f.args[0]),f.args[1])
    if isinstance(f,Iff):
        if isinstance(f.args[1],Ite):
            lhs,ite = f.args
            thenp = expand_abbrevs(Iff(lhs,ite.args[1]))
            elsep = expand_abbrevs(Iff(lhs,ite.args[2]))
            return expand_abbrevs(Ite(ite.args[0],thenp,elsep))
        if is_true(f.args[1]):
            f.args[0]
        if is_false(f.args[1]):
            negate(f.args[0])
        return And(Or(negate(f.args[0]),f.args[1]),
                   Or(negate(f.args[1]),f.args[0]))
    if isinstance(f,Ite):
        thenps = condition_conj(negate(f.args[0]),f.args[1])
        elseps = condition_conj(f.args[0],f.args[2])
        return And(*(thenps + elseps))
    return f

def formula_to_lit(f):
    f = expand_abbrevs(f)
    if isinstance(f,Not):
        return ~formula_to_lit(f.args[0])
    if is_atom(f):
        return Literal(1,f)
    return tseitin_encoding(f)

def formula_to_clause(f):
    f = expand_abbrevs(f)
    f = de_morgan(f)
    if is_true(f):
        return [Literal(1,f)]
    if not isinstance(f,Or):
        return [formula_to_lit(f)]
    return [y for x in f.args for y in formula_to_clause(x)]

def formula_to_cube(f):
    f = expand_abbrevs(f)
    if isinstance(f,Not):
        return [~lit for lit in formula_to_clause(f.args[0])] # De Morgan
    lits = f.args if isinstance(f,And) else [f]
    return [formula_to_lit(x) for x in lits]

def negate(f):
    if isinstance(f,Not):
        return f.args[0]
    return Not(f)

def de_morgan(f):
    """ remove negations from formula by applying de Morgans' laws """
    f = expand_abbrevs(f)
    if not isinstance(f,Not):
        return f
    g = de_morgan(f.args[0])
    if isinstance(g,And):
        if len(g.args) == 1: return de_morgan(negate(g.args[0]))
        return Or(*[negate(x) for x in g.args])
    if isinstance(g,Or):
        if len(g.args) == 1: return de_morgan(negate(g.args[0]))
        return And(*[negate(x) for x in g.args])
    return Not(g)

def formula_to_clauses(f,annot=None):
    if type(f) in (lg.And, lg.Or) and len(f) == 1:
        f = f[0]
#    assert is_prenex_universal(f), f
    return Clauses([drop_universals(f)],annot=annot)

formula_to_clauses_tseitin = formula_to_clauses

def formula_to_clauses_aux(f):
    """ Clausify a formula. Outside of a TseitinContext, this requires that
    the formula is in CNF and with raise ValueException otherwise. Within a
    TseitinContext will do Tseitin encoding. """
#    print "ftc: {} : {} : {}".format(f,type(f),And)
    f = drop_universals(f)
    f = de_morgan(f)
#    print "ftc: {} : {} : {}".format(f,type(f),And)
    if is_false(f):
        return [[]]
    if not(isinstance(f,And)):
        cls = formula_to_clause(f)
        return [] if any(is_taut_lit(lit) for lit in cls) else [cls]
    return [y for x in f.args for y in formula_to_clauses_aux(x)]

def tseitin_encode(f):
    """ Clausify a formula. This can introduce skolems which will be distinct
    from all existing symbols in f."""
    tc = TseitinContext()
    with tc:
        clauses = formula_to_clauses_aux(f)
##    print "tseitin: {}".format(clauses + tc.clauses)
    return tc.add_defs(clauses)


def condition_clauses(clauses,fmla):
    """ return clauses equivalent to fmla -> clauses """
    fmla = negate(fmla)
    # Note here: clauses may already contain Tseitin symbols
    tc = TseitinContext(used_symbols_clauses(clauses))
    with tc:
        clauses = [cl1 for cl in clauses for cl1 in formula_to_clauses(Or(fmla,clause_to_formula(cl)))]
##    print "tseitin: {}".format(clauses + tc.clauses)
    return clauses + tc.clauses

def lit_to_formula(lit):
    return lit.atom if lit.polarity == 1 else Not(lit.atom)

def cube_to_formula(c):
    return And(*(lit_to_formula(lit) for lit in c))

def clause_to_formula(c):
    lits = [lit_to_formula(lit) for lit in c]
    return Or(*lits) if len(lits) != 1 else lits[0]

def clauses_to_formula(cs):
    formula = cs.to_formula()
    return drop_universals(formula)

def subst_both_clauses(clauses,subst):
    """ apply subsitution to both variables and constants in a clause """
    return substitute_constants_clauses(substitute_clauses(clauses,subst),subst)

def clauses_using_symbols(syms,clauses):
    return Clauses([f for f in clauses.fmlas if uses_symbols_ast(syms,f)],
                   clauses.defs)

def canonize_clause(cl):
    """ rewrite clause so that variables occur in order V0, V1, ..."""
    vs = used_variables_in_order_clause(cl)
    subst = dict((v,Variable('V' + str(i),v.sort)) for i,v in enumerate(vs))
    return substitute_clause(cl,subst)

def simplify_clauses(cls):
    fmlas = cls.fmlas
    for i in range(3):
        fmlas = [simplify_clause_fmla(cl) for cl in fmlas]
        fmlas = [cl for cl in fmlas if not is_tautology_fmla(cl)]
#        fmlas = reduce_fmlas(fmlas)
    return Clauses(fmlas,cls.defs)

def trim_clauses(cls):
    """ remove unused let bindings from a Clauses """
    used_syms = set()
    seeds = list(cls.fmlas)
    seeds += [d.args[1] for d in cls.defs if not(d.args[0].rep.is_skolem())]
    while seeds:
        seed = seeds.pop()
        syms = used_symbols_ast(seed)
        for sym in syms:
            if sym.is_skolem() and sym not in used_syms and sym in cls.defidx:
                used_syms.add(sym)
                seeds.append(cls.defidx[sym].args[1])
    newdefs = [d for d in cls.defs if (not d.args[0].rep.is_skolem() or d.args[0].rep in used_syms)]
    return Clauses(cls.fmlas,newdefs)

def rewrite_clause(clause,v,t):
    subs = dict()
    subs[v.rep] = t
    return substitute_clause(clause,subs)

def triv_fmla_to_lit(f):
    if isinstance(f,Not):
        return Literal(0,f.args[0])
    return Literal(1,f)

def collect_or(fmla):
    if isinstance(fmla,Or):
        return [f for g in fmla.args for f in collect_or(g)]
    return [fmla]

def collect_and_list(fmlas):
    for fmla in fmlas:
        if isinstance(fmla,And):
            for c in collect_and_list(fmla.args):
                yield c
        else:
            yield fmla

def triv_fmla_to_clause(fmla):
    return [triv_fmla_to_lit(f) for f in collect_or(fmla)]

def simplify_clause_fmla(fmla):
    return clause_to_formula(simplify_clause(triv_fmla_to_clause(fmla)))


def simplify_clause(clause):
    for lit in clause:
        if lit.polarity == 0 and is_eq(lit.atom):
            for i in [0,1]:
                if isinstance(lit.atom.args[i],Variable):
                    clause = rewrite_clause(clause,lit.atom.args[i],lit.atom.args[1-i])
                    break
    if any(is_taut_lit(lit) for lit in clause):
        return [Literal(1,And())]
    return remove_duplicates([lit for lit in clause if not is_vac_lit(lit)])

def is_tautology(clause):
    for lit in clause:
        if is_taut_lit(lit):
            return True
        for lit2 in clause:
            if lit.polarity != lit2.polarity and lit.atom == lit2.atom:
                return True
    return False

def is_tautology_fmla(fmla):
    return is_tautology(triv_fmla_to_clause(fmla))

def lit_in_clause(lit1,clause):
    for lit2 in clause:
        if lit1.polarity == lit2.polarity and lit1.atom == lit2.atom:
            return True
    return False

def remove_duplicates(clause):
    res = []
    for lit1 in clause:
        if not lit_in_clause(lit1,res):
            res.append(lit1)
    return res

def reduce_clauses(clauses):
    """
    Reduce a clause set by eliminating redundant clauses
    """
    used = []
    unexplored = clauses
    while unexplored:
        cl, unexplored = unexplored[0], unexplored[1:]
        if not subsume(used, cl) and not subsume(unexplored,cl):
          used.append(cl)
    return used

# TODO: these don't handle functions

def term_subsume(term1, term2, env):
    """
    Try to make term1 match term2 (env only operates on term1)
    """
    if is_constant(term1):
        if not (is_constant(term2) and term1.rep == term2.rep and len(term1.args) == len(term2.args)):
            return False
        return all(term_subsume(a1,a2,env) for a1,a2 in zip(term1.args,term2.args))
    else:
        if not (term1.rep in env):
            env[term1.rep] = term2
            return True
        return env[term1.rep] == term2

def lit_subsume(lit1, lit2, env):
    """
    Try to make lit1 match lit2 (env only operates on lit1)
    """
    if lit1.polarity != lit2.polarity or lit1.atom.relname != lit2.atom.relname or len(lit1.atom.args) != len(lit2.atom.args):
        return False
    for t1,t2 in zip(lit1.atom.args, lit2.atom.args):
        if not term_subsume(t1, t2, env):
            return False
    return True

def atom_subsume(at1, at2):
    """
    Try to make atoms at1 match at2
    """
    env = dict()
    if  at1.relname != at2.relname or len(at1.args) != len(at2.args):
        return False
    for t1,t2 in zip(at1.args, at2.args):
        if not term_subsume(t1, t2, env):
            return False
    return True

def commute_lit(lit2):
    return Literal(lit2.polarity,Atom(lit2.atom.relname,[lit2.atom.args[1],lit2.atom.args[0]]))

def clause_subsume_recur(cl1,cl2,env):
    """
    Recuresively try all possibilities of making cl1 subsume cl2, return True on success.
    """
    if not cl1:
        return True
    lit, rest = cl1[0], cl1[1:]
    for lit2 in cl2:
        env_copy = env.copy()
        if lit_subsume(lit, lit2, env):
            if clause_subsume_recur(rest, [l for l in cl2 if l is not lit2], env):
                # should we really use is here? think about [lit1, lit2, lit1]
                return True
        env = env_copy
        if lit.polarity == lit2.polarity and is_equals(lit.atom.rep) and is_equals(lit2.atom.rep) and len(lit2.atom.args) == 2:
            env_copy = env.copy()
            if lit_subsume(lit, commute_lit(lit2), env):
                if clause_subsume_recur(rest, [l for l in cl2 if l is not lit2], env):
                    # should we really use is here? think about [lit1, lit2, lit1]
                    return True
            env = env_copy
    return False

#
def clause_subsume(cl1, cl2):
    """
    Return True iff cl2 is subsumed by cl1 (i.e., cl1 => cl2).
    """
    env = dict()
    return clause_subsume_recur(cl1,cl2,env)

def subsume(clauses, cl):
    """
    Return True iff cl is subsumed by a clause in clauses
    """
    for clp in clauses:
      if clause_subsume(clp, cl):
         return True
    return False

def distinct_variable_renaming(vars1,vars2):
    rn = UniqueRenamer('',(v.rep for v in vars2))
    return dict((v.rep,rename_variable(v,rn(v.rep))) for v in vars1)

def rename_variable(v,name):
    return type(v)(name,v.sort)

def used_variable_names_ast(ast):
    for v in used_variables_ast(ast):
        yield v.rep

def variables_distinct_ast(ast1,ast2):
    """ rename variables in ast1 so they don't occur in ast2.
    """
    map1 = distinct_variable_renaming(used_variables_ast(ast1),used_variables_ast(ast2))
    return substitute_ast(ast1,map1)

def rename_variables_distinct_asts(vars,asts):
    """ rename variables in vars so they don't occur in asts.
    """
    map1 = distinct_variable_renaming(vars,used_variables_asts(asts))
    return [map1[v.name] for v in vars]

def variables_distinct_list_ast(ast_list,ast2):
    """ rename variables in ast_list so they don't occur in ast2.
    """
    return variables_distinct_ast(Atom('#',ast_list),ast2).args

def is_individual_ast(ast):
    return is_individual(ast)



def or_clauses2(clauses1,clauses2):
    """ Take the logical or of two clause sets. """

    if not clauses1 or not clauses2: return []
    if [] in clauses1: return clauses2
    if [] in clauses2: return clauses1

    used = used_symbols_clauses(clauses1 + clauses2);
    v = bool_const(UniqueRenamer('__ts',used)())

    clauses1 = [[Literal(1,v)] + c for c in clauses1]
    clauses2 = [[Literal(0,v)] + c for c in clauses2]
    return clauses1 + clauses2

def coerce_args_to_clauses(args):
    return [(a if isinstance(a,Clauses) else formula_to_clauses(a)) for a in args]

def fix_or_annot(res,vs,args):
    if len(args) == 0:
        return res
    annots = [a.annot for a in args]
    annot = annots[0]
    for a,v in zip(annots[1:],vs[1:]):
        annot = None if annot is None or a is None else a.ite(v,annot)
    return Clauses(res.fmlas,res.defs,annot)

def or_clauses(*args):
    if not any(isinstance(a,Clauses) for a in args):
        return Or(*args)
    args = coerce_args_to_clauses(args)
    orig_args = list(args)
#    args = [a for a in args if not a.is_false() or a.annot is not None]
    args = [a for a in args if not a.is_false()]
    if len(args) == 0:
        res,vs = false_clauses(),[]
    elif len(args) == 1:
        res,vs = args[0],[And()]
    else:
        used = set(chain(*[arg.symbols() for arg in args]))
        rn = UniqueRenamer('__ts0',used)
        res,vs,args = or_clauses_int(rn,args)
    fixed_vs = []
    fixed_args = []
    idx = 0
    for a in orig_args:
        if a.is_false():
            fixed_vs.append(Or())
            fixed_args.append(a)
        else:
            fixed_vs.append(vs[idx])
            fixed_args.append(args[idx])
            idx += 1
    return fix_or_annot(res,fixed_vs,fixed_args)


def ite_clauses(cond,args):
    assert len(args) == 2
    args = coerce_args_to_clauses(args)
    if args[0].is_false() and args[1].is_false():
        return args[0]
    if args[0].is_false():
        args[0] = Clauses(args[0].fmlas,args[1].defs,args[0].annot) 
    elif args[1].is_false():
        args[1] = Clauses(args[1].fmlas,args[0].defs,args[1].annot) 
    used = set(chain(*[arg.symbols() for arg in args]))
    used.update(symbols_ast(cond))
    rn = UniqueRenamer('__ts0',used)
    return ite_clauses_int(rn,cond,args)

def elim_definitions(clauses,dead):
    c2 = clauses.copy()
    fmlas = clauses.fmlas
    for sym in dead:
        if sym in clauses.defidx:
            fmlas.append(c2.defidx[sym].to_constraint())
#    print "elim_definitions fmlas = {}".format(["%s" % f for f in fmlas])
    deadset = set(dead)
    defs = [d for d in clauses.defs if d.defines() not in deadset]
    return Clauses(fmlas,defs,clauses.annot)

def rename_symbols(rn,clauses1,to_rename):
    map1 = dict((s,s.rename(rn)) for s in to_rename)
    return rename_clauses(clauses1,map1)


def elim_dead_definitions(rn,args):
    """ If a symbol defined in one arg occurs free in another,
    then eliminate the definition by converting it to clauses """
    defd = set(d.defines() for a in args for d in a.defs)
    occurs = [set(a.symbols()) for a in args]
    captured = [sym for sym in defd if any (sym not in a.defidx for a in args)]
    dead = [sym for sym in captured if not sym.is_skolem()]
    to_rename = [sym for sym in captured if sym.is_skolem()]
    args = [rename_symbols(rn,arg,to_rename) for arg in args]
#    print "args = {}, dead = {}".format(args,dead)
    res = [elim_definitions(a,dead) for a in args]
    return res

def or_clauses_int(rn,args):
#    print "or_clauses_int: args = {}".format(args)
    args = elim_dead_definitions(rn,args)
#    print "or_clauses_int: args = {}".format(args)
    vs = [bool_const(rn()) for a in args]
    fmlas = ([Or(*vs)]
               + [Or(Not(v),cl) for cls,v in zip(args,vs) for cl in cls.fmlas])
    defidx = dict()
    for cls,v in zip(args,vs):
        for d in cls.defs:
            s = d.defines()
            if s not in defidx:
                defidx[s] = d
            else:
                defidx[s] = Definition(d.args[0],Ite(v,d.args[1],defidx[s].args[1]))
    defs = [d for n,d in defidx.iteritems()] # TODO: hash traversal dependency
    res = Clauses(fmlas,defs)
    #    print "or_clauses_int res = {}".format(res)
    return res,vs,args

def debug_clauses_list(cl):
    for clauses in cl:
        print "definitions:"
        for df in clauses.defs:
            print df
        print "fmlas:"
        for fmla in clauses.fmlas:
            print ivy_logic.close_formula(fmla)

def ite_clauses_int(rn,cond,args):
    assert len(args) == 2
    # print "ite_clauses_int args:"
    # debug_clauses_list(args)
    args = elim_dead_definitions(rn,args)
    a0,a1 = args[0].annot,args[1].annot
#    print "or_clauses_int: args = {}".format(args)
    v = bool_const(rn())
#    argfmlas = [cls.fmlas[0] if len(cls.fmlas) == 1 else And(*cls.fmlas) for cls in args]
#    fmlas = [simp_ite(v,argfmlas[0],argfmlas[1])]
    fmlas = ([Or(Not(v),f) for f in args[0].fmlas]
             + [Or(v,f) for f in args[1].fmlas])
    defidx = dict()
    for d in args[0].defs:
        s = d.defines()
        defidx[s] = d
    for d in args[1].defs:
        s = d.defines()
        if s not in defidx:
            defidx[s] = d
        else:
            defidx[s] = Definition(d.args[0],simp_ite(v,defidx[s].args[1],d.args[1]))
    defs = [d for n,d in defidx.iteritems()] + [Definition(v,cond)] # TODO: hash traversal dependency
    annot = None if a0 is None or a1 is None else a0.ite(v,a1)
    res = Clauses(fmlas,defs,annot)
    # print "ite_clauses_int res:"
    # debug_clauses_list([res])
    return res

def bool_const(name):
    return Atom(Symbol(name,RelationSort([])),[])

def tagged_or_clauses(prefix,*args):
    """Same as or_clauses, but gives each disjunct a unique "tag" predicate
    that can be used to determine which disjunct is true in a model. The tag
    predicate symbols begin with "prefix". See find_true_disjunct.
    """
    args = coerce_args_to_clauses(args)
    res,vs,args = or_clauses_int(UniqueRenamer('__to0',dict()),args)
    return fix_or_annot(res,vs,args)

def find_true_disjunct(clauses,eval_fun):
    """See tagged_or_clauses. If a tagged disjunction is satisfiable,
    return the index of some true disjunct. Here, "eval_fun" returns the
    truth value of a predicate symbol in the satisfying assignment.
    We assume fmla is the result of tagged_or_clauses. Returns None if
    no disjunct is true.

    TODO: this is done by linear search, but could be binary search if
    tagged_or_clauses is implement appropriately.
    """
    for idx,atom in enumerate(clauses.fmlas[0].args):
        if eval_fun(atom):
            return idx
    return None


#    return reduce(or_clauses2,args)


def and_clauses(*args,**kwargs):
    if not any(isinstance(a,Clauses) for a in args):
        return And(*args)
    args = coerce_args_to_clauses(args)
    if not args:
        return true_clauses()

    annot_op = kwargs.pop('annot_op',None)
    if annot_op is None:
        annot = None
        for a in args:
            annot = a.annot if annot is None else annot if a.annot is None else annot.conj(a.annot)
    else:
         annot = annot_op(*[c.annot for c in args])
         
    if any(cls.is_false() for cls in args):
        return false_clauses(annot=annot)
    fmlas = [c for cls in args for c in cls.fmlas]
    defs = [d for cls in args for d in cls.defs]
    return Clauses(fmlas,defs,annot)

def negate_clauses(clauses):
    if isinstance(clauses,Clauses):
        assert clauses.is_universal_first_order()
        return dual_clauses(clauses)
        #TODO: change this to "Not(clauses.to_formula())"
    return Not(clauses)

def eqcm_upd(lhs,rhs,symset,map2):
    if lhs in symset and is_constant(rhs):
        symset.remove(lhs)
        r,l = map2[rhs],map2[lhs]
        r.append(lhs)
        r.extend(l)
        del l[:]
        return True
    return False

def exists_quant_clauses_map(syms,clauses):
    used = used_symbols_clauses(clauses)
    symset = set(syms)
    map1 = dict()
    map2 = defaultdict(list)
    defs = []
    for df in clauses.defs:
        lhs,rhs = df.args
        if not eqcm_upd(lhs,rhs,symset,map2):
            if not eqcm_upd(rhs,lhs,symset,map2):
                defs.append(df)
    for v,w in map2.iteritems():
        for x in w:
            map1[x] = v
    clauses = Clauses(clauses.fmlas,defs)
    rn = UniqueRenamer('__',used)
    for s in syms:
        map1[s] = rename(s,rn)
    return map1,rename_clauses(clauses,map1)


def has_enumerated_sort(sig,sym):
    sort = sym.sort
    return (isinstance(sort,EnumeratedSort) or
               isinstance(sort,FunctionSort) and isinstance(sort.rng,EnumeratedSort))

def var_to_skolem(pref,v):
    return var_to_constant(v,pref + v.name)

def var_to_constant(v,name):
    sym = Symbol(name,v.sort)
    return Constant(sym)


def false_clauses(annot=None):
    return Clauses([[]],annot=annot)


def true_clauses(annot=None):
    return Clauses([],annot=annot)

instantiator = None

def definition_instances(fmla):
    if instantiator != None:
        gts = apps_ast(fmla)
        return instantiator(gts)
    return Clauses([])

def unfold_definitions_clauses(clauses):
    if instantiator != None:
        gts = apps_clauses(clauses)
        insts = instantiator(gts)
        if insts.fmlas:
            clauses = and_clauses(clauses,insts)
    return clauses

def dual_clauses(clauses, skolemizer=None):
    if skolemizer == None:
        skolemizer = lambda v: var_to_skolem('__',Variable(v.rep,v.sort))
    vs = used_variables_in_order_clauses(clauses)
    sksubs = dict((v.rep,skolemizer(v)) for v in vs)
    clauses = substitute_clauses(clauses,sksubs)
    fmla = negate(clauses_to_formula(clauses))
    if instantiator != None:
        gts = apps_clauses(clauses)
        insts = instantiator(gts)
        fmla = And(fmla,clauses_to_formula(insts))
    return formula_to_clauses(fmla)

def dual_formula(fmla, skolemizer=None):
    if skolemizer == None:
        skolemizer = lambda v: var_to_skolem('__',Variable(v.rep,v.sort))
    vs = used_variables_in_order_ast(fmla)
    sksubs = dict((v.rep,skolemizer(v)) for v in vs)
    fmla = negate(substitute_ast(fmla,sksubs))
    if instantiator != None:
        gts = apps_ast(fmla)
        insts = clauses_to_formula(instantiator(gts))
        fmla = And(fmla,insts)
    return fmla

def skolemize_formula(fmla, skolemizer=None):
    if skolemizer == None:
        skolemizer = lambda v: var_to_skolem('__sk__',Variable(v.rep,v.sort))
    vs = []
    while is_exists(fmla):
        vs.extend(fmla.variables)
        fmla = fmla.body
    sksubs = dict((v.rep,skolemizer(v)) for v in vs)
    fmla = substitute_ast(fmla,sksubs)
    if instantiator != None:
        gts = apps_ast(fmla)
        insts = clauses_to_formula(instantiator(gts))
        fmla = And(fmla,insts)
    return fmla

def reskolemize_clauses(clauses, skolemizer):
    print clauses
    cs = [c for c in used_constants_clauses(clauses) if '__' in c.rep]
#    print "reskolemize_clauses c = {}".format(cs)
    sksubs = dict((c,skolemizer(Variable(c.rep,c.sort))) for c in cs)
    return substitute_constants_clauses(clauses,sksubs)

def unused_constant(used_constants,sort):
    """Return a constant name which is not in current sig and not in used names.
    """
    used_names = set(repr(a) for a in used_constants)
    for s in ivy_logic.sig.symbols:
        used_names.add(s)
#    print "used_names: {}".format(used_names)
    for name in constant_name_generator():
        if name not in used_names:
#            print "name: {}".format(name)
            return Symbol(name,sort)

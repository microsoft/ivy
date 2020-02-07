#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
# following are just to make sure these encodings are loaded, since z3 needs them
import encodings.ascii
import encodings.latin_1

import itertools
from itertools import chain
from collections import defaultdict
import re
import functools

import z3
import ivy_logic
from ivy_logic_utils import used_variables_clause, used_variables_ast, variables_ast,\
   to_clauses, constants_clauses, used_relations_clauses, rel_inst, fun_eq_inst, \
   is_ground_lit, used_constants_clauses, substitute_constants_clauses, eq_atom, \
   functions_clauses, fun_inst, substitute_lit, used_constants_clause, used_symbols_clause,Clauses, used_symbols_clause, and_clauses, true_clauses, used_symbols_ast, sym_placeholders, used_symbols_clauses, ground_apps_clauses, dual_clauses
from ivy_core import minimize_core, biased_core
import ivy_utils as iu
import ivy_unitres as ur
import logic as lg

import sys

# Following accounts for Z3 API symbols that are hidden as of Z3-4.5.0

z3_to_ast_array = z3._to_ast_array if '_to_ast_array' in z3.__dict__ else z3.z3._to_ast_array
z3_to_expr_ref = z3._to_expr_ref if '_to_expr_ref' in z3.__dict__ else z3.z3._to_expr_ref

use_z3_enums = True

def set_seed(seed):
    print 'setting seed to {}'.format(seed)
    z3.set_param('smt.random_seed',seed)

opt_seed = iu.Parameter("seed",0,process=int)
opt_seed.set_callback(set_seed)

def set_macro_finder(truth):
    z3.set_param('smt.macro_finder',truth)
    
opt_incremental = iu.BooleanParameter("incremental",True)
opt_show_vcs = iu.BooleanParameter("show_vcs",False)

#z3.set_param('smt.mbqi.trace',True)
opt_macro_finder = iu.BooleanParameter("macro_finder",True)
set_macro_finder(True)
opt_macro_finder.set_callback(set_macro_finder)

def set_use_native_enums(t):
    global use_z3_enums
    use_z3_enums = t


z3_builtins = set(["bit0","bit1"])

def solver_name(symbol):
    name = symbol.name
    if name.startswith('bfe['):
        if bfe_to_z3(symbol) is not None:
            return None
    elif name in iu.polymorphic_symbols:
        sort = symbol.sort.domain[0].name
        if sort in ivy_logic.sig.interp and not isinstance(ivy_logic.sig.interp[sort],ivy_logic.EnumeratedSort):
            return None
#        name += ':' + sort
        for s in symbol.sort.domain:
            name += ':' + s.name
    if name in ivy_logic.sig.interp:
        return None
    if name in z3_builtins:
        raise iu.IvyError(None,'name "{}" clashes with Z3 built-in'.format(name))
    return name
    #    return '_' + name if isinstance(symbol,ivy_logic.Symbol) and name[0].isalpha() else name

# S = z3.DeclareSort("S")

def my_minus(*args):
    if len(args) == 1:
        return -args[0]
    return args[0] - args[1]

def my_eq(x,y):
    ctx = z3.main_ctx()
#    print "my_eq: {} = {}".format(x,y)
    return z3.BoolRef(z3.Z3_mk_eq(ctx.ref(), x.as_ast(), y.as_ast()), ctx)

z3_sort_parser = re.compile(r'bv\[[0-9]+\]')

def sorts(name):
    if name.startswith('bv[') and name.endswith(']'):
        width = int(name[3:-1])
        return z3.BitVecSort(width)
    if name.startswith('strbv[') and name.endswith(']'):
        width = int(name[6:-1])
        return z3.BitVecSort(width)
    if name.startswith('intbv[') and name.endswith(']'):
        width = int(name[name.rfind('[')+1:-1])
        return z3.BitVecSort(width)
    if name == 'int':
        return z3.IntSort()
    if name == 'nat':
        return z3.IntSort()
    if name == 'strlit':
        return z3.StringSort()
    return None
        
#sorts = {}
#sorts = {"S":S,
#         "Int":z3.IntSort()}

def parse_int_params(name):
    things = name.split('[')[1:]
#    print "things:".format(things)
    if not all(t.endswith(']') for t in things):
        raise SyntaxError()
    return [int(t[:-1]) for t in things]
    

def is_solver_sort(name):
    return name.startswith('bv[') and name.endswith(']') or name == 'int' or name == 'nat' or name == 'strlit' or name.startswith('strbv[') or name.startswith('intbv[')

relations_dict = {'<':(lambda x,y: z3.ULT(x, y) if z3.is_bv(x) else x < y),
             '<=':(lambda x,y: z3.ULE(x, y) if z3.is_bv(x) else x <= y),
             '>':(lambda x,y: z3.UGT(x, y) if z3.is_bv(x) else x > y),
             '>=':(lambda x,y: z3.UGE(x, y) if z3.is_bv(x) else x >= y),
             }

def relations(name):
    return relations_dict.get(name)

functions_dict = {"+":(lambda x,y: x + y),
             "-":my_minus,
             "*":(lambda x,y: x * y),
             "/":(lambda x,y: x / y),
             "concat":(lambda x,y: z3.Concat(x,y)),
             "bvand":(lambda x,y: x & y),
             "bvor":(lambda x,y: x | y),
             "bvnot":(lambda x: ~x),
             }

def bfe_to_z3(sym):
    try:
        things = parse_int_params(sym.name)
    except:
        return None
    if len(things) == 2:
        lo,hi = things
        insort = sym.sort.dom[0].to_z3()
        outsort = sym.sort.rng.to_z3()
#        assert (z3.is_bv_sort(insort) and z3.is_bv_sort(outsort))
        if not z3.is_bv_sort(insort):
            return None
        if insort.size() <= hi:
            hi = insort.size() - 1
        if outsort == z3.IntSort():
            if hi < lo:
                return lambda x: z3.IntVal(0)
            return lambda x: z3.BV2Int(z3.Extract(hi,lo,x))
        if not z3.is_bv_sort(outsort):
            return None
        if outsort.size() < hi - lo + 1:
            hi = lo + outsort.size() - 1
        if hi < lo:
            return lambda x: z3.BitVecVal(0,outsort.size())
        elif hi - lo + 1 < outsort.size():
            return lambda x: z3.Concat(z3.BitVecVal(0,outsort.size() - (hi - lo + 1)),z3.Extract(hi,lo,x))
        else:
            return lambda x: z3.Extract(hi,lo,x)


    
def functions(name):
    # if name.startswith('bfe['):
    #     try:
    #         things = parse_int_params(name)
    #         if len(things) == 2:
    #             lo,hi = things
    #             return lambda x: my_z3_extract(hi,lo,x)
    #     except:
    #         return None
    return functions_dict.get(name)

def is_solver_op(name):
    return relations(name) != None or functions(name) != None


def clear():
    global z3_sorts, z3_predicates, z3_constants, z3_functions
    z3_sorts = dict()
    z3_predicates = {ivy_logic.equals : my_eq}
    z3_constants = dict()
    z3_functions = dict()

clear()    

#z3_sorts_inv = dict((get_id(z3sort),ivysort) for ivysort,z3sort in z3_sorts.iteritems())
z3_sorts_inv = {}

def uninterpretedsort(us):
    s = z3_sorts.get(us.rep,None)
    if s is not None: return s
    s = lookup_native(us,sorts,"sort")
    if s == None:
        s = z3.DeclareSort(us.rep)
    z3_sorts[us.rep] = s
    z3_sorts_inv[get_id(s)] = us
    return s

def functionsort(fs):
#    print "fs.rng = {!r}".format(fs.rng)
    if fs.is_relational():
        return [s.to_z3() for s in fs.dom] + [z3.BoolSort()]
    return [s.to_z3() for s in fs.dom] + [fs.rng.to_z3()]

def enumeratedsort(es):
    res,consts = z3.EnumSort(es.name,es.extension)
    for c in consts:
        z3_constants[str(c)] = c
#    print "enum {} : {}".format(res,type(res))
    return res

def symbol_to_z3(s):
    return z3.Const(s.name, s.sort.to_z3()) if s.sort.dom == [] else z3.Function(s.name,s.sort.to_z3())    

ivy_logic.UninterpretedSort.to_z3 = uninterpretedsort
ivy_logic.FunctionSort.to_z3 = functionsort
ivy_logic.EnumeratedSort.to_z3 = enumeratedsort
ivy_logic.BooleanSort.to_z3 = lambda self: z3.BoolSort()
ivy_logic.Symbol.to_z3 = symbol_to_z3


def lookup_native(thing,table,kind):
    z3name = ivy_logic.sig.interp.get(thing.name)
    if z3name == None:
        if  thing.name.startswith('bfe['):
            return bfe_to_z3(thing)
        if thing.name in iu.polymorphic_symbols:
            sort = thing.sort.domain[0].name
            if sort in ivy_logic.sig.interp and not isinstance(ivy_logic.sig.interp[sort],ivy_logic.EnumeratedSort):
                if thing.name == '-' and ivy_logic.sig.interp[sort] == 'nat':
                    return lambda x,y: z3.If(x < y,z3.IntVal(0),x-y)
                z3val = table(thing.name)
                if z3val == None:
                    raise iu.IvyError(None,'{} is not a supported Z3 {}'.format(name,kind))
                return z3val
        return None
    if isinstance(z3name,ivy_logic.EnumeratedSort):
        return z3name.to_z3()
    z3val = table(z3name)
    if z3val == None:
        raise iu.IvyError(None,'{} is not a supported Z3 {}'.format(z3name,kind))
    return z3val

def check_native_compat_sym(sym):
    table,kind = (relations,"relation") if sym.is_relation() else (functions,"function") 
    thing = lookup_native(sym,table,kind)
#    print "check_native_compat_sym: {} {}".format(sym,thing)
    try:
        if thing is not None:
#            print "check_native_compat_sym: {} {}".format(sym,thing)
            z3args = []
            for ds in sym.sort.dom:
                z3sort = lookup_native(ds,sorts,"sort")
                if z3sort == None:
                    raise iu.IvyError(None,'domain sort "{}" is uninterpreted'.format(ds))
                z3args.append(z3sort.cast("0"))
            z3val = thing(*z3args)
            z3sort = z3val.sort()
            ns = lookup_native(sym.sort.rng,sorts,"sort")
            if ns == None:
                raise iu.IvyError(None,'range sort "{}" is uninterpreted'.format(sym.sort.rng))
            if ns != z3sort:
                raise iu.IvyError(None,'range sort {}={} does not match {}'.format(sym.sort.rng,ns,z3sort))
    except Exception as e:
        raise iu.IvyError(None,'cannot interpret {} as {}: {}'.format(sym,ivy_logic.sig.interp[sym.name],e))

def check_compat():
    for name,value in ivy_logic.sig.interp.iteritems():
        if name in ivy_logic.sig.symbols:
            sym = ivy_logic.sig.symbols[name]
            sorts = sym.sort.sorts if isinstance(sym.sort,ivy_logic.UnionSort) else [sym.sort]
            for sort in sorts:
                check_native_compat_sym(ivy_logic.Symbol(name,sort))

def sort_card(sort):
    sig = lookup_native(sort,sorts,"sort")
    sig = sig if sig is not None else sort.to_z3()
    if z3.is_bv_sort(sig):
        return 2**sig.size()
    if isinstance(sig,z3.DatatypeSortRef):
        return sig.num_constructors()
    return None


# TODO: this seems wrong: why return a constant?
def native_symbol(sym):
    if isinstance(sym.sort,ConstantSort):
        return z3.Const(sym.rep, name.sort.to_z3())
    return z3.Function(sym.rep, *(name.sort.to_z3()))

def apply_z3_func(pred,tup):
    if isinstance(pred,z3.BoolRef):
        assert not tup
        return pred
    if not isinstance(pred,z3.FuncDeclRef):
        return pred(*tup)
    _args, sz = z3_to_ast_array(tup)
    fact = z3_to_expr_ref(z3.Z3_mk_app(pred.ctx_ref(), pred.ast, sz, _args), pred.ctx)
    return fact

def numeral_to_z3(num):
    # TODO: allow other numeric types
    z3sort = lookup_native(num.sort,sorts,"sort")
    if z3sort == None:
        return z3.Const(num.name+':'+num.sort.name,num.sort.to_z3()) # uninterpreted sort
    try:
        name = num.name[1:-1] if num.name.startswith('"') else num.name
        if isinstance(z3sort,z3.SeqSortRef) and z3sort.is_string():
            return z3.StringVal(name)
        return z3sort.cast(str(int(name,0))) # allow 0x,0b, etc
    except:
        raise iu.IvyError(None,'Cannot cast "{}" to native sort {}'.format(num,z3sort))

# Enumerated sorts can be interpreted as numeric types. However, we have to
# check that the constants actually fit in the type.

def enumerated_to_numeral(term):
    raise iu.IvyError(None,'Cannot interpret enumerated type "{}" as a native sort (not yet supported)'.format(term.sort.name))

def term_to_z3(term):
    if ivy_logic.is_boolean(term):
        return formula_to_z3_int(term)
    if not term.args:
        if isinstance(term,ivy_logic.Variable):
            sorted = hasattr(term,'sort')
            sksym = term.rep + ':' + term.sort.name if sorted else term.rep
            res = z3_constants.get(sksym)
            if res is not None: return res
#            print str(term.sort)
            sig = lookup_native(term.sort,sorts,"sort") if sorted else S
            if sig == None:
                sig = term.sort.to_z3()
#            if sorted:
#                print type(term.sort)
#                print term.sort
#            print type(sksym)
#            print sksym
#            print sig
            res = z3.Const(sksym,sig)
            z3_constants[sksym] = res
            return res
        res = z3_constants.get(str(term.rep))
        if res is None:
#            if isinstance(term.rep,str):
#                print "{} : {}".format(term,term.rep)
            if term.is_numeral():
                res = numeral_to_z3(term.rep)
            elif ivy_logic.is_enumerated(term) and ivy_logic.is_interpreted_sort(term.sort):
                res = enumerated_to_numeral(term)
            else:
                iso = term.rep.sort
                # TODO: this is dangerous
                sig = iso.to_z3() if iso is not None else S
#                print "term: {}, iso : {}, sig = {}".format(term,iso,sig)
                res = z3.Const(solver_name(term.rep),sig)
            z3_constants[term.rep] = res
    elif isinstance(term,ivy_logic.Ite):
        return z3.If(formula_to_z3_int(term.args[0]),term_to_z3(term.args[1]),term_to_z3(term.args[2]))
    else:
        if not hasattr(term,'rep'):
            print term
            print term.lineno
        fun = z3_functions.get(term.rep)
        if fun is None:
            fun = lookup_native(term.rep,functions,"function")
            if fun is None:
                sig = term.rep.sort.to_z3()
                sn = solver_name(term.rep)
                assert solver_name is not None, term.rep
                fun = z3.Function(sn, *sig)
            z3_functions[term.rep] = fun
        args = [term_to_z3(arg) for arg in term.args]
        res = apply_z3_func(fun,args)
    return res

def lt_pred(sort):
    sym = ivy_logic.Symbol('<',sort)
    sig = sym.sort.to_z3()
    return z3.Function(solver_name(sym), *sig)
    
polymacs = {
    '<=' : lambda s,x,y: z3.Or(x == y,lt_pred(s)(x,y)),
    '>' : lambda s,x,y: lt_pred(s)(y,x),
    '>=' : lambda s,x,y: z3.Or(x == y,lt_pred(s)(y,x)),
}

def get_polymacs(op):
    return functools.partial(polymacs[op.name],op.sort)

def atom_to_z3(atom):
    if ivy_logic.is_equals(atom.rep) and ivy_logic.is_enumerated(atom.args[0]) and not use_z3_enums:
        return encode_equality(*atom.args)
    if atom.relname not in z3_predicates:
        rel = lookup_native(atom.relname,relations,"relation")
#        print "atom: {}, rep: {}, rep.sort: {}".format(atom,atom.rep,atom.rep.sort)
        if not rel:
            if atom.rep.name in polymacs and iu.ivy_use_polymorphic_macros:
                rel = get_polymacs(atom.rep)
            else:
                sig = atom.rep.sort.to_z3()
                rel = z3.Function(solver_name(atom.rep), *sig) if isinstance(sig,list) else z3.Const(solver_name(atom.rep),sig)
        z3_predicates[atom.relname] = rel
#    return z3_predicates[atom.relname](
#        *[term_to_z3(t) for t in atom.args])
    pred = z3_predicates[atom.relname]
    tup = [term_to_z3(t) for t in atom.args]
    return apply_z3_func(pred,tup)

def literal_to_z3(lit):
    z3_atom = formula_to_z3_int(lit.atom)
    if lit.polarity == 0:
        return z3.Not(z3_atom)
    else:
        return z3_atom

def quant_constraints(vs):
    natvars = [v for v in vs if ivy_logic.sig.interp.get(v.sort.name,None) == 'nat']
    if len(natvars) == 0:
        return []
    return [ivy_logic.Not(ivy_logic.Symbol('<',ivy_logic.RelationSort([v.sort,v.sort]))(v,ivy_logic.Symbol('0',v.sort)))
            for v in natvars]


# this adds bounds for nat

def forall(vs,z3_vs,z3_body):
    cnstrs = [z3.IntVal(0) <= z3_v for (v,z3_v) in zip(vs,z3_vs) if ivy_logic.sig.interp.get(v.sort.name,None) == 'nat']
    if len(cnstrs) > 0:
        z3_body = z3.Implies(z3.And(*cnstrs),z3_body)
    return z3.ForAll(z3_vs, z3_body)

def exists(vs,z3_vs,z3_body):
    cnstrs = [z3.IntVal(0) <= z3_v for (v,z3_v) in zip(vs,z3_vs) if ivy_logic.sig.interp.get(v.sort.name,None) == 'nat']
    if len(cnstrs) > 0:
        z3_body = z3.And(*(cnstrs + [z3_body]))
    return z3.Exists(z3_vs, z3_body)

def clause_to_z3(clause):
    z3_literals = [literal_to_z3(lit) for lit in clause]
    z3_formula = z3.Or(z3_literals)
    variables = sorted(used_variables_clause(clause))
    if len(variables) == 0:
        return z3_formula
    else:
        z3_variables = [term_to_z3(v) for v in variables]
        return forall(variables, z3_variables, z3_formula)

def conj_to_z3(cl):
    if isinstance(cl,ivy_logic.And):
        return z3.And(*[conj_to_z3(t) for t in cl.args])
    return formula_to_z3_closed(cl)

def type_constraints(syms):
    natsyms = [s for s in syms
               if ivy_logic.sig.interp.get(s.sort.rng.name,None) == 'nat'
                  and not ivy_logic.is_interpreted_symbol(s)]
    res = []
    for sym in natsyms:
        t = (sym if not ivy_logic.is_function_sort(sym.sort) else
             sym(*[ivy_logic.Variable('X'+str(n),s) for n,s in enumerate(sym.sort.dom)]))
        sort = t.sort
        fmla = ivy_logic.Not(ivy_logic.Symbol('<',ivy_logic.RelationSort([t.sort,t.sort]))(t,ivy_logic.Symbol('0',t.sort)))
        z3_fmla = formula_to_z3_closed(fmla)
        res.append(z3_fmla)
    return res
                             

def clauses_to_z3(clauses):
    z3_clauses = [conj_to_z3(cl) for cl in clauses.fmlas]
    z3_clauses.extend([formula_to_z3(dfn) for dfn in clauses.defs])
    z3_clauses.extend(type_constraints(used_symbols_clauses(clauses)))
    res = z3.And(z3_clauses)
    return res

def formula_to_z3_int(fmla):
#    print "formula_to_z3_int: {} : {}".format(fmla,type(fmla))
    if ivy_logic.is_atom(fmla):
        return atom_to_z3(fmla)
    if isinstance(fmla,ivy_logic.Definition) and ivy_logic.is_enumerated(fmla.args[0]) and not use_z3_enums:
        return encode_equality(*fmla.args)
    args = [formula_to_z3_int(arg) for arg in fmla.args]
    if isinstance(fmla,ivy_logic.And):
        return z3.And(args)
    if isinstance(fmla,ivy_logic.Or):
        return z3.Or(args)
    if isinstance(fmla,ivy_logic.Not):
        return z3.Not(args[0])
    if isinstance(fmla,ivy_logic.Definition):
        z3_body = my_eq(args[0],args[1])
        return z3_body
        assert all(ivy_logic.is_variable(v) for v in fmla.args[0].args)
        z3_vs = [term_to_z3(v) for v in fmla.args[0].args]
        return z3.ForAll(z3_vs, z3_body)
    if isinstance(fmla,ivy_logic.Iff):
        return my_eq(args[0],args[1])
    if isinstance(fmla,ivy_logic.Implies):
        return z3.Implies(args[0],args[1])
    if isinstance(fmla,ivy_logic.Ite):
        return z3.If(args[0],args[1],args[2])
    if ivy_logic.is_quantifier(fmla):
        variables = ivy_logic.quantifier_vars(fmla)
        q = forall if ivy_logic.is_forall(fmla) else exists
        res =  q(variables, [term_to_z3(v) for v in variables], args[0])
#        print "res = {}".format(res)
        return res
    if ivy_logic.is_individual(fmla):
        return term_to_z3(fmla)
    print "bad fmla: {!r}".format(fmla)
    assert False

def formula_to_z3_closed(fmla):
    z3_formula = formula_to_z3_int(fmla)
    variables = sorted(used_variables_ast(fmla))
    if len(variables) == 0:
        return z3_formula
    else:
        z3_variables = [term_to_z3(v) for v in variables]
        if isinstance(fmla,ivy_logic.Definition):
            return z3.ForAll(z3_variables, z3_formula)
        return forall(variables, z3_variables, z3_formula)

def formula_to_z3(fmla):
    z3_fmla = formula_to_z3_closed(fmla)
    tcs = type_constraints(used_symbols_ast(fmla))
    if len(tcs) > 0:
        z3_fmla = z3.And(*([z3_fmla] + tcs))
    return z3_fmla
                           


def unsat_core(clauses1, clauses2, implies = None, unlikely=lambda x:False):
#    print "unsat_core clauses1 = {}, clauses2 = {}".format(clauses1,clauses2)
#    assert clauses1.defs == []
    fmlas = clauses1.fmlas
    s2 = z3.Solver()
    alits = [z3.Const("__c%s" % n, z3.BoolSort()) for n,c in enumerate(fmlas)]
    cc = [z3.Or(z3.Not(a),formula_to_z3(c)) for a,c in zip(alits,fmlas)]
    foo = [(a,f) for a,f in zip(alits,fmlas) if unlikely(f)]
    unlikely_lits = [a for a,f in foo]
    for d in clauses1.defs:
        s2.add(formula_to_z3(d.to_constraint()))
    for c in cc:
        s2.add(c)
    s2.add(clauses_to_z3(clauses2))
    if implies is not None:
        s2.add(not_clauses_to_z3(implies))
    is_sat = s2.check(alits)
    if is_sat == z3.sat:
#        print "unsat_core model = {}".format(get_model(s2))
        return None
    if unlikely_lits:
        core = biased_core(s2,alits,unlikely_lits)
    else:
        core = minimize_core(s2)
    core_ids = [get_id(a) for a in core]
    res = [c for a,c in zip(alits,fmlas) if get_id(a) in core_ids]
#    print "unsat_core res = {}".format(res)
    return Clauses(res,list(clauses1.defs))


def cube_to_z3(cube):
    if len(cube) == 0:
        return z3.BoolVal(True)
    fmla = z3.And([literal_to_z3(lit) for lit in cube])
    return fmla

def get_id(x):
    return z3.Z3_get_ast_id(x.ctx_ref(), x.as_ast())

def check_cube(s,cube,memo = None,memo_unsat_only = False):
    s.push()
    f = cube_to_z3(cube)
##    print f
    fid = get_id(f)
    if memo is not None and fid in memo :
##        print "memo %s" % memo[fid][1]
        res = memo[fid][1]
        if (not res) or (not memo_unsat_only):
            return memo[fid][1]
    s.add(f)
#    f = open("ivy.smt2","w")
#    f.write(s.to_smt2())
#    f.close()
    cr = s.check()
    s.pop()
    res = cr != z3.unsat
    if memo is not None:
        memo[fid] = (f,res) # keep reference to f to preserve id
##    print "res %s" % res
    return res

def new_solver():
    return z3.Solver()

def solver_add(solver,fmla):
    solver.add(formula_to_z3(fmla))

def is_sat(s):
    return s.check() != z3.unsat

def add_clauses(s,clauses):
    foo = clauses_to_z3(clauses)
#    print "foo = {}".format(foo)
    s.add(foo)

def get_model(s):
    return s.model()

def terms_match(tl1,tl2):
    if len(tl1) != len(tl2):
        return False
    env = dict()
    for x,y in zip(tl1,tl2):
        if isinstance(x,ivy_logic.Variable):
            if x.rep in env:
                if y.rep != env[x.rep]:
                    return False
            env[x.rep] = y.rep
        else:
            if x.rep != y.rep:
                return False
    return True

def get_arg_range(m,x):
    decl = x.decl()
    v = m[decl].as_list()
    range = [y[-1] for y in v[0:-1]] + [v[-1]]
    return range

import itertools

class SortOrder(object):
    def __init__(self,vs,order,model):
        self.vs = vs
        self.order = order
        self.model = model
    def __call__(self,x,y):
        interp = zip(self.vs,(x,y))
        fact = substitute(self.order,*interp)
        fact_val = self.model.eval(fact)
#        print "order: %s = %s" % (fact,fact_val)
        return -1 if z3.is_true(fact_val) else 1   

def collect_numerals(z3term):
    if z3.is_int_value(z3term) or z3.is_bv_value(z3term):
        yield z3term
    elif z3.is_app_of(z3term,z3.Z3_OP_ITE):
        for z in collect_numerals(z3term.arg(1)):
            yield z
        for z in collect_numerals(z3term.arg(2)):
            yield z

def from_z3_numeral(z3term,sort):
    name = str(z3term)
    if not(name[0].isdigit() or name[0] == '"' or name[0] == '-'):
        print "unexpected numeral from Z3 model: {}".format(name)
    return ivy_logic.Symbol(name,sort)

def collect_model_values(sort,model,sym):
    term = sym(*sym_placeholders(sym))
    val = model.eval(term_to_z3(term),model_completion=True)
    nums = set(from_z3_numeral(n,sort) for n in collect_numerals(val))
    return nums

def mine_interpreted_constants(model,vocab):
    sorts = ivy_logic.interpreted_sorts()
    sort_values = dict((sort,set()) for sort in sorts)
    for s in vocab:
        sort = s.sort.rng
        if sort in sort_values:
            sort_values[sort].update(collect_model_values(sort,model,s))
    return dict((x,map(term_to_z3,list(y))) for x,y in sort_values.iteritems())
    
def enumerated_range(sort):
    res = [z3_constants[x] for x in sort.defines()]
    return res

class HerbrandModel(object):
    def __init__(self,solver,model,vocab):
        self.solver, self.model = solver, model
        self.constants = dict((sort_from_z3(s),model.get_universe(s))
                              for s in model.sorts())
        self.constants.update(mine_interpreted_constants(model,vocab))
#        print "model: %s" % model
#        print "univ: %s" % self.constants

    def sorts(self):
        return [s for s in self.constants]

    def sort_universe(self,sort):
        return [constant_from_z3(sort,c) for c in self.constants[sort]]

    def sorted_sort_universe(self,sort):
        elems = self.constants[sort]
#        print "elems: {}".format(map(str,elems))
        vs = [ivy_logic.Variable(s,sort) for s in ["X","Y"]]
        order = ivy_logic.Symbol("<",ivy_logic.RelationSort([sort,sort]))
        order_atom = atom_to_z3(order(*vs))
        z3_vs = map(term_to_z3,vs)
#        print "order_atom: {}".format(order_atom)
        try:
            fun = z3.Function
            self.model[order.to_z3()]
#            print "sorting..."
            elems = sorted(elems,SortOrder(z3_vs,order_atom,self.model))
        except IndexError:
            pass
#        print "elems: {}".format(map(str,elems))
        return [constant_from_z3(sort,elem) for elem in elems]

    def universes(self, numerals=False):
#        print "sorts: {!r}".format(self.sorts())
        if numerals:
            return dict((s,[c.rename(lambda s:str(i)) for i,c in enumerate(self.sorted_sort_universe(s))]
                           if not ivy_logic.is_interpreted_sort(s) else list(self.sort_universe(s)))
                        for s in self.sorts())
        return dict((s,[c.skolem() for c in self.sort_universe(s)]) for s in self.sorts())

    def check(self,fmla):
        """ Return the set of satisfying assignments to the free variables in fmla. Returns
            a table in the format (vars,rows), where each row is a tuple of values of the
            variables in vars.
        """
        vs = list(variables_ast(fmla))
        s = self.solver
        m = self.model
        ranges = [enumerated_range(x.sort) if isinstance(x.sort,ivy_logic.EnumeratedSort) else
                  self.constants[x.sort] for x in vs]
        z3_fmla = literal_to_z3(fmla)
#        print "z3_fmla = {}".format(z3_fmla)
        z3_vs = [term_to_z3(v) for v in vs]
        insts = []
        for tup in itertools.product(*ranges):
            interp = zip(z3_vs,tup)
            fact = substitute(z3_fmla,*interp)
            fact_val = m.eval(fact,model_completion=True)
#            print "%s = %s" % (fact,fact_val)
            if z3.is_true(fact_val):
                args = [constant_from_z3(v.sort,y) for v,y in zip(vs,tup)]
                insts.append(args)
        return (vs,insts)

    def eval(self,fmla):
        """ Evaluate a formula in the model. Variables are interpreted universally. """
        vs,tups = self.check(ivy_logic.Literal(0,fmla))
        return not tups

    def eval_constant(self,c):
        return get_model_constant(self.model,c)

    def eval_to_constant(self,t):
        return constant_from_z3(t.sort,self.model.eval(term_to_z3(t),model_completion=True))

    def __str__(self):
        return self.model.sexpr()
    
# TODO: need to map Z3 sorts back to ivy sorts
def sort_from_z3(s):
    return z3_sorts_inv[get_id(s)]

def constant_from_z3(sort,c):
    if z3.is_true(c):
        return ivy_logic.And()
    if z3.is_false(c):
        return ivy_logic.Or()
    return ivy_logic.Constant(ivy_logic.Symbol(repr(c),sort))

def get_model_constant(m,t):
    s = t.get_sort()
    if isinstance(s,ivy_logic.EnumeratedSort) and not use_z3_enums:
        for v in s.defines():
            w = ivy_logic.Constant(ivy_logic.Symbol(v,s))
            if z3.is_true(m.eval(encode_equality(t,w))):
                return w
#        print "model: {}".format(m.sexpr())
#        print "term: {}".format(t)
        res = ivy_logic.Constant(ivy_logic.Symbol(s.defines()[0],s))
        print "warning: model doesn't give a value for enumerated term {}. returning {}.".format(t,res)
        return res
#        assert False # model doesn't give a value for enumerated term
    return constant_from_z3(s,m.eval(term_to_z3(t),model_completion=True))



def clauses_imply(clauses1, clauses2):
    """True if clauses1 imply clauses2.
    """
    s = z3.Solver()
    z1 = clauses_to_z3(clauses1)
#    print "z1 = {}".format(z1)
    s.add(z1)
    z2 = not_clauses_to_z3(clauses2)
#    print "z2 = {}".format(z2)
    s.add(z2)
    return s.check() == z3.unsat

def clauses_imply_list(clauses1, clauses2_list):
    """True if clauses1 imply clauses2.
    """
    s = z3.Solver()
    z1 = clauses_to_z3(clauses1)
#    print "assume {}".format(clauses1)
#    print "z1 = {}".format(z1)
    s.add(z1)

    res = []
    negs = map(dual_clauses,clauses2_list)
        
    for clauses2 in negs:
        z2 = clauses_to_z3(clauses2)
#        print "check {}".format(clauses2)
#        print "z2 = {}".format(z2)
        s.push()
        s.add(z2)
        res.append(s.check() == z3.unsat)
        s.pop()
    return res

class AssumeAssert(object):
    def __init__(self,clauses,doc=None):
        self.clauses = clauses
        self.doc = doc

class Assume(AssumeAssert):
    pass

class Assert(AssumeAssert):
    pass

def check_sequence(assume_assert_list,reporter):
    """True if clauses1 imply clauses2.
    """
    s = z3.Solver()

    res = []

    for aa in assume_assert_list:
        if isinstance(aa,Assume):
#            print "assume {}".format(aa.clauses)
            if reporter is not None:
                reporter.start(False,aa.doc)
            z1 = clauses_to_z3(aa.clauses)
            s.add(z1)
            res.append(True)
        else:
#            print "assert {}".format(aa.clauses)
            if reporter is not None:
                reporter.start(True,aa.doc)
            clauses2 = dual_clauses(aa.clauses)
            z2 = clauses_to_z3(clauses2)
            s.push()
            s.add(z2)
            res.append(s.check() == z3.unsat)
            if reporter is not None:
                if not reporter.end(s.check() == z3.unsat,aa.doc):
                    return res
            s.pop()
    return res


def not_clauses_to_z3(clauses):
    # Separate the definition of skolems
    sdefs,defs = [],[]
    for dfn in clauses.defs:
        (sdefs if dfn.defines().is_skolem() else defs).append(dfn)
    dcls = Clauses([],sdefs)
    cls = Clauses(clauses.fmlas,defs)
#    print "not_clauses_to_z3: dcls: {} cls: {}".format(dcls,cls)
    return z3.And(clauses_to_z3(dcls),z3.Not(clauses_to_z3(clauses)))

def clauses_sat(clauses1):
    """True if clauses1 imply clauses2.
    """
    s = z3.Solver()
    s.add(clauses_to_z3(clauses1))
    return s.check() != z3.unsat


def remove_duplicates_clauses(clauses):
    # tricky: store all z3 fmlas in list so not GC'd until all id's computed!
    z3fs = [(c,formula_to_z3(c)) for c in clauses.fmlas]
    return Clauses(list(iu.unique2((x,get_id(y)) for x,y in z3fs)),clauses.defs)

def clauses_case(clauses1):
    """ Drop literals in a clause set while maintaining satisfiability.
    This only works for quantifier-free clauses. """
    s = z3.Solver()
    s.add(clauses_to_z3(clauses1))
    if s.check() == z3.unsat:
        return [[]]
    m = get_model(s)
#    print "clauses_case: after SAT check"
##    print "clauses1: {}".format(clauses1)
    clauses = Clauses([clause_model_simp(m,c) for c in clauses1.clauses])
    clauses = remove_duplicates_clauses(clauses)
    while True:
#        print "clause_case: starting iteration"
#        print "clauses: {}".format(clauses)
        num_old_clauses = len(clauses.clauses)
        r = ur.UnitRes(clauses.clauses)
        with r.context():
            r.propagate()
#        print "clause_case: after propagation"
        new_clauses = Clauses([[l] for l in r.unit_queue] + r.clauses)
#        print "new_clauses: {}".format(new_clauses)
        clauses = Clauses([clause_model_simp(m,c) for c in new_clauses.clauses])
#        print "clause_case: after model-based simplification"
        clauses = remove_duplicates_clauses(clauses)
#        print "clause_case: after duplicate removal"
        if len(clauses.clauses) <= num_old_clauses:
            return clauses



def clause_model_simp(m,c):
    """ Simplify a clause by dropping literals while maintaining its truth in a model. """
    res = []
    for l in c:
        if not is_ground_lit(l):
            res.append(l)
            continue
#        if isinstance(l.atom,ivy_logic.And):
#            print "clause_model_simp: {}".format(c)
        v = m.eval(literal_to_z3(l))
        if z3.is_true(v):
            return [l]
        if not z3.is_false(v):
            res.append(l)
    return res

def get_model_clauses(clauses1):
    s = z3.Solver()
    z3c = clauses_to_z3(clauses1)
    s.add(z3c)
    res = s.check()
    if res == z3.unsat:
        return None
    m = get_model(s)
    return HerbrandModel(s,m,used_symbols_clauses(clauses1))

def sort_size_constraint(sort,size):
    if isinstance(sort,ivy_logic.UninterpretedSort):
        syms = [ivy_logic.Symbol('__'+sort.name+'$'+str(i),sort) for i in range(size)]
        v = ivy_logic.Variable('X'+sort.name,sort)
        res =  ivy_logic.Or(*[ivy_logic.Equals(v,s) for s in syms])
#        print "sort_size_constraint : {}".format(res)
        return res
    return ivy_logic.And()


def relation_size_constraint(relation, size):
    assert type(relation) is lg.Const
    assert type(relation.sort) is lg.FunctionSort

    consts = [
        [
            lg.Const('__${}${}${}'.format(relation.name, i, j), s)
            for j, s in enumerate(relation.sort.domain)
        ]
        for i in range(size)
    ]

    vs = [
        lg.Var('X${}${}'.format(relation.name, j), s)
        for j, s in enumerate(relation.sort.domain)
    ]
    result = lg.Or(lg.Not(relation(*vs)), *(
        lg.And(*(
            lg.Eq(c, v) for c, v in  zip(cs,vs)
        ))
        for cs in consts
    ))
#    print "relation_size_constraint: {}".format(result)
    return result


def size_constraint(x, size):
    if type(x) is lg.UninterpretedSort:
        return sort_size_constraint(x, size)

    elif type(x) is lg.Const and type(x.sort) is lg.FunctionSort:
        return relation_size_constraint(x, size)

    else:
        return lg.And()


def model_if_none(clauses1,implied,model):
    h = model
    if h == None:
        s = z3.Solver()
        z3c = clauses_to_z3(clauses1)
        s.add(z3c)
        if implied is not None:
            s.add(not_clauses_to_z3(implied))
        sort_size = 1
        while True:
            s.push()
            for sort in ivy_logic.uninterpreted_sorts():
                s.add(formula_to_z3(sort_size_constraint(sort,sort_size)))
            if s.check() != z3.unsat:
                m = get_model(s)
                print "model = {}, size = {}".format(m,sort_size)
##        print "clauses1 = {}".format(clauses1)
##        print "z3c = {}".format(str(z3c))
                syms = used_symbols_clauses(clauses1)
                if implied is not None:
                    syms.update(used_symbols_clauses(implied))
                h = HerbrandModel(s,m,syms)
                s.pop()
                return h
            sort_size += 1
            s.pop()
    return h


def decide(s,atoms=None):
#    print "solving{"
#    f = open("ivy.smt2","w")
#    f.write(s.to_smt2())
#    f.close()
    res = s.check() if atoms == None else s.check(atoms)
    if res == z3.unknown:
        print s.to_smt2()
        raise iu.IvyError(None,"Solver produced inconclusive result")
#    print "}"
    return res

def get_small_model(clauses, sorts_to_minimize, relations_to_minimize, final_cond=None, shrink=True):
    """
    Return a HerbrandModel with a "small" model of clauses.

    sorts_to_minimize is a list of sorts, and relations_to_minimize is
    a list of relations,

    The model minimization occurs in 2 ways:

    First, minimize universe size lexicographically according to the order of
    sorts_to_minimize.

    Second, minimize the number of positive entries in the relations
    according to the order of relations_to_minimize.

    The parameter final_cond can be a list of objects have the following interface:

        cond():  returns a final condition as a clauses object
        start(): called before starting
        sat(): called if sat, return True if should ignore result
        unsat() : called if unsat
        assume() : if returns true, assume rather than check

    """

    if opt_show_vcs.get():
        print ''
        print "definitions:"
        for df in clauses.defs:
            print df
            print
        print "axioms:"
        for fmla in clauses.fmlas:
            print fmla
            print

    s = z3.Solver()
    the_fmla = clauses_to_z3(clauses)
#    iu.dbg('the_fmla')
    s.add(the_fmla)
    
    # res = decide(s)
    # if res == z3.unsat:
    #     return None

    assumes = []
    if final_cond is not None:
        if isinstance(final_cond,list):
            res = z3.unsat
            for fc in final_cond:
                if not opt_incremental.get():
                    s = z3.Solver()
                    s.add(clauses_to_z3(clauses))
                    for fmla in assumes:
                        s.add(clauses_to_z3(fmla))
                fc.start()
                if fc.assume():
                    if opt_show_vcs.get():
                        print '\nassume: {}'.format(fc.cond())
                    s.add(clauses_to_z3(fc.cond()))
                    assumes.append(fc.cond())
                else:
                    if opt_incremental.get():
                        s.push()
                    foo = fc.cond()
                    if opt_show_vcs.get():
                        print '\nassert: {}'.format(foo)
                    the_fmla = clauses_to_z3(foo)
#                    iu.dbg('the_fmla')
                    s.add(the_fmla)
                    res = decide(s)
                    if res != z3.unsat:
                        if fc.sat():
                            res = z3.unsat
                        else:
                            break
                    else:
                        fc.unsat()
                    if opt_incremental.get():
                        s.pop()
        else:
            s.add(clauses_to_z3(final_cond))
            res = decide(s)
    else:
        res = decide(s)
    if res == z3.unsat:
        return None

    if shrink:
        print "searching for a small model...",
        sys.stdout.flush()
        for x in chain(sorts_to_minimize, relations_to_minimize):
            for n in itertools.count(1):
                s.push()
                sc = size_constraint(x, n)
                s.add(formula_to_z3(sc))
                res = decide(s)
                if res == z3.sat:
                    break
                else:
                    s.pop()
        print "done"
    m = get_model(s)
#    print "model = {}".format(m)
#    f = open("ivy.smt2","w")
#    f.write(s.to_smt2())
#    f.close()
    h = HerbrandModel(s,m,used_symbols_clauses(clauses))
    return h


def model_universe_facts(h,sort,upclose):
    if ivy_logic.is_interpreted_sort(sort):
        return []
    # get universe elements
    elems = h.sort_universe(sort)
    # constraint defining universe
    uc = []
    if not upclose:
        uc = [[ivy_logic._eq_lit(ivy_logic.Variable('X',c.sort),c) for c in elems]]
    # universe elements are distinct
    dc = [[ivy_logic._neq_lit(c1,c2)]
          for (c1,c2) in iu.distinct_unordered_pairs(elems)]
    return uc+dc


def model_facts(h,ignore,clauses1,upclose=False):
    # define the universe for each sort:
    uc = [fact for s in h.sorts() for fact in model_universe_facts(h,s,upclose)]
    # values of constants in formula
    temp = [[(ivy_logic.Constant(c),
                             get_model_constant(h.model,ivy_logic.Constant(c)))]
          for c in used_constants_clauses(clauses1)
          if not ignore(c) and c not in ivy_logic.sig.constructors]
#    print "temp = {}".format(temp)
    vc = [[ivy_logic._eq_lit(ivy_logic.Constant(c),
                             get_model_constant(h.model,ivy_logic.Constant(c)))]
          for c in used_constants_clauses(clauses1)
          if not ignore(c) and c not in ivy_logic.sig.constructors]
#    print "model_facts vc = {}".format(vc)
    # values of relations in formula
#    print "used_relations_clauses = {}".format(used_relations_clauses(clauses1))
    urc = dict((ivy_logic.normalize_symbol(r),n) for r,n in used_relations_clauses(clauses1).iteritems())
    vr = [[l]
          for (r,n) in urc.iteritems()
          if not ignore(r)
          for l in relation_model_to_clauses(h,r,n)]
    # values of functions in formula
    fns = set(f for (f,arity) in functions_clauses(clauses1) if not ignore(f) and arity >= 1)
    vf = [[l] for f in fns for l in function_model_to_clauses(h,f)]
    res = uc + vc + vr + vf
    return Clauses(res)

#def numeral_assign(h):
#    return m = dict((c.rep,ivy_logic.Constant(c.rep.rename(lambda s:str(i))))
#             for s in h.sorts() for i,c in enumerate(h.sorted_sort_universe(s)))

def numeral_assign(clauses,h):
    num_by_sort = defaultdict(list)
    numerals = [c for c in used_constants_clauses(clauses) if c.is_numeral()]
    for num in numerals:
        num_by_sort[num.sort].append(num)
#    print "num_by_sort: {}".format(numerals)
    foom = dict()
    used = set()
#    print "starting: foom = {}".format(foom)
    for s in h.sorts():
#        print "na sort: {}".format(repr(s))
        if ivy_logic.is_interpreted_sort(s):
            continue
#        print "sort loop: sort = {}, foom = {}".format(s,foom)
        for num in num_by_sort[s]:
#            print "foom = {}".format(foom)
            numv = h.eval_constant(num)
#            print "eval: {}:{} = {}".format(num,num.sort,numv)
            if numv in foom:
                print "two numerals assigned same value!: {} = {}".format(num,foom[numv])
            else:
#                print "assigning {} to {}".format(num,numv)
                foom[numv] = num
            used.add(num)
        i = 0
        for c in h.sorted_sort_universe(s):
            if c not in foom:
                while True:
                    num = ivy_logic.Constant(c.rep.rename(lambda s:str(i)))
                    i = i + 1
                    if num not in used:
                        foom[c.rep] = num
                        break
    return foom

def clauses_model_to_clauses(clauses1,ignore = None, implied = None,model = None, numerals=False):
    """ Return a model of clauses1 or None. Model is represented by a
    clause set that uniquely characterizes it. The function "ignore", if
    provided, returns true for symbols that should be ignored in the
    model (tyipically skolems).
    """
##    print "clauses_model_to_clauses clauses1 = {}".format(clauses1)
    h = model_if_none(clauses1,implied,model)
    ignore = ignore if ignore is not None else lambda x: False
    res = model_facts(h,ignore,clauses1)
#    print "core after mode_facts: {} ".format(unsat_core(res,true_clauses()))
    # if using numerals, replace the universe elements with them
    if numerals:
        m = numeral_assign(res,h)
#        print "dict: {}".format([(str(x),str(y)) for x,y in m.iteritems()])
    # else, existentially quantify the names of the universe elements
    else:
        m = dict((c.rep,ivy_logic.Constant(c.rep.prefix('__')))
                 for s in h.sorts() for c in h.sort_universe(s))
    res = substitute_constants_clauses(res,m)
#    print "core after rename: {} ".format(unsat_core(res,true_clauses()))
#    print "clauses_model_to_clauses res = {}".format(res)
    return res

def bound_quantifiers_clauses(h,clauses,reps):
   """ Bound the universal quantifiers in "clauses" to just the terms in
       Herbrand model h. This applies only to quantifiers in the constraints of
       "clauses" and not to the definitions. The map reps gives representatives
       for the terms in the Herbrand universe."""

   def bdv(v):
       """ Return a formula bounding a variable of ubninterpreted sort """
       eqs = [ivy_logic.Equals(v,reps[c.rep]) for c in h.sort_universe(v.sort)]
       return ivy_logic.Or(*eqs)

   def bq(fmla):
       """ Bound the free variables in fmla of uninterpeted sort """
       vs = list(sorted(used_variables_ast(fmla)))
       vs = [v for v in vs if not ivy_logic.is_interpreted_sort(v.sort)]
       cnsts = [bdv(v) for v in vs]
       bq_res = ivy_logic.Implies(ivy_logic.And(*cnsts),fmla) if cnsts else fmla
       return bq_res

   new_fmlas = map(bq,clauses.fmlas)
   return Clauses(fmlas=new_fmlas,defs=list(clauses.defs))

def filter_redundant_facts(clauses,axioms):
    """ Filter out redundant constraints from "clauses", given the
    "axioms".  Currently, this removes only negative formulas that are
    implied by the positive formulas, so it should work well for facts
    about total orders, for example. """
    
    fmlas = clauses.fmlas
    pos_fmlas = [fmla for fmla in fmlas if not isinstance(fmla,ivy_logic.Not)]
    neg_fmlas = [fmla for fmla in fmlas if isinstance(fmla,ivy_logic.Not)]
    s2 = z3.Solver()
    alits = [z3.Const("__c%s" % n, z3.BoolSort()) for n,c in enumerate(neg_fmlas)]
    cc = [z3.Or(z3.Not(a),z3.Not(formula_to_z3(c))) for a,c in zip(alits,neg_fmlas)]
    s2.add(clauses_to_z3(axioms))
    for d in clauses.defs:
        s2.add(formula_to_z3(d.to_constraint()))
    for fmla in pos_fmlas:
        s2.add(formula_to_z3(fmla))
    for c in cc:
        s2.add(c)
    keep = []
    for fmla,alit in zip(neg_fmlas,alits):
        if decide(s2,[alit]) == z3.sat:
            keep.append(fmla)
#    print "unsat_core res = {}".format(res)
    return Clauses(pos_fmlas+keep,list(clauses.defs))




def clauses_model_to_diagram(clauses1,ignore = None, implied = None,model = None,axioms=None,weaken=True,numerals=True):
    """ Return a diagram of a model of clauses1 or None.  The function "ignore", if
    provided, returns true for symbols that should be ignored in the
    diagram.
    """
#    print "clauses_model_to_diagram clauses1 = {}".format(clauses1)
    if axioms == None:
        axioms = true_clauses()
#    print "model = {}".format(model)
    h = model_if_none(and_clauses(clauses1,axioms),implied,model)
    ignore = ignore if ignore is not None else lambda x: False
    res = model_facts(h,(lambda x: False),clauses1,upclose=True) # why not pass axioms?
#    print "clauses_model_to_diagram res = {}".format(res)
    # find representative elements
    # find representatives of universe elements
    if numerals:
        reps = numeral_assign(res,h)
    else:
        reps = dict()
        for c in used_constants_clauses(clauses1):
    #        print "constant: {}".format(c)
            mc = get_model_constant(h.model,ivy_logic.Constant(c))
    #        print "value: {}".format(mc)
            if mc.rep not in reps or reps[mc.rep].rep.is_skolem() and not c.is_skolem():
                reps[mc.rep] = ivy_logic.Constant(c)
        for s in h.sorts():
            for e in h.sort_universe(s):
                if e.rep not in reps:
                    reps[e.rep] = e.rep.skolem()()
#    print "clauses_model_to_diagram reps = {}".format(reps)
    # filter out clauses using universe elements without reps
#    res = [cls for cls in res if all(c in reps for c in used_constants_clause(cls))]
    # replace universe elements with their reps
#    print "clauses_model_to_diagram res = {}".format(res)
    res = substitute_constants_clauses(res,reps)
    # filter defined skolems
   # this caused a bug in the leader example. the generated diagram did not satisfy clauses1
    res.fmlas = [f for f in res.fmlas if not any((x.is_skolem() and x in clauses1.defidx) for x in used_symbols_ast(f))]
#    print "clauses_model_to_diagram res = {}".format(res)
    uc = Clauses([[ivy_logic._eq_lit(ivy_logic.Variable('X',c.get_sort()),reps[c.rep])
                   for c in h.sort_universe(s)] for s in h.sorts()])
#    print "clauses_model_to_diagram uc = {}".format(uc)

    res = filter_redundant_facts(res,axioms)

    uc = true_clauses()
#    print "weaken: {}".format(weaken)
    if weaken:
        def unlikely(fmla):
            # remove if possible the =constant predicates
            return ivy_logic.is_eq(fmla) and ivy_logic.is_constant(fmla.args[0])
        clauses1_weak = bound_quantifiers_clauses(h,clauses1,reps)
        res = unsat_core(res,and_clauses(uc,axioms),clauses1_weak,unlikely=unlikely) # implied not used here
#    print "clauses_model_to_diagram res = {}".format(res)

#    print "foo = {}".format(unsat_core(and_clauses(uc,axioms),true_clauses(),clauses1))

    # filter out non-rep skolems
    repset = set(c.rep for e,c in reps.iteritems())
#    print "clauses_model_to_diagram repset = {}".format(repset)
    ign = lambda x,ignore=ignore: (ignore(x) and not x in repset)
    res = Clauses([cl for cl in res.fmlas if not any(ign(c) for c in used_symbols_ast(cl))])
#    print "clauses_model_to_diagram res = {}".format(res)
    return res

def relation_model_to_clauses(h,r,n):
    lit = ivy_logic.Literal(1,rel_inst(r))
    res = []
    get_lit_facts(h,lit,res)
    get_lit_facts(h,~lit,res)
    return res
#    pos = h.ground_instances(lit)
#    neg = h.ground_instances(~lit)
#    return pos + neg;

def get_lit_facts(h,lit,res):
    vs,rows = h.check(lit)
##    print "rows = {}".format(rows)
    for r in rows:
##        print "r = {}".format(r)
        subst = dict(zip([v.rep for v in vs],r))
##        print "subst = {}".format(subst)
        res += [substitute_lit(lit,subst)]

def function_model_to_clauses(h,f):
    sort = f.sort
    rng = sort.rng
    res = []
    fterm = fun_inst(f)
    if isinstance(rng,ivy_logic.EnumeratedSort) and not use_z3_enums:
        for c in rng.defines():
            eq = ivy_logic._eq_lit(fterm,ivy_logic.Constant(ivy_logic.Symbol(c,rng)))
#            print "function_model_to_clauses: {}".format(eq)
            get_lit_facts(h,eq,res) 
    # non-enumerated function types
    else:
        lit = ivy_logic.Literal(1,fun_eq_inst(f))
        get_lit_facts(h,lit,res)
#        print "fun facts: {}".format([str(r) for r in res])
    return res

def clauses_imply_formula(clauses1, fmla2):
    """True if clauses1 imply clauses2.
    """
    s = z3.Solver()
    s.add(clauses_to_z3(clauses1))
    s.add(formula_to_z3(ivy_logic.Not(fmla2)))
#    print s.to_smt2()
    return s.check() == z3.unsat

def ceillog2(n):
    bits,vals = 0,1
    while vals < n:
        bits += 1
        vals *= 2
    return bits

def gebin(bits,n):
    if n == 0:
        return z3.BoolVal(True)
    if n >= 2**len(bits):
        return z3.BoolVal(False)
    hval = 2**(len(bits)-1)
    if hval <= n:
        return z3.And(bits[0],gebin(bits[1:],n-hval))
    return z3.Or(bits[0],gebin(bits[1:],n))

def binenc(m,n):
    return [(z3.BoolVal(True) if m & (1 << (n-1-i)) else z3.BoolVal(False))
            for i in range(n)]

def z3_function(name,sig):
    return z3.Function(name, *sig) if isinstance(sig,list) else z3.Const(name,sig)

def encode_term(t,n,sort):
    if isinstance(t,ivy_logic.Ite):
        cond = formula_to_z3_int(t.args[0])
        thenterm = encode_term(t.args[1],n,sort)
        elseterm = encode_term(t.args[2],n,sort)
        return [z3.If(cond,x,y) for x,y in zip(thenterm,elseterm)]
    if t.rep in ivy_logic.sig.constructors:
        try:
            m = sort.defines().index(t.rep.name)
        except ValueError:
            print "{} : {} : {}".format(sort,sort.defines(),t.rep)
            exit(1)
        return binenc(m,n)
    elif isinstance(t,ivy_logic.Variable):
            sksym = t.rep + ':' + t.sort.name
            res = [z3.Const(sksym + ':' + str(n-1-i),z3.BoolSort()) for i in range(n)]
            iu.dbg('res')
            return res
    else:
#        return [atom_to_z3(ivy_logic.Atom(t.rep + ':' + str(n-1-i),t.args))
#                for i in range(n)]
        args = [term_to_z3(arg) for arg in t.args]
        print "encode_term t={}".format(t)
        sig = ivy_logic.RelationSort(t.rep.sort.dom).to_z3()

        res = [apply_z3_func(z3_function(t.rep.name + ':' + str(n-1-i),sig),args)
               for i in range(n)]
        print "encode_term res={}".format(res)
        return res

def encode_equality(*terms):
    sort = terms[0].sort
    n = len(sort.defines())
    bits = ceillog2(n)
    eterms = [encode_term(t,bits,sort) for t in terms]
    eqs = z3.And([x == y for x,y in zip(*eterms)])
    alt = z3.And([gebin(e,n-1) for e in eterms])
    res =  z3.Or(eqs,alt)
#    print "encode_equality terms={},{}".format(terms[0],terms[1])
#    print "encode_equality res={}".format(res)
    return res

# this is just a stripped-down version of the one in z3.py

def substitute(t, *m):
    """Apply substitution m on t, m is a list of pairs of the form (from, to). Every occurrence in t of from is replaced with to. """
    num = len(m)
    _from = (z3.Ast * num)()
    _to   = (z3.Ast * num)()
    for i in range(num):
        _from[i] = m[i][0].as_ast()
        _to[i]   = m[i][1].as_ast()
    return z3_to_expr_ref(z3.Z3_substitute(t.ctx.ref(), t.as_ast(), num, _from, _to), t.ctx)


if __name__ == '__main__':
    # clauses = ivy_logic.to_clauses("[[~n(V,_y)],[~n(V1,V),~n(V2,V),=(V1,V2)]]")
#    # print clauses
    # print
    # z3_formula = clauses_to_z3(clauses)
    # print z3_formula
    # print
    # print

    # f = clauses_to_z3(ivy_logic.to_clauses("[[p()],[~p()]]"))
    # s = z3.Solver()
    # s.add(f)
    # print s.check() # should be unsat

    # f1 = clauses_to_z3(ivy_logic.to_clauses("[[p()]]"))
    # f2 = clauses_to_z3(ivy_logic.to_clauses("[[~p()]]"))
    # s = z3.Solver()
    # s.add(f1)
    # s.add(f2)
    # print s.check() # this is also unsat

    # ivy_logic.add_symbol('p',ivy_logic.RelationSort([ivy_logic.universe]))
    # cls = to_clauses("p(x) & ~p(y)")
    # print clauses_model_to_clauses(cls)

    s = ivy_logic.EnumeratedSort(["a","b","c"])
    for c in s.defines():
        t = add_symbol(c,s)
        ivy_logic.sig.constructors.add(t)
    add_symbol('f',ivy_logic.FunctionSort([ivy_logic.universe],s))
    cls = to_clauses("f(x) = a & f(y) = b")
    print clauses_model_to_clauses(cls)

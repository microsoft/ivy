#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_art import *
import pickle
from ivy_interp import Interp, eval_state_facts
from functools import partial
from ivy_concept_space import *
from ivy_parser import parse,ConstantDecl,ActionDef,Ivy,inst_mod
from ivy_actions import DerivedUpdate, type_check_action, type_check, SymbolList, UpdatePattern, ActionContext, LocalAction, AssignAction, CallAction, Sequence, IfAction, WhileAction, AssertAction, AssumeAction, NativeAction, ChoiceAction, has_code
from ivy_utils import IvyError
import ivy_logic
import ivy_dafny_compiler as dc
import ivy_solver as slv
import ivy_logic_utils as lu
import string
import ivy_ast
import ivy_utils as iu
import ivy_actions as ia
import ivy_alpha
import ivy_module as im
import ivy_theory as ith
import ivy_isolate as iso
import ivy_printer
import ivy_proof as ip
from collections import defaultdict
from tarjan import tarjan

class IvyDeclInterp(object):
    def __call__(self,ivy):
        for decl in ivy.decls:
            with ASTContext(decl):
                n = decl.name()
#                print "decl: {} : {}".format(n,decl.lineno if hasattr(decl,'lineno') else None)
                if n == 'assert': n = '_assert' # reserved in python!
                if hasattr(self,n):
                    for x in decl.args:
                        getattr(self,n)(x)

from ivy_ast import ASTContext

# ast compilation


ivy_ast.Variable.get_sort = lambda self: ivy_logic.find_sort(resolve_alias(self.sort.rep))

def thing(self):
    with ASTContext(self):
        return self.cmpl()

# "roots" are AST objects that bind variables, such as assignment, assume, etc. 
# some roots have symbols as args instead of terms (e.g., field assign)
def compile_root_args(self):
    return [(find_symbol(a) if isinstance(a,str) else a.compile()) for a in self.args]

def other_thing(self):
    # we have to do sort inference on roots
    if hasattr(self,'sort_infer_root'):
        with top_sort_as_default():
            res = self.clone(compile_root_args(self))
        return sort_infer(res)
    else:
        return self.clone([a.compile() for a in self.args])

ivy_logic.AST.compile = ivy_ast.AST.compile = thing
ivy_logic.AST.cmpl = ivy_ast.AST.cmpl = other_thing

op_pairs = [
    (ivy_ast.And,ivy_logic.And),
    (ivy_ast.Or,ivy_logic.Or),
    (ivy_ast.Not,ivy_logic.Not),
    (ivy_ast.Globally,ivy_logic.Globally),
    (ivy_ast.Eventually,ivy_logic.Eventually),
    (ivy_ast.And,ivy_logic.And),
    (ivy_ast.Definition,ivy_logic.Definition),
    (ivy_ast.Implies,ivy_logic.Implies),
    (ivy_ast.Iff,ivy_logic.Iff),
    (ivy_ast.Ite,ivy_logic.Ite),
]

for fc,tc in op_pairs:
    fc.cmpl = lambda self,tc=tc: tc(*[a.compile() for a in self.args])


class Context(object):
    def __enter__(self):
        self.old_context = globals().get(self.name,None)
        globals()[self.name] = self
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        globals()[self.name] = self.old_context
        return False # don't block any exceptions

class ReturnContext(Context):
    def __init__(self,values,lineno=None):
        self.values = values
        self.lineno = lineno
        self.name = 'return_context'
    

class ExprContext(Context):
    """ Context Manager for compiling an expression. """
    def __init__(self,code=None,local_syms=None,lineno=None):
        self.code = code if code != None else []
        self.local_syms = local_syms if local_syms != None else []
        self.lineno = lineno
        self.name = 'expr_context'
    def extract(self):
        for c in self.code:
            c.lineno = self.lineno
        if len(self.code) == 1:
            return self.code[0]
        res = LocalAction(*(self.local_syms + [Sequence(*self.code)]))
        res.lineno = self.lineno
        return res


class TopContext(Context):
    """ Context Manager for compiling an expression. """
    def __init__(self,actions):
        self.actions = actions
        self.name = 'top_context'

return_context = None
expr_context = None
top_context = None

def pull_args(args,num,sym,top):
    if len(args) < num:
        raise IvyError(None,'not enough arguments to {}'.format(sym))
    if top and len(args) > num:
        raise IvyError(None,'too many arguments to {}'.format(sym))
    res = args[:num]
    del args[:num]
    return res


class cfrfail(Exception):
    def __init__(self,symbol_name):
        self.symbol_name = symbol_name

def compile_field_reference_rec(symbol_name,args,top=False):
    sym = ivy_logic.find_polymorphic_symbol(symbol_name,throw=False)
    if sym is None:
        parent_name,child_name = iu.parent_child_name(symbol_name)
        if parent_name == 'this':
            raise cfrfail(symbol_name)
        try:
            with ReturnContext(None):
                base = compile_field_reference_rec(parent_name,args)
        except cfrfail as err:
            raise cfrfail(symbol_name if err.symbol_name in im.module.hierarchy else err.symbol_name)
        sort = base.sort
        sort_parent,sort_child = iu.parent_child_name(sort.name)
        destr_name = iu.compose_names(sort_parent,child_name)
        if top_context and destr_name in top_context.actions:
            if not expr_context:
                raise IvyError(None,'call to action {} not allowed outside an action'.format(destr_name))
            args.insert(0,base)
            return field_reference_action(destr_name,args,top)
        sym = ivy_logic.find_polymorphic_symbol(destr_name)
        args.insert(0,base)
    if hasattr(sym.sort,'dom') and len(sym.sort.dom) > 0:
        res = sym(*pull_args(args,len(sym.sort.dom),sym,top))
        return res
    return sym
                           
def field_reference_action(actname,args,top):
    nformals = len(top_context.actions[actname][0])
    return compile_inline_call(ivy_ast.Atom(actname,[]),pull_args(args,nformals,actname,top))

def compile_field_reference(symbol_name,args):
    try:
        return compile_field_reference_rec(symbol_name,args,top=True)
    except cfrfail as err:
        if symbol_name in ivy_logic.sig.sorts:
            raise IvyError(None,"type {} used where a function or individual symbol is expected".format(err.symbol_name))
        raise IvyError(None,"unknown symbol: {}".format(err.symbol_name))

    
def sort_infer_contravariant(term,sort):
    try:
        return sort_infer(term,sort,True)
    except ivy_logic.Error:
        res = sort_infer(term)
        if not(res.sort == sort or im.module.is_variant(sort,res.sort)):
            raise IvyError(None,"cannot convert argument of type {} to {}".format(res.sort,sort))
        return res

def compile_inline_call(self,args):
    params,returns = top_context.actions[self.rep]
    if return_context is None or return_context.values is None:
        if len(returns) != 1:
            raise IvyError(self,"wrong number of return values")
            # TODO: right now we can't do anything with multiple returns
            sorts = [cmpl_sort(r.sort) for r in returns]
            ress = []
            for sort in sorts:
                res = ivy_logic.Symbol('loc:'+str(len(expr_context.local_syms)),sort)
                expr_context.local_syms.append(res)
                ress.append(res())
            expr_context.code.append(CallAction(*([ivy_ast.Atom(self.rep,args)]+ress)))
            return ivy_ast.Tuple(*ress)
        sort = cmpl_sort(returns[0].sort)
        res = ivy_logic.Symbol('loc:'+str(len(expr_context.local_syms)),sort)
        expr_context.local_syms.append(res)
        return_values = [res]
    else:
        return_values = return_context.values
        if len(returns) != len(return_values):
            raise IvyError(self,"wrong number of return values")
    with ASTContext(self):
        if len(params) != len(args):
            raise iu.IvyError(self,"wrong number of input parameters (got {}, expecting {})".format(len(args),len(params)))
        args = [sort_infer_contravariant(a,cmpl_sort(p.sort)) for a,p in zip(args,params)]
    expr_context.code.append(CallAction(*([ivy_ast.Atom(self.rep,args)]+return_values)))
    if return_context is None or return_context.values is None:
        return res()
    return None

def compile_app(self):
    args = [a.compile() for a in self.args]
    # handle action calls in rhs of assignment
    if expr_context and top_context and self.rep in top_context.actions:
        return compile_inline_call(self,args)
    sym = self.rep.cmpl() if isinstance(self.rep,ivy_ast.NamedBinder) else ivy_logic.Equals if self.rep == '=' else ivy_logic.find_polymorphic_symbol(self.rep,throw=False) 
    if sym is not None:
        return (sym)(*args)
    res = compile_field_reference(self.rep,args)
    return res
    
def cmpl_sort(sortname):
    return ivy_logic.find_sort(resolve_alias(sortname))

def cmpl_native_expr(self):
    res = self.clone([a.compile() for a in self.args])
    res.sort = ivy_logic.TopS
    return res

ivy_ast.NativeExpr.cmpl = cmpl_native_expr

ivy_ast.App.cmpl = ivy_ast.Atom.cmpl = compile_app

ivy_ast.Variable.cmpl = lambda self: ivy_logic.Variable(self.rep,cmpl_sort(self.sort) if isinstance(self.sort,str) else self.sort)

ivy_ast.ConstantSort.cmpl = lambda self,name: ivy_logic.ConstantSort(name)

ivy_ast.EnumeratedSort.cmpl = lambda self,name: ivy_logic.EnumeratedSort(name,self.extension)

SymbolList.cmpl = lambda self: self.clone([find_symbol(s) for s in self.symbols])

def cquant(q):
    return ivy_logic.ForAll if isinstance(q,ivy_ast.Forall) else ivy_logic.Exists

ivy_ast.Quantifier.cmpl = lambda self: cquant(self)([v.compile() for v in self.bounds],self.args[0].compile())

ivy_ast.NamedBinder.cmpl = lambda self: ivy_logic.NamedBinder(
    self.name,
    [v.compile() for v in self.bounds],
    self.args[0].compile()
)

ivy_ast.LabeledFormula.cmpl = lambda self: self.clone([self.label,sortify_with_inference(self.formula)])

# compiling update patterns is complicated because they declare constants internally
def UpdatePattern_cmpl(self):
    with ivy_logic.sig.copy():
        return ivy_ast.AST.cmpl(self)
        
UpdatePattern.cmpl = UpdatePattern_cmpl

def ConstantDecl_cmpl(self):
    return self.clone([compile_const(v,ivy_logic.sig) for v in self.args])

ConstantDecl.cmpl =  ConstantDecl_cmpl 

def Old_cmpl(self):
    foo = self.args[0].compile()
    return foo.rep.prefix('old_')(*foo.args)

ivy_ast.Old.cmpl = Old_cmpl

def get_arg_sorts(sig,args,term=None):
    if term is not None:
        args = sortify_with_inference(ivy_ast.AST(*(args+[term]))).args[0:-1]
        return [arg.get_sort() for arg in args]
    return [arg.compile().get_sort() for arg in args]
                
def get_function_sort(sig,args,rng,term=None):
    return ivy_logic.FunctionSort(*(get_arg_sorts(sig,args,term)+[rng])) if args else rng

def get_relation_sort(sig,args,term=None):
    return ivy_logic.RelationSort(get_arg_sorts(sig,args,term))

def sortify(ast):
#    print "compiling : {}".format(ast)
    return ast.compile()

def sortify_with_inference(ast):
#    print "compiling : {}".format(ast)
    with top_sort_as_default():
        res = ast.compile()
    with ASTContext(ast):
        res = sort_infer(res)
    return res


ivy_ast.AST.compile_with_sort_inference = sortify_with_inference

def compile_const(v,sig):
    with ASTContext(v):
      rng = cmpl_sort(v.sort) if hasattr(v,'sort') else ivy_logic.default_sort()
      sort = get_function_sort(sig,v.args,rng)
      with sig:
          return add_symbol(v.rep,sort)
    

def compile_local(self):
    sig = ivy_logic.sig.copy()
    with sig:
        ls = self.args[0:-1]
        if len(ls) == 1 and isinstance(ls[0],AssignAction):
            v = ls[0]
            lhs = v.args[0]
            rhs = v.args[1]
            # temporarily rename lhs symbol in case it clashes with an existing symbol
#            tmp_lhs = lhs.prefix('__var_tmp:')
            tmp_lhs = lhs
            code = []
            local_syms = []
            with ExprContext(code,local_syms):
                with alpha_sort_as_default():
                    sym = compile_const(tmp_lhs,sig)
                    ctmp_lhs = tmp_lhs.compile()
                    crhs = rhs.compile()
            with ASTContext(self):
                teq = sort_infer(Equals(ctmp_lhs,crhs))
            clhs,crhs = list(teq.args)
#            clhs = clhs.drop_prefix('__var_tmp:')
            asgn = v.clone([clhs,crhs])
            ivy_logic.remove_symbol(sym)
            if clhs.rep.name in sig.symbols:
                del sig.symbols[clhs.rep.name] # shadow the existing symbol
            ivy_logic.add_symbol(clhs.rep.name,clhs.rep.sort)
            body = sortify(self.args[-1])
            lines = body.args if isinstance(body,Sequence) else [body]
            body = Sequence(*([asgn]+lines))
            code.append(LocalAction(clhs.rep,body))
            for c in code:
                c.lineno = self.lineno
            if len(code) == 1:
                return code[0]
            res = LocalAction(*(local_syms + [Sequence(*code)]))
            res.lineno = self.lineno
            return res
        cls = [compile_const(v,sig) for v in ls]
        body = sortify(self.args[-1])
        res = LocalAction(*(cls+[body]))
        res.lineno = self.lineno
        return res

LocalAction.cmpl = compile_local

def compile_assign(self):
    code = []
    local_syms = []
    with ExprContext(code,local_syms):
        if isinstance(self.args[0],ivy_ast.Tuple):
            args = [sortify_with_inference(a) for a in self.args]
            if not isinstance(args[1],ivy_ast.Tuple) or len(args[0].args) != len(args[1].args):
                raise IvyError(self,"wrong number of values in assignment");
            for lhs,rhs in zip(args[0].args,args[1].args):
                code.append(AssignAction(lhs,rhs))
        else:
            with top_sort_as_default():
                args = [a.compile() for a in self.args]
            if isinstance(args[1],ivy_ast.Tuple):
                raise IvyError(self,"wrong number of values in assignment");
            asorts = [a.sort for a in args]
            with ASTContext(self):
                if im.module.is_variant(*asorts):
                    teq = sort_infer(ivy_logic.pto(*asorts)(*args))
                else:
                    teq = sort_infer(Equals(*args))
            args = list(teq.args)
            code.append(AssignAction(*args))
        for c in code:
            c.lineno = self.lineno
        if len(code) == 1:
            return code[0]
        res = LocalAction(*(local_syms + [Sequence(*code)]))
        res.lineno = self.lineno
        return res

AssignAction.cmpl = compile_assign

def compile_call(self):
    assert top_context
    ctx = ExprContext(lineno = self.lineno)
    name = self.args[0].rep
    if name not in top_context.actions:
        with ctx:
            with ReturnContext([a.cmpl() for a in self.args[1:]]):
                res = compile_field_reference(name,[a.compile() for a in self.args[0].args])
        if res is not None:
            raise IvyError(self,'call to non-action')
        res = ctx.extract()
        return res
    #    print "compiled call action: {}".format(res)
        return res

    with ctx:
        args = [a.cmpl() for a in self.args[0].args]
    params,returns = top_context.actions[name]
    if len(returns) != len(self.args) - 1:
        raise iu.IvyError(self,"wrong number of output parameters (got {}, expecting {})".format(len(self.args) - 1,len(returns)))
    if len(params) != len(args):
        raise iu.IvyError(self,"wrong number of input parameters (got {}, expecting {})".format(len(args),len(params)))
    with ASTContext(self):
        mas = [sort_infer(a,cmpl_sort(p.sort)) for a,p in zip(args,params)]
#        print self.args
    res = CallAction(*([ivy_ast.Atom(name,mas)] + [a.cmpl() for a in self.args[1:]]))
    res.lineno = self.lineno
    ctx.code.append(res)
    res = ctx.extract()
#    print "compiled call action: {}".format(res)
    return res

CallAction.cmpl = compile_call


def compile_if_action(self):
    if isinstance(self.args[0],ivy_ast.Some):
        sig = ivy_logic.sig.copy()
        with sig:
            ls = self.args[0].params()
            fmla = self.args[0].fmla()
            cls = [compile_const(v,sig) for v in ls]
            sfmla = sortify_with_inference(fmla)
            sargs = cls+[sfmla]
            if isinstance(self.args[0],ivy_ast.SomeMinMax):
                sargs.append(sortify_with_inference(self.args[0].index()))
            args = [self.args[0].clone(sargs),self.args[1].compile()]
        args += [a.compile() for a in self.args[2:]]
        return self.clone(args)
    else:
        ctx = ExprContext(lineno = self.lineno)
        with ctx:
            cond = sortify_with_inference(self.args[0])
        rest = [a.compile() for a in self.args[1:]]
        ctx.code.append(self.clone([cond]+rest))
        res = ctx.extract()
        return res

IfAction.cmpl = compile_if_action

def compile_while_action(self):
        ctx = ExprContext(lineno = self.lineno)
        with ctx:
            cond = sortify_with_inference(self.args[0])
            invars = map(sortify_with_inference,self.args[2:])
        body = self.args[1].compile()
        if ctx.code:
            raise iu.IvyError(self,'while condition may not contain action calls')
        ctx.code.append(self.clone([cond,body]+invars))
        res = ctx.extract()
        return res

WhileAction.cmpl = compile_while_action

def compile_assert_action(self):
    ctx = ExprContext(lineno = self.lineno)
    with ctx:
        cond = sortify_with_inference(self.args[0])
    ctx.code.append(self.clone([cond]))
    res = ctx.extract()
    return res

AssertAction.cmpl = compile_assert_action
AssumeAction.cmpl = compile_assert_action

def compile_native_arg(arg):
    if isinstance(arg,ivy_ast.Variable):
        return sortify_with_inference(arg)
    if arg.rep in ivy_logic.sig.symbols:
        return sortify_with_inference(arg)
    res = arg.clone(map(sortify_with_inference,arg.args)) # handles action names
    return res.rename(resolve_alias(res.rep))

def compile_native_symbol(arg):
    name = arg.rep
    if name in ivy_logic.sig.symbols:
        sym = ivy_logic.sig.symbols[name]
        if not isinstance(sym,ivy_logic.UnionSort):
            return sym
    name = resolve_alias(name)
    if name in ivy_logic.sig.sorts:
        return ivy_logic.Variable('X',ivy_logic.sig.sorts[name])
    if ivy_logic.is_numeral_name(name):
        return ivy_logic.Symbol(name,ivy_logic.TopS)
    raise iu.IvyError(arg,'{} is not a declared symbol or type'.format(name))

def compile_native_action(self):
    fields = self.args[0].code.split('`')
    args = [self.args[0]] + [compile_native_arg(a) if not fields[i*2].endswith('"') else compile_native_symbol(a) for i,a in enumerate(self.args[1:])]
    return self.clone(args)

NativeAction.cmpl = compile_native_action

def compile_native_name(atom):
    assert all(isinstance(a,ivy_ast.Variable) and isinstance(a.sort,str) for a in atom.args)
    return ivy_ast.Atom(atom.rep,[ivy_ast.Variable(a.rep,resolve_alias(a.sort)) for a in atom.args])

def compile_native_def(self):
    fields = self.args[1].code.split('`')
    args = [compile_native_name(self.args[0]),self.args[1]] + [compile_native_arg(a) if not fields[i*2].endswith('"') else compile_native_symbol(a) for i,a in enumerate(self.args[2:])]
    return self.clone(args)

def compile_action_def(a,sig):
    sig = sig.copy()
    if not hasattr(a.args[1],'lineno'):
        print a
    assert hasattr(a.args[1],'lineno')
    with sig:
        with ASTContext(a.args[1]):
            params = a.args[0].args
            pformals = [v.to_const('prm:') for v in params] 
            if params:
                subst = dict((x.rep,y) for x,y in zip(params,pformals))
                a = ivy_ast.substitute_ast(a,subst)
                assert hasattr(a.args[1],'lineno')
    #            a = ivy_ast.subst_prefix_atoms_ast(a,subst,None,None)
    #            print "after: %s" % (a)
            # convert object paramaters to arguments (object-orientation!)
            formals =  [compile_const(v,sig) for v in pformals + a.formal_params]
            returns = [compile_const(v,sig) for v in a.formal_returns]
    #        print returns
            res = sortify(a.args[1])
            assert hasattr(res,'lineno'), res
            for suba in res.iter_subactions():
                if isinstance(suba,CallAction):
                    if any(lu.used_variables_ast(a) for a in suba.args[0].args):
#                        iu.dbg('a.args[0]')
#                        iu.dbg('a.formal_params')
#                        iu.dbg('suba.lineno')
#                        iu.dbg('suba')
                        raise iu.IvyError(suba,"call may not have free variables")
            res.formal_params = formals
            res.formal_returns = returns
            res.label = a.args[0].relname
            return res

def compile_defn(df):
    has_consts = any(not isinstance(p,ivy_ast.Variable) for p in df.args[0].args)
    sig = ivy_logic.sig.copy() if has_consts else ivy_logic.sig
    with ivy_ast.ASTContext(df):
        with sig:
            for p in df.args[0].args:
                if not isinstance(p,ivy_ast.Variable):
                    compile_const(p,sig)
            if isinstance(df.args[1],ivy_ast.SomeExpr):
                ifval = df.args[1].if_value() or df.args[1].params()[0]
                elseval = df.args[1].else_value() or ifval
                eqn = ivy_ast.Forall(df.args[1].params(),
                                     ivy_ast.Atom('=',(df.args[0],ivy_ast.Ite(df.args[1].fmla(),ifval,elseval))))
                fmla = sortify_with_inference(eqn)
                args = [list(fmla.variables)[0],fmla.body.args[1].args[0]]
                if df.args[1].if_value() :
                    args.append(fmla.body.args[1].args[1])
                if df.args[1].else_value() :
                    args.append(fmla.body.args[1].args[2])
                df = ivy_logic.Definition(fmla.body.args[0],ivy_logic.Some(*args))
            else:
                eqn = ivy_ast.Atom('=',(df.args[0],df.args[1]))
                eqn = sortify_with_inference(eqn)
                df = ivy_logic.Definition(eqn.args[0],eqn.args[1])
            return df
    
def compile_schema_prem(self,sig):
    if isinstance(self,ivy_ast.ConstantDecl):
        with ivy_logic.WithSorts(sig.sorts.values()):
            sym = compile_const(self.args[0],sig)
        return self.clone([sym])
    elif isinstance(self,ivy_ast.DerivedDecl):
        raise IvyErr(self,'derived functions in schema premises not supported yet')
    elif isinstance(self,ivy_ast.TypeDef):
        t = ivy_logic.UninterpretedSort(self.args[0].rep)
        sig.sorts[t.name] = t
        return t
    elif isinstance(self,ivy_ast.LabeledFormula):
        with ivy_logic.WithSymbols(sig.all_symbols()):
            return self.compile()
    
def compile_schema_conc(self,sig):
    with ivy_logic.WithSymbols(sig.all_symbols()):
        if isinstance(self,ivy_ast.Definition):
            return compile_defn(self)
        return sortify_with_inference(self)

def compile_schema_body(self):
    sig = ivy_logic.Sig()
    prems = [compile_schema_prem(p,sig) for p in self.args[:-1]]
    res = ivy_ast.SchemaBody(*(prems+[compile_schema_conc(self.args[-1],sig)]))
    res.instances = []
    return res

ivy_ast.SchemaBody.compile = compile_schema_body    

def compile_schema_instantiation(self,fmla):
    if self.schemaname() not in im.module.schemata:
        raise iu.IvyError(self,'schema {} does not exist'.format(self.schemaname()))
    schema = im.module.schemata[self.schemaname()]
    schemasyms = [x.args[0] for x in schema.prems() if isinstance(x,ivy_ast.ConstantDecl)]
    schemasorts = [s for s in schema.prems() if isinstance(s,ivy_logic.UninterpretedSort)]
    sortmap = dict()
    pairs = []
    for d in self.match():
        x,y = d.lhs(),d.rhs()
        if isinstance(x,ivy_ast.Atom) and any((s.name == x.rep) for s in schemasorts):
            xsort = ivy_logic.UninterpretedSort(x.rep)
            if xsort in sortmap:
                raise iu.IvyError(self,'symbol {} is matched twice'.format(x))
            if y.rep not in ivy_logic.sig.sorts:
                raise iu.IvyError(self,'symbol {} is not a sort'.format(y))
            sortmap[xsort] = ivy_logic.UninterpretedSort(y.rep)
        else:
            pairs.append((x,y))
    sorted_pairs = []
    with top_sort_as_default():
        for x,y in pairs:
            with ivy_logic.WithSymbols(schemasyms):
                x,_ = ivy_logic.sort_infer_list([x.compile(),schema.conc()])
            x = ip.apply_match_alt(sortmap,x)
            y,_,_ = ivy_logic.sort_infer_list([y.compile(),fmla,x])
            sorted_pairs.append((x,y))

    return self.clone([self.args[0]]+
                      [ivy_ast.Definition(x,y) for x,y in sortmap.iteritems()] +
                      [ivy_ast.Definition(x,y) for x,y in sorted_pairs])

last_fmla = None

ivy_ast.SchemaInstantiation.compile = lambda self: compile_schema_instantiation(self,last_fmla)

def resolve_alias(name): 
    if name in im.module.aliases:
        return im.module.aliases[name]
    parts = name.rsplit(iu.ivy_compose_character,1)
    if len(parts) == 2:
        return resolve_alias(parts[0]) + iu.ivy_compose_character + parts[1]
    return name

defined_attributes = set(["weight","test"])

class IvyDomainSetup(IvyDeclInterp):
    def __init__(self,domain):
        self.domain = domain
    def alias(self,dfn):
        self.domain.aliases[dfn.defines()] = resolve_alias(dfn.args[1].rep)
    def object(self,atom):
        self.domain.add_object(atom.rep)
    def axiom(self,ax):
        self.domain.labeled_axioms.append(ax.compile())
    def property(self,ax):
        lf = ax.compile()
        self.domain.labeled_props.append(lf)
        self.last_fact = lf
    def named(self,lhs):
        cond = ivy_logic.drop_universals(self.last_fact.formula)
        if not ivy_logic.is_exists(cond) or len(cond.variables) != 1:
            raise IvyError(lhs,'property is not existential')
        rng = list(cond.variables)[0].sort
        vmap = dict((x.name,x) for x in lu.variables_ast(cond))
        used = set()
        with ivy_logic.UnsortedContext():
            args = [arg.compile() for arg in lhs.args]
        targs = []
        for a in args:
            if a.name in used:
                raise IvyError(lhs,'repeat parameter: {}'.format(a.name))
            used.add(a.name)
            if a.name in vmap:
                v = vmap[a.name]
                targs.append(v)
                if not (ivy_logic.is_topsort(a.sort) or a.sort != v.sort):
                    raise IvyError(lhs,'bad sort for {}'.format(a.name))
            else:
                if ivy_logic.is_topsort(a.sort):
                    raise IvyError(lhs,'cannot infer sort for {}'.format(a.name))
                targs.append(a)
        for x in vmap:
            if x not in used:
                raise IvyError(lhs,'{} must be a parameter of {}'.format(x,lhs.rep))
        dom = [x.sort for x in targs]
        sym = self.domain.sig.add_symbol(lhs.rep,ivy_logic.FuncConstSort(*(dom+[rng])))
        self.domain.named.append((self.last_fact,sym(*targs) if targs else sym))
    def schema(self,sch):
        if isinstance(sch.defn.args[1],ivy_ast.SchemaBody):
            self.domain.schemata[sch.defn.defines()] = sch.defn.args[1].compile()
        else:
            self.domain.schemata[sch.defn.defines()] = sch
    def instantiate(self,inst):
        try:
            self.domain.schemata[inst.relname].instantiate(inst.args)
        except LookupError:
            raise IvyError(inst,"{} undefined in instantiation".format(inst.relname))
        except IndexError:
            raise IvyError(inst,"wrong number of parameters in instantiation")
    def relation(self,rel):
        with ASTContext(rel):
            sym = add_symbol(rel.relname,get_relation_sort(self.domain.sig,rel.args))
        self.domain.all_relations.append((sym,len(rel.args)))
        self.domain.relations[sym] = len(rel.args)
    def individual(self,v):
        sym = compile_const(v,self.domain.sig)
#        print "sym: {!r}".format(sym)
        self.domain.functions[sym] = len(v.args)
        return sym
    def destructor(self,v):
        sym = self.individual(v)
        dom = sym.sort.dom
        if not dom:
            raise IvyError(v,"A destructor must have at least one parameter")
        self.domain.destructor_sorts[sym.name] = dom[0]
        self.domain.sort_destructors[dom[0].name].append(sym)
    def add_definition(self,ldf):
        defs = self.domain.native_definitions if isinstance(ldf.formula.args[1],ivy_ast.NativeExpr) else self.domain.definitions
        lhsvs = list(lu.variables_ast(ldf.formula.args[0]))
        for idx,v in enumerate(lhsvs):
            if v in lhsvs[idx+1:]:
                raise IvyError(ldf,"Variable {} occurs twice on left-hand side of definition".format(v))
        for v in lu.used_variables_ast(ldf.formula.args[1]):
            if v not in lhsvs:
                raise IvyError(ldf,"Variable {} occurs free on right-hand side of definition".format(v))
        defs.append(ldf)
        self.last_fact = ldf

    def derived(self,ldf):
        try:
            label = ldf.label
            df = ldf.formula
            lhs = df.args[0]
            sym = ivy_logic.add_symbol(lhs.rep,ivy_logic.TopFunctionSort(len(lhs.args)))
            df  = compile_defn(df)
            ivy_logic.remove_symbol(sym)
            add_symbol(df.args[0].rep.name,df.args[0].rep.sort)
            self.domain.all_relations.append((sym,len(lhs.args)))
            self.domain.relations[sym] = len(lhs.args)
            self.add_definition(ldf.clone([label,df]))
            self.domain.updates.append(DerivedUpdate(df))
            self.domain.symbol_order.append(sym)
        except ValueError:
            raise IvyError(df,"definition of derived relation must be a cube")
    def definition(self,ldf):
        label = ldf.label
        df = ldf.formula
        df = compile_defn(df)
        self.add_definition(ldf.clone([label,df]))
        self.domain.updates.append(DerivedUpdate(df))
        self.domain.symbol_order.append(df.args[0].rep)
        if not self.domain.sig.contains_symbol(df.args[0].rep):
            add_symbol(df.args[0].rep.name,df.args[0].rep.sort)
            
    def proof(self,pf):
        global last_fmla
        last_fmla = self.last_fact.formula
        self.domain.proofs.append((self.last_fact,pf.compile()))

    def progress(self,df):
        rel = df.args[0]
        with ASTContext(rel):
            sym = add_symbol(rel.relname,get_relation_sort(self.domain.sig,rel.args,df.args[1]))
        df = sortify_with_inference(df)
        self.domain.progress.append(df)
    def rely(self,df):
        df = sortify_with_inference(df)
        self.domain.rely.append(df)
    def mixord(self,df):
        self.domain.mixord.append(df)
    def concept(self,c):
        rel = c.args[0]
        with ASTContext(c):
          add_symbol(rel.relname,get_relation_sort(self.domain.sig,rel.args,c.args[1]))
        c = sortify_with_inference(c)
        self.domain.concept_spaces.append((c.args[0],c.args[1]))
    def update(self,upd):
        self.domain.updates.append(upd.compile())
    def type(self,typedef):
#        print "typedef {!r}".format(typedef)
        self.domain.sort_order.append(typedef.name)
        if isinstance(typedef,ivy_ast.GhostTypeDef):
            self.domain.ghost_sorts.add(typedef.name)
        if isinstance(typedef.value,ivy_ast.StructSort):
            sort = ivy_logic.ConstantSort(typedef.name)
            self.domain.sig.sorts[typedef.name] = sort
            # handle empty struct
            if typedef.name not in self.domain.sort_destructors:
                self.domain.sort_destructors[typedef.name] = []
            for a in typedef.value.args:
                p = a.clone([ivy_ast.Variable('V:dstr',sort.name)]+a.args)
                p.sort = a.sort
                with ASTContext(typedef):
                    with ASTContext(a):
                        self.destructor(p)
            return
        with ASTContext(typedef.value):
            sort = typedef.value.cmpl(typedef.name)
        self.domain.sig.sorts[typedef.name] = sort
        for c in sort.defines(): # register the type's constructors
            sym = Symbol(c,sort)
            self.domain.functions[sym] = 0
            self.domain.sig.symbols[c] = sym
            self.domain.sig.constructors.add(sym)
    def variant(self,v):
        for r in v.args:
            if r.rep not in self.domain.sig.sorts:
                raise IvyError(v,"undefined sort: {}".format(r.rep))
        self.domain.variants[v.args[1].rep].append(self.domain.sig.sorts[v.args[0].rep])
    def implementtype(self,thing):
        v = thing.formula
        for r in v.args:
            if r.rep not in self.domain.sig.sorts:
                raise IvyError(v,"undefined sort: {}".format(r.rep))
        impd = v.implemented()
        impr = v.implementer()
        if (impd in self.domain.native_types or
            impd in self.domain.sig.interp):
            raise IvyError(v,"{} is already interpreted".format(impd))
#        if impd in ivy_logic.sort_dependencies(impr):
#            raise IvyError(v,"cannot implement type {} with {} because {} depends on {}".format(impd,impr,impr,impd))
        ivy_logic.implement_type(ivy_logic.find_sort(impd),ivy_logic.find_sort(impr))
        self.domain.interps[impd].append(thing)
        
    def interpret(self,thing):
        sig = self.domain.sig
        interp = sig.interp
        if isinstance(thing.formula.args[1],ivy_ast.NativeType):
            lhs = thing.formula.args[0].rep
            if lhs in interp or lhs in self.domain.native_types :
                raise IvyError(thing,"{} is already interpreted".format(lhs))
            self.domain.native_types[lhs] = thing.formula.args[1]
            return
        lhs,rhs = (a.rep for a in thing.formula.args)
        self.domain.interps[lhs].append(thing)
        if lhs in self.domain.native_types :
            raise IvyError(thing,"{} is already interpreted".format(lhs))
        if lhs in interp:
            if interp[lhs] != rhs:
                raise IvyError(thing,"{} is already interpreted".format(lhs))
            return
        if isinstance(rhs,ivy_ast.Range):
            interp[lhs] = ivy_logic.EnumeratedSort(lhs,["{}:{}".format(i,lhs) for i in range(int(rhs.lo),int(rhs.hi)+1)])
            return
        for x,y,z in zip([sig.sorts,sig.symbols],
                         [slv.is_solver_sort,slv.is_solver_op],
                         ['sort','symbol']):
            if lhs in x:
                if not y(rhs):
                    raise IvyError(thing,"{} not a native {}".format(rhs,z))
                interp[lhs] = rhs
                if z == 'sort' and isinstance(rhs,str):
                    compile_theory(self.domain,lhs,rhs)
                return
        raise IvyUndefined(thing,lhs)
    def scenario(self,scen):
        for (s,lineno) in scen.places():
            with ASTContext(scen):
                sym = add_symbol(s,ivy_logic.RelationSort([]))
                self.domain.all_relations.append((sym,0))
                self.domain.relations[sym] = 0

    def mixin(self,m):
        if m.args[1].relname  != 'init' and m.args[1].relname not in top_context.actions:
            raise IvyError(m,'unknown action: {}'.format(m.args[1].relname))
            
class IvyConjectureSetup(IvyDeclInterp):
    def __init__(self,domain):
        self.domain = domain
    def conjecture(self,ax):
        cax = ax.compile()
        self.domain.labeled_conjs.append(cax)

def check_is_action(mod,ast,name):
    if name not in mod.actions:
        raise IvyError(ast,'{} is not an action'.format(name))

class IvyARGSetup(IvyDeclInterp):
    def __init__(self,mod):
        self.mod = mod
#    def individual(self,v):
#        self.mod.pvars.append(sortify(v).rep)
    def init(self,s):
        la = s.compile()
        self.mod.labeled_inits.append(la)
#        s = sortify_with_inference(s)
#        print "s:{}".format(s)
#        type_check(self.mod,s)
#         c = formula_to_clauses_tseitin(s)
#        if not c:
#            raise IvyError(ax,"initial condition must be a clause")
        im.module.init_cond = and_clauses(im.module.init_cond,formula_to_clauses(la.formula))
    def action(self,a):
        name = a.args[0].relname
        self.mod.actions[name] = compile_action_def(a,self.mod.sig)
        self.mod.public_actions.add(name)
    def state(self,a):
        self.mod.predicates[a.args[0].relname] = a.args[1]
    def mixin(self,m):
#        if any(a.args for a in m.args):
#            raise IvyError(m,"mixins may not have parameters")
        self.mod.mixins[m.args[1].relname].append(m)
    def _assert(self,a):
        with ASTContext(a):
            self.mod.assertions.append(type(a)(a.args[0],sortify_with_inference(a.args[1])))
    def isolate(self,iso):
        self.mod.isolates[iso.name()] = iso
    def export(self,exp):
        check_is_action(self.mod,exp,exp.exported())
        self.mod.exports.append(exp)
    def import_(self,imp):
        check_is_action(self.mod,imp,imp.imported())
        self.mod.imports.append(imp)
    def private(self,pvt):
        self.mod.privates.add(pvt.privatized())
    def delegate(self,exp):
        self.mod.delegates.append(exp)
    def native(self,native_def):
        self.mod.natives.append(compile_native_def(native_def))
    def attribute(self,a):
        lhs,rhs = a.args
#        if len(lhs.args) != 0:
#            raise IvyError(a,'attribute names may not have parameters')
        fields = lhs.rep.split(iu.ivy_compose_character)
        oname = iu.ivy_compose_character.join(fields[:-1])
        oname = 'this' if oname == '' else oname
        aname = fields[-1]
        if oname not in self.mod.actions and oname not in self.mod.hierarchy:
            raise IvyError(a,'"{}" does not name an action or object'.format(oname))
        if aname not in defined_attributes:
            raise IvyError(a,'"{}" does not name a defined attribute'.format(aname))
        self.mod.attributes[lhs.rep] = rhs
    def scenario(self,scen):
        init_tokens = set(p.rep for p in scen.args[0].args)
        transs_by_action = defaultdict(list)
        for tr in scen.args[1:]:
            transs_by_action[tr.args[2].args[1].args[0].rep].append(tr)
        for (place_name,lineno) in scen.places():
            sym = find_symbol(place_name)
            iname = place_name + '[init]'
            iact = AssignAction(sym,ivy_logic.And() if (place_name in init_tokens) else ivy_logic.Or())
            iact.formal_params = []
            iact.formal_returns = []
            iact.lineno = scen.lineno
            self.mod.actions[iname] = iact
            self.mixin(ivy_ast.MixinAfterDef(ivy_ast.Atom(iname),ivy_ast.Atom('init')))
        for actname,trs in transs_by_action.iteritems():
            choices = []
            params = None
            afters = []
            for tr in trs:
                scmix = tr.args[2]
                is_after = isinstance(scmix,ivy_ast.ScenarioAfterMixin)
                df = scmix.args[1]
                body = compile_action_def(df,self.mod.sig)
                seq = []
                if not is_after:
                    for p in tr.args[0].args:
                        seq.append(AssumeAction(find_symbol(p.rep)))
                    for p in tr.args[0].args:
                        seq.append(AssignAction(find_symbol(p.rep),ivy_logic.Or()))
                    for p in tr.args[1].args:
                        seq.append(AssignAction(find_symbol(p.rep),ivy_logic.And()))
                    seq.append(body)
                    seq = Sequence(*seq)
                else:
                    for p in tr.args[0].args:
                        seq.append(AssignAction(find_symbol(p.rep),ivy_logic.Or()))
                    for p in tr.args[1].args:
                        seq.append(AssignAction(find_symbol(p.rep),ivy_logic.And()))
                    seq.append(body)
                    seq = Sequence(*seq)
                    seq = IfAction(And(*[find_symbol(p.rep) for p in tr.args[0].args]),seq)
                if params is None:
                    params = body.formal_params
                    returns = body.formal_returns
                    mixer = scmix.args[0]
                    mixee = scmix.args[1].args[0]
                else:
                    aparams = df.formal_params + df.formal_returns
                    subst = dict(zip(aparams,params+returns))
                    seq = substitute_constants_ast(seq,subst)
                seq.lineno = tr.lineno
                if not is_after:
                    choices.append(seq)
                else:
                    afters.append(seq)
            if choices:
                choice = BalancedChoice(choices)
                choice.lineno = choices[0].lineno
                choice.formal_params = params
                choice.formal_returns = returns
                self.mod.actions[mixer.rep] = choice
                self.mixin(ivy_ast.MixinBeforeDef(mixer,mixee))
            if afters:
                choice = Sequence(*afters)
                choice.lineno = afters[0].lineno
                choice.formal_params = params
                choice.formal_returns = returns
                self.mod.actions[mixer.rep] = choice
                self.mixin(ivy_ast.MixinAfterDef(mixer,mixee))
                
        
def BalancedChoice(choices):
    if len(choices) == 1:
        return choices[0]
    return ChoiceAction(BalancedChoice(choices[0:len(choices)/2]),
                        BalancedChoice(choices[len(choices)/2:]))

def ivy_new(filename = None):
#    d = Interp()
    if filename:
        f = open(filename,'rU')
        if not f:
            raise IvyError(None,"not found: %s" % filename)
        ivy_load_file(f)
    ag = AnalysisGraph()
    return ag

isolate = iu.Parameter("isolate")    

# collect actions in case of forward reference
def collect_actions(decls):
    res = {}
    for d in decls:
        if d.name() == 'action':
            for a in d.args:
                res[a.defines()] = (a.args[0].args + a.formal_params,a.formal_returns)
    return res

def infer_parameters(decls):
    mixees = defaultdict(list)
    actdecls = dict()
    for d in decls:
        if d.name() == "action":
            for a in d.args:
                actdecls[a.defines()] = a
    for d in decls:
        if d.name() == "mixin":
            for a in d.args:
                mixeename = a.args[1].relname
                if mixeename == "init":
                    continue
                if mixeename not in actdecls:
                    raise IvyError(a,"undefined action: {}".format(mixeename))
                mixees[a.args[0].relname].append(mixeename)
    for d in decls:
        if d.name() == "action":
            for a in d.args:
                am = mixees[a.defines()]
                if len(am) == 1 and am[0] in actdecls:
                    mixin = a.args[1]
                    mixee = actdecls[am[0]]
                    nparms = len(a.args[0].args)
                    mnparms = len(mixee.args[0].args)
                    if len(a.formal_params) + nparms > len(mixee.formal_params) + mnparms:
                        raise iu.IvyError(a.args[1],'monitor has too many input parameters for {}'.format(mixee.defines()))
                    if len(a.formal_returns) > len(mixee.formal_returns):
                        raise iu.IvyError(a.args[1],'monitor has too many output parameters for {}'.format(mixee.defines()))
                    required = mnparms - nparms
                    if len(a.formal_params) < required:
                        raise iu.IvyError(a.args[1],'monitor must supply at least {} explicit input parameters for {}'.format(required,mixee.defines()))
                    xtraps = (mixee.args[0].args+mixee.formal_params)[len(a.formal_params)+nparms:]
                    xtrars = mixee.formal_returns[len(a.formal_returns):]
                    if xtraps or xtrars:
                        a.formal_params.extend(xtraps)
                        a.formal_returns.extend(xtrars)
                        subst = dict((x.drop_prefix('fml:').rep,x.rep) for x in (xtraps + xtrars))
                        a.args[1] = ivy_ast.subst_prefix_atoms_ast(a.args[1],subst,None,None)

def check_instantiations(mod,decls):
    schemata = set()
    for decl in decls.decls:
        if isinstance(decl,ivy_ast.SchemaDecl):
            for inst in decl.args:
                schemata.add(inst.defines())
    for decl in decls.decls:
        if isinstance(decl,ivy_ast.InstantiateDecl):
            for inst in decl.args:
                if inst.relname not in schemata:
                    raise IvyError(inst,"{} undefined in instantiation".format(inst.relname))


def sort_dependencies(mod,sortname):
    if sortname in mod.sort_destructors:
        for destr in mod.sort_destructors[sortname]:
            return [s.name for s in destr.sort.dom[1:] + (destr.sort.rng,)]
    if sortname in mod.interps:
        t = mod.interps[sortname]
        if isinstance(t,ivy_ast.NativeType):
            return [s.rep for s in t.args[1:] if s.rep in mod.sig.sorts]
    return []

def create_sort_order(mod):
    arcs = [(x,s) for s in mod.sort_order for x in sort_dependencies(mod,s)]
    # do nothing if sccs already sorted
    number = dict((x,i) for i,x in enumerate(mod.sort_order))
    if all(x == 'bool' or number[x] < number[y] for x,y in arcs):
        return
    m = defaultdict(set)
    for x,y in arcs:
        m[x].add(y)
    sccs = tarjan(m)
    # remove trivial sccs
    sccs = [scc for scc in sccs if len(scc) > 1 or scc[0] in sort_dependencies(mod,scc[0])]
    if len(sccs) > 0:
        raise iu.IvyError(None,'these sorts form a dependency cycle: {}.'.format(','.join(sccs[0])))
    mod.sort_order = iu.topological_sort(mod.sort_order,arcs)

def tarjan_arcs(arcs,notriv=True):
    m = defaultdict(set)
    for x,y in arcs:
        m[x].add(y)
    sccs = tarjan(m)
    if notriv:
        sccs = [scc for scc in sccs if len(scc) > 1 or scc[0] in m[scc[0]]]
    return sccs
        

def check_definitions(mod):
    arcs = [(d.formula.defines(),x)
            for d in mod.definitions
            for x in lu.symbols_ast(d.formula.args[1])]
    dmap = dict((d.formula.defines(),d) for d in mod.definitions)
    pmap = dict((lf.id,p) for lf,p in mod.proofs)
    sccs = tarjan_arcs(arcs)
    import ivy_proof
    prover = ivy_proof.ProofChecker([],[],mod.schemata)
    for scc in sccs:
        if len(scc) > 1:
            raise iu.IvyError(None,'these definitions form a dependency cycle: {}'.format(','.join(scc)))
        d = dmap[scc[0]]
        if d.id not in pmap:
            raise iu.IvyError(d,'definition of {} requires a recursion schema'.format(d.formula.defines()))
        prover.admit_definition(d,pmap[d.id])
        
def check_properties(mod):
    props = mod.labeled_props
    mod.labeled_props = []
    pmap = dict((lf.id,p) for lf,p in mod.proofs)
    nmap = dict((lf.id,n) for lf,n in mod.named)

    def named_trans(prop):
        if prop.id in nmap:
            name = nmap[prop.id]
            fmla = ivy_logic.drop_universals(prop.formula)
            v = list(fmla.variables)[0]
            fmla = fmla.body
            fmla = lu.substitute_ast(fmla,{v.name:name})
            prop = prop.clone([prop.label,fmla])
        return prop
            
    import ivy_proof
    prover = ivy_proof.ProofChecker([],[],mod.schemata)
    for prop in props:
        if prop.id in pmap:
            print 'checking {}...'.format(prop.label)
            subgoals = prover.admit_proposition(prop,pmap[prop.id])
            prop = named_trans(prop)
            if len(subgoals) == 0:
                mod.labeled_axioms.append(prop)
            else:
                for g in subgoals:
                    label = ia.compose_atoms(prop.label,g.label)
                    mod.labeled_props.append(g.clone([label,g.formula]))
                mod.labeled_props.append(prop)
                mod.subgoals.append((prop,subgoals))
        # elif prop.temporal:
        #     from ivy_l2s import l2s
        #     print "=================" + "\n" * 10
        #     l2s(mod, prop)
        else:
            mod.labeled_props.append(prop)
            if prop.id in nmap:
                nprop = named_trans(prop)
                mod.labeled_props.append(nprop)
                mod.subgoals.append((nprop,[prop]))
                


def ivy_compile_theory(mod,decls,**kwargs):
    IvyDomainSetup(mod)(decls)
    
def ivy_compile_theory_from_string(mod,theory,sortname,**kwargs):
    import StringIO
    sio = StringIO.StringIO(theory)
    module = read_module(sio)
    ivy = Ivy()
    inst_mod(ivy,module,None,{'t':sortname},dict())
    ivy_compile_theory(mod,ivy,**kwargs)

def compile_theory(mod,sortname,theoryname,**kwargs):
    theory = ith.get_theory(theoryname)
    if theory is not None:
        ivy_compile_theory_from_string(mod,theory,sortname,**kwargs)
    
def compile_theories(mod,**kwargs):
    for name,value in mod.sig.interp.iteritems():
        if name in mod.sig.sorts and isinstance(value,str):
            theory = th.get_theory(value)
            ivy_compile_theory_from_string(mod,theory,name,**kwargs)

def ivy_compile(decls,mod=None,create_isolate=True,**kwargs):
    mod = mod or im.module
    with mod.sig:
        check_instantiations(mod,decls)
        for name in decls.defined:
            mod.add_to_hierarchy(name)
#        infer_parameters(decls.decls)
        with TopContext(collect_actions(decls.decls)):
            IvyDomainSetup(mod)(decls)
            IvyConjectureSetup(mod)(decls)
            IvyARGSetup(mod)(decls)
        mod.macros = decls.macros
        # progress properties are not state symbols -- remove from sig
        for p in mod.progress:
            remove_symbol(p.defines())
        mod.type_check()
        # try instantiating all the actions to type check them
        for name,action in mod.actions.iteritems():
#            print "checking: {} = {}".format(name,action)
            type_check_action(action,mod)
            if not hasattr(action,'lineno'):
                print "no lineno: {}".format(name)
            assert hasattr(action,'formal_params'), action
    
            # print "actions:"
            # for x,y in mod.actions.iteritems():
            #     print iu.pretty("action {} = {}".format(x,y))

        create_sort_order(mod)
        check_definitions(mod)
        check_properties(mod)
        if create_isolate:
            iso.create_isolate(isolate.get(),mod,**kwargs)
            im.module.labeled_axioms.extend(im.module.labeled_props)
            im.module.theory_context().__enter__()


def clear_rules(modname):
    import sys
    if modname in sys.modules:
        d = sys.modules[modname].__dict__
    else:
        d = sys.modules['ivy.' + modname].__dict__
    for s in list(d):
        if s.startswith('p_'):
            del d[s]

def read_module(f,nested=False):
    import ivy_logic_parser
    import ivy_parser
    header = f.readline()
    s = '\n' + f.read() # newline at beginning to preserve line numbers
    header = string.strip(header)
    if header.startswith('#lang ivy'):
        version = header[len('#lang ivy'):]
        old_version = iu.get_string_version()
        iu.set_string_version(version)
        if version != old_version:
            if nested:
                raise IvyError(None,'#lang ivy{} expected'.format(old_version)) 
#            print "version: {}, old_version: {}".format(version,old_version)
            clear_rules('ivy_logic_parser')
            clear_rules('ivy_parser')
            reload(ivy_logic_parser)
            reload(ivy_parser)
        ivy_parser.importer = import_module
        decls = parse(s,nested)
    elif header == '//lang dafny1':
        decls = dc.parse_to_ivy(s)
    else:
        err = IvyError(None,'file must begin with "#lang ivyN.N"')
        err.lineno = 1
        if iu.filename:
            err.filename = iu.filename
        raise err
    return decls

def import_module(name):
    fname = name + '.ivy'
    try: 
        f = open(fname,'rU')
    except Exception:
        fname = os.path.join(os.path.dirname(os.path.abspath(__file__)),'include',fname)
        try:
            f = open(fname,'rU')
        except Exception:
            raise IvyError(None,"module {} not found in current directory or module path".format(name))
    with iu.SourceFile(fname):
        mod = read_module(f,nested=True)
    return mod

def ivy_load_file(f,**kwargs):
    decls = read_module(f)
    ivy_compile(decls,**kwargs)

def ivy_from_string(string,**kwargs):
    import StringIO
    sio = StringIO.StringIO(string)
    ivy_load_file(sio,**kwargs)
    return ivy_new()

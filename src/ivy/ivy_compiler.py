#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_art import *
import pickle
from ivy_interp import Interp, eval_state_facts
from functools import partial
from ivy_concept_space import *
from ivy_parser import parse,ConstantDecl,ActionDef
from ivy_actions import DerivedUpdate, type_check_action, type_check, SymbolList, UpdatePattern, ActionContext, LocalAction, AssignAction, CallAction, Sequence, IfAction, AssertAction, AssumeAction
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


ivy_ast.Variable.get_sort = lambda self: ivy_logic.find_sort(self.sort.rep)

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
   (ivy_ast.And,ivy_logic.And),
   (ivy_ast.Definition,ivy_logic.Definition),
   (ivy_ast.Implies,ivy_logic.Implies),
   (ivy_ast.Iff,ivy_logic.Iff),
   (ivy_ast.Ite,ivy_logic.Ite)]

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

expr_context = None
top_context = None

def compile_app(self):
    args = [a.compile() for a in self.args]
    # handle action calls in rhs of assignment
    if expr_context and top_context and self.rep in top_context.actions:
        returns = top_context.actions[self.rep]
        if len(returns) != 1:
            raise IvyError(self,"wrong number of return values")
            # TODO: right now we can't do anything with multiple returns
            sorts = [find_sort(r.sort) for r in returns]
            ress = []
            for sort in sorts:
                res = ivy_logic.Symbol('loc:'+str(len(expr_context.local_syms)),sort)
                expr_context.local_syms.append(res)
                ress.append(res())
            expr_context.code.append(CallAction(*([ivy_ast.Atom(self.rep,args)]+ress)))
            return ivy_ast.Tuple(*ress)
        sort = find_sort(returns[0].sort)
        res = ivy_logic.Symbol('loc:'+str(len(expr_context.local_syms)),sort)
        expr_context.local_syms.append(res)
        expr_context.code.append(CallAction(ivy_ast.Atom(self.rep,args),res))
        return res()
    return (ivy_logic.Equals if self.rep == '=' else ivy_logic.find_polymorphic_symbol(self.rep))(*args)
    

ivy_ast.App.cmpl = ivy_ast.Atom.cmpl = compile_app

ivy_ast.Variable.cmpl = lambda self: ivy_logic.Variable(self.rep,ivy_logic.find_sort(self.sort) if isinstance(self.sort,str) else self.sort)

ivy_ast.ConstantSort.cmpl = lambda self: ivy_logic.ConstantSort(self.rep)

ivy_ast.EnumeratedSort.cmpl = lambda self: ivy_logic.EnumeratedSort(self.name,self.extension)

SymbolList.cmpl = lambda self: self.clone([find_symbol(s) for s in self.symbols])

def cquant(q):
    return ivy_logic.ForAll if isinstance(q,ivy_ast.Forall) else ivy_logic.Exists

ivy_ast.Quantifier.cmpl = lambda self: cquant(self)([v.compile() for v in self.bounds],self.args[0].compile())

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
      rng = find_sort(v.sort) if hasattr(v,'sort') else ivy_logic.default_sort()
      return add_symbol(v.rep,get_function_sort(sig,v.args,rng))
    

def compile_local(self):
    sig = ivy_logic.sig.copy()
    with sig:
        ls = self.args[0:-1]
        cls = [compile_const(v,sig) for v in ls]
        res = LocalAction(*(cls+[sortify(self.args[-1])]))
        res.lineno = self.lineno
        return res

LocalAction.cmpl = compile_local

def compile_assign(self):
    code = []
    local_syms = []
    with ExprContext(code,local_syms):
        args = [sortify_with_inference(a) for a in self.args]
        if isinstance(args[0],ivy_ast.Tuple):
            if not isinstance(args[1],ivy_ast.Tuple) or len(args[0].args) != len(args[1].args):
                raise IvyError(self,"wrong number of values in assignment");
            for lhs,rhs in zip(args[0].args,args[1].args):
                code.append(AssignAction(lhs,rhs))
        elif isinstance(args[1],ivy_ast.Tuple):
            raise IvyError(self,"wrong number of values in assignment");
        else:
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
    ctx = ExprContext(lineno = self.lineno)
    with ctx:
        mas = [a.cmpl() for a in self.args[0].args]
    n = self.args[0].rep
#        print self.args
    res = CallAction(*([ivy_ast.Atom(n,mas)] + [a.cmpl() for a in self.args[1:]]))
    res.lineno = self.lineno
    ctx.code.append(res)
    res = ctx.extract()
#    print "compiled call action: {}".format(res)
    return res

CallAction.cmpl = compile_call


def compile_if_action(self):
    ctx = ExprContext(lineno = self.lineno)
    with ctx:
        cond = sortify_with_inference(self.args[0])
    rest = [a.compile() for a in self.args[1:]]
    ctx.code.append(self.clone([cond]+rest))
    res = ctx.extract()
    return res

IfAction.cmpl = compile_if_action

def compile_assert_action(self):
    ctx = ExprContext(lineno = self.lineno)
    with ctx:
        cond = sortify_with_inference(self.args[0])
    ctx.code.append(self.clone([cond]))
    res = ctx.extract()
    return res

AssertAction.cmpl = compile_assert_action
AssumeAction.cmpl = compile_assert_action

def compile_action_def(a,sig):
    sig = sig.copy()
    if not hasattr(a.args[1],'lineno'):
        print a
    assert hasattr(a.args[1],'lineno')
    with sig:
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
        res.formal_params = formals
        res.formal_returns = returns
        res.label = a.args[0].relname
        return res
    
    
class IvyDomainSetup(IvyDeclInterp):
    def __init__(self,domain):
        self.domain = domain
    def axiom(self,ax):
        self.domain.labeled_axioms.append(ax.compile())
    def schema(self,sch):
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
    def derived(self,df):
        try:
            rel = df.args[0]
            with ASTContext(rel):
              sym = add_symbol(rel.relname,get_relation_sort(self.domain.sig,rel.args,df.args[1]))
            df = sortify_with_inference(df)
            self.domain.all_relations.append((sym,len(rel.args)))
            self.domain.relations[sym] = len(rel.args)
            self.domain.concepts.append(df)
            self.domain.updates.append(DerivedUpdate(df))
        except ValueError:
            raise IvyError(df,"definition of derived relation must be a cube")
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
        sort = typedef.args[1].compile()
        self.domain.sig.sorts[typedef.args[0]] = sort
        for c in sort.defines(): # register the type's constructors
            sym = Symbol(c,sort)
            self.domain.functions[sym] = 0
            self.domain.sig.symbols[c] = sym
            self.domain.sig.constructors.add(sym)
    def interpret(self,thing):
        lhs,rhs = (a.rep for a in thing.args)
        sig = self.domain.sig
        interp = sig.interp
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
                return
        raise IvyUndefined(thing,lhs)
            
class IvyConjectureSetup(IvyDeclInterp):
    def __init__(self,domain):
        self.domain = domain
    def conjecture(self,ax):
        cax = ax.compile()
        self.domain.labeled_conjs.append(cax)

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
        if any(a.args for a in m.args):
            raise IvyError(m,"mixins may not have parameters")
        self.mod.mixins[m.args[1].relname].append(m)
    def _assert(self,a):
        with ASTContext(a):
            self.mod.assertions.append(type(a)(a.args[0],sortify_with_inference(a.args[1])))
    def isolate(self,iso):
        self.mod.isolates[iso.name()] = iso
    def export(self,exp):
        self.mod.exports.append(exp)
    def delegate(self,exp):
        self.mod.delegates.append(exp)
        
        
def ivy_new(filename = None):
#    d = Interp()
    if filename:
        f = open(filename,'r')
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
                res[a.defines()] = a.formal_returns
    return res

def ivy_compile(decls,mod=None,create_isolate=True,**kwargs):
    mod = mod or im.module
    with mod.sig:
        for name in decls.defined:
            mod.add_to_hierarchy(name)
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

        if create_isolate:
            iso.create_isolate(isolate.get(),mod,**kwargs)



def clear_rules(modname):
    import sys
    d = sys.modules[modname].__dict__
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
        f = open(fname,'r')
    except Exception:
        raise IvyError(None,"module {} not found in current directory".format(name))
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

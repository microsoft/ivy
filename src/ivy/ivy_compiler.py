#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_art import *
import pickle
from ivy_interp import Interp, eval_state_facts
from functools import partial
from ivy_concept_space import *
from ivy_parser import parse,ConstantDecl,ActionDef
from ivy_actions import DerivedUpdate, type_check_action, type_check, SymbolList, UpdatePattern, ActionContext, LocalAction, AssignAction, CallAction, Sequence
from ivy_utils import IvyError
import ivy_logic
import ivy_dafny_compiler as dc
import ivy_solver as slv
import ivy_logic_utils as lu
import string
import ivy_ast
import ivy_utils as iu
import ivy_actions as ia


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

# ast compilation

class ASTContext(object):
    """ ast compiling context, handles line numbers """
    def __init__(self,ast):
        self.ast = ast
    def __enter__(self):
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        if isinstance(exc_val,ivy_logic.Error):
#            assert False
            raise IvyError(self.ast,str(exc_val))
        if exc_type == IvyError and exc_val.lineno == None and hasattr(self.ast,'lineno'):
            exc_val.lineno = self.ast.lineno
        return False # don't block any exceptions

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
    def __init__(self,code,local_syms):
        self.code = code
        self.local_syms = local_syms
        self.name = 'expr_context'

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
                ress.append(res)
            expr_context.code.append(CallAction(*([ivy_ast.Atom(self.rep,args)]+ress)))
            return ivy_ast.Tuple(*ress)
        sort = find_sort(returns[0].sort)
        res = ivy_logic.Symbol('loc:'+str(len(expr_context.local_syms)),sort)
        expr_context.local_syms.append(res)
        expr_context.code.append(CallAction(ivy_ast.Atom(self.rep,args),res))
        return res
    return (ivy_logic.Equals if self.rep == '=' else ivy_logic.find_polymorphic_symbol(self.rep))(*args)
    

ivy_ast.App.cmpl = ivy_ast.Atom.cmpl = compile_app

ivy_ast.Variable.cmpl = lambda self: ivy_logic.Variable(self.rep,ivy_logic.find_sort(self.sort) if isinstance(self.sort,str) else self.sort)

ivy_ast.ConstantSort.cmpl = lambda self: ivy_logic.ConstantSort(self.rep)

ivy_ast.EnumeratedSort.cmpl = lambda self: ivy_logic.EnumeratedSort(self.extension)

SymbolList.cmpl = lambda self: self.clone([find_symbol(s) for s in self.symbols])

def cquant(q):
    return ivy_logic.ForAll if isinstance(q,ivy_ast.Forall) else ivy_logic.Exists

ivy_ast.Quantifier.cmpl = lambda self: cquant(self)([v.compile() for v in self.bounds],self.args[0].compile())

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
    rng = find_sort(v.sort) if hasattr(v,'sort') else ivy_logic.default_sort()
    with ASTContext(v):
      return add_symbol(v.rep,get_function_sort(sig,v.args,rng))
    

def compile_local(self):
    sig = ivy_logic.sig.copy()
    with sig:
        ls = self.args[0:-1]
        cls = [compile_const(v,sig) for v in ls]
        res = LocalAction(*(cls+[sortify(self.args[-1])]))
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
        if len(code) == 1:
            return code[0]
        return LocalAction(*(local_syms + [Sequence(*code)]))


AssignAction.cmpl = compile_assign

def compile_action_def(a,sig):
    sig = sig.copy()
    with sig:
        params = a.args[0].args
        pformals = [v.to_const('prm:') for v in params] 
        if params:
            subst = dict((x.rep,y) for x,y in zip(params,pformals))
#            print subst
            a = ivy_ast.substitute_ast(a,subst)
#            a = ivy_ast.subst_prefix_atoms_ast(a,subst,None,None)
#            print "after: %s" % (a)
        # convert object paramaters to arguments (object-orientation!)
        formals =  [compile_const(v,sig) for v in pformals + a.formal_params]
        returns = [compile_const(v,sig) for v in a.formal_returns]
#        print returns
        res = sortify(a.args[1])
        res.formal_params = formals
        res.formal_returns = returns
        return res
    
    
class IvyDomainSetup(IvyDeclInterp):
    def __init__(self,domain):
        self.domain = domain
    def axiom(self,ax):
#        print "axiom: {}".format(ax)
        self.domain.axioms.append(sortify_with_inference(ax))
    def conjecture(self,ax):
        fmla = sortify_with_inference(ax)
        try: 
            self.domain.conjs.append(formula_to_clauses(fmla))
        except ValueError:
            raise IvyError(ax,"conjecture must be a clause")

        # Make a conecpt space from the conjecture

        csname = 'conjecture:'+ str(len(self.domain.conjs))
        variables = list(lu.used_variables_ast(fmla))
        sort = ivy_logic.RelationSort([v.sort for v in variables])
        sym = ivy_logic.Symbol(csname,sort)
        space = NamedSpace(ivy_logic.Literal(0,fmla))
        self.domain.concept_spaces.append((sym(*variables),space))

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
        for x,y,z in zip([sig.sorts,sig.symbols],
                         [slv.sorts,[x for x in slv.relations] + [x for x in slv.functions]],
                         ['sort','symbol']):
            if lhs in x:
                if rhs not in y:
                    raise IvyError(thing,"{} not a native {}".format(rhs,z))
                interp[lhs] = rhs
                return
        raise IvyUndefined(thing,lhs)
            

class IvyARGSetup(IvyDeclInterp):
    def __init__(self,ag):
        self.ag = ag
    def individual(self,v):
        self.ag.pvars.append(sortify(v).rep)
    def init(self,s):
        s = sortify_with_inference(s)
#        print "s:{}".format(s)
        type_check(self.ag.domain,s)
        c = formula_to_clauses_tseitin(s)
        if not c:
            raise IvyError(ax,"initial condition must be a clause")
        self.ag.init_cond = and_clauses(self.ag.init_cond,c)
    def action(self,a):
        self.ag.actions[a.args[0].relname] = compile_action_def(a,self.ag.domain.sig)
        self.ag.public_actions.add(a.args[0].relname)
    def state(self,a):
        self.ag.predicates[a.args[0].relname] = a.args[1]
    def mixin(self,m):
        if any(a.args for a in m.args):
            raise IvyError(m,"mixins may not have parameters")
        self.ag.mixins[m.args[1].relname].append(m)
    def _assert(self,a):
        with ASTContext(a):
            self.ag.assertions.append(type(a)(a.args[0],sortify_with_inference(a.args[1])))
    def isolate(self,iso):
        self.ag.isolates[iso.name()] = iso
    def export(self,exp):
        self.ag.exports.append(exp)
    def delegate(self,exp):
        self.ag.delegates.append(exp)
        
        
def ivy_new(filename = None):
    d = Interp()
    ag = AnalysisGraph(d,[])
    if filename:
        f = open(filename,'r')
        if not f:
            raise IvyError(None,"not found: %s" % filename)
        ivy_load_file(f,ag)
    return ag


def lookup_action(ast,ag,name):
    if name not in ag.actions:
        raise IvyError(ast,"action {} undefined".format(name))
    return ag.actions[name]

isolate = iu.Parameter("isolate")

def add_mixins(ag,actname,action2,assert_to_assume=False,use_mixin=lambda:True,mod_mixin=lambda m:m):
    # TODO: mixins need to be in a fixed order
    res = action2
    for mixin in ag.mixins[actname]:
        mixin_name = mixin.args[0].relname
        action1 = lookup_action(mixin,ag,mixin_name)
        if use_mixin(mixin_name):
            if assert_to_assume:
                action1 = action1.assert_to_assume()
            action1 = mod_mixin(action1)
        res = ivy_actions.mixin_before(mixin,action1,res)
    return res

def summarize_action(action):
    res = ivy_actions.Sequence()
    res.formal_params = action.formal_params
    res.formal_returns = action.formal_returns
    return res

# Delegation of assertions

#    For purposes of compositional proofs, he precondition of an
#    action can be treated as a requirement on the called or as
#    a guarantee of the action when called. In the former case, we say
#    the action *delegates* its precondition to the caller. 

#    Normally, only preconditions equivalent to true can be guaranteed
#    by the action. However, this is not the case in the presense of
#    "before" mixins, since the precondition of the action may be
#    implied by the predondition of the mixin.

#    The default convention is that action *do not* delegate to their
#    callers, but mixins *do*. This gives a way to separated what is
#    guaranteed by the caller from what is guaranteed by the callee.

#    This also means that "opaque" actions can be summarized (see
#    below) since their preconditions must be true. 


# Isolation of components. 

# In each isolate, each component of the hierarchy has one of three
# possible roles:

# 1) Verified. Every assertion delegated to this component is checked.

# 2) Present. Assertions delegated to this component are not checked,
# but the component's actions are not summarized.

# 3) Opaque. The state of this component is abstracted. Its actions are
# summarized.

# Rules for isolation.

# 1) Calls from non-opaque to opaque components.

#    a) are allowed only if the called action does not delegate its
#    assertions to the caller. this is because it is not possible to
#    verify the precondition of the action when its state components
#    are abstracted.

#    b) are allowed only if the called action does not transitively
#    call any non-opaque action. this is because we cannot model the
#    effect of such a call.

#    c) are summarized by null actions

# Conditions (a) and (b) are needed to assume that (c) is sound

# 2) Globally exported actions of opaque components.

#     These are summarized by a single globally exported action that
#     non-deterministically calls all non-opaque actions that are
#     transitively called by a globally exported opaque
#     action. Assertions delegated to this summary action are not
#     checked.

# Rules for the collection of isolates

#     Each assertion must be checked in all possible calling contexts,
#     including external.

#     To guarantee this, we require the following:

#     1) Each non-delegating action must have the verified role in
#     some isolate.

#     2) Each *call* to a delegating action must have the verified role
#     in some isolate.

#     This means that a delegating action that is exported but not
#     internally called will not have its assertions checked. 

# Rules for global export of actions

#     The external version of an action is exported from the isolate if:

#     1) The action is originally globally exported and it is not opaque

#     2) The action is not opaque and is called from any opaque action



def startswith_some(s,prefixes):
    return any(s.startswith(name+iu.ivy_compose_character) for name in prefixes)

def isolate_component(ag,isolate_name):
    domain = ag.domain
    if isolate_name not in ag.isolates:
        raise IvyError(None,"undefined isolate: {}".format(isolate_name))
    isolate = ag.isolates[isolate_name]
    verified = set(a.relname for a in isolate.verified())
    present = set(a.relname for a in isolate.present())
    present.update(verified)
    delegates = set(s.delegated() for s in ag.delegates)
    for name in present:
        if name not in domain.hierarchy:
            raise IvyError(None,"{} is not a module instance".format(name))
    
    new_actions = {}
    use_mixin = lambda name: startswith_some(name,present)
    mod_mixin = lambda m: m if startswith_some(name,verified) else m.prefix_calls('ext:')
    for actname,action in ag.actions.iteritems():
        ver = startswith_some(actname,verified)
        pre = startswith_some(actname,present)
        if pre: 
            if not ver:
                ext_action = action.assert_to_assume().prefix_calls('ext:')
                if actname in delegates:
                    int_action = action.prefix_calls('ext:')
                else:
                    int_action = ext_action
            else:
                int_action = ext_action = action
            # internal version of the action has mixins checked
            new_actions[actname] = add_mixins(ag,actname,int_action,False,use_mixin,mod_mixin)
            # external version of the action assumes mixins are ok
            new_action = add_mixins(ag,actname,ext_action,True,use_mixin,mod_mixin)
            new_actions['ext:'+actname] = new_action
            # TODO: external version is public if action public *or* called from opaque
            # public_actions.add('ext:'+actname)
        else:
            # TODO: here must check that summarized action does not
            # have a call dependency on the isolated module
            action = summarize_action(action)
            new_actions[actname] = add_mixins(ag,actname,action,False,use_mixin,mod_mixin)
            new_actions['ext:'+actname] = add_mixins(ag,actname,action,True,use_mixin,mod_mixin)


    # figure out what is exported:
    exported = set()
    for e in ag.exports:
        if not e.scope() and startswith_some(e.exported(),present): # global scope
            exported.add('ext:' + e.exported())
    for actname,action in ag.actions.iteritems():
        if not startswith_some(actname,present):
            for c in action.iter_calls():
                if startswith_some(c,present):
                    exported.add('ext:' + c)
#    print "exported: {}".format(exported)

    ag.public_actions = exported
    ag.actions = new_actions

    ext_act = ia.ChoiceAction(*[ag.actions[x] for x in sorted(exported)])
    exported.add('ext');
    ag.actions['ext'] = ext_act;

#    print "actions:"
#    for x,y in ag.actions.iteritems():
#        print iu.pretty("action {} = {}".format(x,y))
    
# collect actions in case of forward reference
def collect_actions(decls):
    res = {}
    for d in decls:
        if d.name() == 'action':
            for a in d.args:
                res[a.defines()] = a.formal_returns
    return res

def ivy_compile(ag,decls):
    ag.actions = {}
    ag.predicates = {}
    ag.assertions = []
    ag.mixins = defaultdict(list)
    ag.domain.clear()
    ag.public_actions = set()
    ag.isolates = {}
    ag.exports = []
    ag.delegates = []
    with ag.domain.sig:
        ag.init_cond = true_clauses()
        for name in decls.defined:
            ag.domain.add_to_hierarchy(name)
        with TopContext(collect_actions(decls.decls)):
            IvyDomainSetup(ag.domain)(decls)
            IvyARGSetup(ag)(decls)
        ag.domain.macros = decls.macros
        if not ag.states:
            ac = ag.context
            with ac:
                if ag.predicates:
                    if not ag.init_cond.is_true():
                        raise IvyError(None,"init and state declarations are not compatible");
                    for n,p in ag.predicates.iteritems():
                        s = eval_state_facts(p)
                        if s is not None:
                            s.label = n
                else:
                    ac.new_state(ag.init_cond)
        ag.domain.type_check()
        # try instantiating all the actions to type check them
        for name,action in ag.actions.iteritems():
#            print "checking: {} = {}".format(name,action)
            type_check_action(action,ag.domain,ag.states[0].in_scope)
        iso = isolate.get()
        if iso:
            isolate_component(ag,iso)
        else:
            # apply all the mixins in no particular order
            for name,mixins in ag.mixins.iteritems():
                for mixin in mixins:
                    action1,action2 = (lookup_action(mixin,ag,a.relname) for a in mixin.args)
                    mixed = ivy_actions.mixin_before(mixin,action1,action2)
                    ag.actions[mixin.args[1].relname] = mixed
            # find the globally exported actions (all if none specified, for compat)
            if ag.exports:
                ag.public_actions = set()
                for e in ag.exports:
                    if not e.scope(): # global export
                        ag.public_actions.add(e.exported())
            else:
                for a in ag.actions:
                    ag.public_actions.add(a)

            print "actions:"
            for x,y in ag.actions.iteritems():
                print iu.pretty("action {} = {}".format(x,y))


    ivy_logic.sig = ag.domain.sig # TODO: make this an environment

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
        raise IvyError(None,'file must begin with "#lang ivyN.N" or "//lang dafnyN.N"') 
    return decls

def import_module(name):
    f = open(name + '.ivy','r')
    if not f:
        raise IvyError(None,"module {} not found in current directory".format(name))
    return read_module(f,nested=True)

def ivy_load_file(f,ag):
    decls = read_module(f)
    ivy_compile(ag,decls)


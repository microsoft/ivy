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
import ivy_alpha
import ivy_module as im

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
            if isinstance(self.ast.lineno,tuple):
                exc_val.filename, exc_val.lineno = self.ast.lineno
            else:
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
#            print subst
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
        return res
    
    
class IvyDomainSetup(IvyDeclInterp):
    def __init__(self,domain):
        self.domain = domain
    def axiom(self,ax):
        print "axiom: {}".format(ax)
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
    def __init__(self,ag):
        self.ag = ag
    def individual(self,v):
        self.ag.pvars.append(sortify(v).rep)
    def init(self,s):
        la = s.compile()
        self.ag.domain.labeled_inits.append(la)
#        s = sortify_with_inference(s)
#        print "s:{}".format(s)
#        type_check(self.ag.domain,s)
#         c = formula_to_clauses_tseitin(s)
#        if not c:
#            raise IvyError(ax,"initial condition must be a clause")
        im.module.init_cond = and_clauses(im.module.init_cond,formula_to_clauses(la.formula))
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
#    d = Interp()
    ag = AnalysisGraph()
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

def add_mixins(ag,actname,action2,assert_to_assume=lambda m:False,use_mixin=lambda:True,mod_mixin=lambda m:m):
    # TODO: mixins need to be in a fixed order
    assert hasattr(action2,'lineno'), action2
    assert hasattr(action2,'formal_params'), action2
    res = action2
    for mixin in ag.mixins[actname]:
        mixin_name = mixin.args[0].relname
        action1 = lookup_action(mixin,ag,mixin_name)
        assert hasattr(action1,'lineno')
        assert hasattr(action1,'formal_params'), action1
        if use_mixin(mixin_name):
            if assert_to_assume(mixin):
                action1 = action1.assert_to_assume()
                assert hasattr(action1,'lineno')
                assert hasattr(action1,'formal_params'), action1
            action1 = mod_mixin(action1)
            assert hasattr(action1,'lineno')
            assert hasattr(action1,'formal_params'), action1
            res = ivy_actions.apply_mixin(mixin,action1,res)
    return res

def summarize_action(action):
    res = ivy_actions.Sequence()
    res.lineno = action.lineno
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

create_big_action = True

def set_create_big_action(t):
    global create_big_action
    create_big_action = t

interpret_all_sorts = False

def set_interpret_all_sorts(t):
    global interpret_all_sorts
    interpret_all_sorts = t

def startswith_some(s,prefixes):
    return any(s.startswith(name+iu.ivy_compose_character) for name in prefixes)

def startswith_eq_some(s,prefixes):
    return any(s.startswith(name+iu.ivy_compose_character) or s == name for name in prefixes)

def test_startswith_some(name,present):
    iu.dbg('name','present')
    res = startswith_some(name,present)
    iu.dbg('res')
    return res

def isolate_component(ag,isolate_name):
    domain = ag.domain
    if isolate_name not in ag.isolates:
        raise IvyError(None,"undefined isolate: {}".format(isolate_name))
    isolate = ag.isolates[isolate_name]
    verified = set(a.relname for a in isolate.verified())
    present = set(a.relname for a in isolate.present())
    present.update(verified)
    if not interpret_all_sorts:
        for type_name in list(ivy_logic.sig.interp):
            if not startswith_eq_some(type_name,present):
                del ivy_logic.sig.interp[type_name]
    print "interp: {}".format(ivy_logic.sig.interp) 
    delegates = set(s.delegated() for s in ag.delegates)
    for name in present:
        if name not in domain.hierarchy and name not in ivy_logic.sig.sorts:
            raise IvyError(None,"{} is not a module instance".format(name))
    
    new_actions = {}
    iu.dbg('present')
    use_mixin = lambda name: test_startswith_some(name,present)
    mod_mixin = lambda m: m if startswith_some(name,verified) else m.prefix_calls('ext:')
    all_mixins = lambda m: True
    no_mixins = lambda m: False
    after_mixins = lambda m: isinstance(m,ivy_ast.MixinAfterDef)
    before_mixins = lambda m: isinstance(m,ivy_ast.MixinBeforeDef)
    for actname,action in ag.actions.iteritems():
        ver = startswith_some(actname,verified)
        pre = startswith_some(actname,present)
        if pre: 
            if not ver:
                assert hasattr(action,'lineno')
                assert hasattr(action,'formal_params'), action
                ext_action = action.assert_to_assume().prefix_calls('ext:')
                assert hasattr(ext_action,'lineno')
                assert hasattr(ext_action,'formal_params'), ext_action
                if actname in delegates:
                    int_action = action.prefix_calls('ext:')
                    assert hasattr(int_action,'lineno')
                    assert hasattr(int_action,'formal_params'), int_action
                else:
                    int_action = ext_action
                    assert hasattr(int_action,'lineno')
                    assert hasattr(int_action,'formal_params'), int_action
            else:
                int_action = ext_action = action
                assert hasattr(int_action,'lineno')
                assert hasattr(int_action,'formal_params'), int_action
            # internal version of the action has mixins checked
            new_actions[actname] = add_mixins(ag,actname,int_action,no_mixins,use_mixin,lambda m:m)
            # external version of the action assumes mixins are ok
            new_action = add_mixins(ag,actname,ext_action,before_mixins,use_mixin,mod_mixin)
            new_actions['ext:'+actname] = new_action
            # TODO: external version is public if action public *or* called from opaque
            # public_actions.add('ext:'+actname)
        else:
            # TODO: here must check that summarized action does not
            # have a call dependency on the isolated module
            action = summarize_action(action)
            new_actions[actname] = add_mixins(ag,actname,action,after_mixins,use_mixin,mod_mixin)
            new_actions['ext:'+actname] = add_mixins(ag,actname,action,all_mixins,use_mixin,mod_mixin)


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

    if create_big_action:
        ext_act = ia.ChoiceAction(*[new_actions[x] for x in sorted(exported)])
        exported.add('ext');
        new_actions['ext'] = ext_act;


    # We allow objects to reference any symbols in global scope, and
    # we keep axioms declared in global scope. Because of the way
    # thigs are named, this gives a different condition for keeping
    # symbols and axioms (in particular, axioms in global scope have
    # label None). Maybe this needs to be cleaned up.

    keep_sym = lambda name: (iu.ivy_compose_character not in name
                            or startswith_eq_some(name,present))
    
    keep_ax = lambda name: (name is None or startswith_eq_some(name,present))

    # filter the conjectures

    new_conjs = [c for c in domain.labeled_conjs if keep_ax(str(c.label))]
    del domain.labeled_conjs[:]
    domain.labeled_conjs.extend(new_conjs)

    print "conjectures:"
    for c in domain.labeled_conjs:
        print c

    # filter the signature

    new_syms = set(s for s in domain.sig.symbols if keep_sym(s))
    for s in list(domain.sig.symbols):
        if s not in new_syms:
            del domain.sig.symbols[s]

    iu.dbg('domain.sig.symbols')

    # filter the inits

    for thing in domain.labeled_inits:
        print thing
    print present

    new_inits = [c for c in domain.labeled_inits if keep_ax(str(c.label))]
    for thing in new_inits:
        print thing
    del domain.labeled_inits[:]
    domain.labeled_inits.extend(new_inits)
    
    init_cond = ivy_logic.And(*(lf.formula for lf in new_inits))
    im.module.init_cond = formula_to_clauses(init_cond)

    iu.dbg('init_cond')

    ag.public_actions.clear()
    ag.public_actions.update(exported)
    ag.actions.clear()
    ag.actions.update(new_actions)

    print "actions:"
    for x,y in ag.actions.iteritems():
        print iu.pretty("action {} = {}".format(x,y))
    
# collect actions in case of forward reference
def collect_actions(decls):
    res = {}
    for d in decls:
        if d.name() == 'action':
            for a in d.args:
                res[a.defines()] = a.formal_returns
    return res

def ivy_compile(ag,decls):
    with ag.domain.sig:
        for name in decls.defined:
            ag.domain.add_to_hierarchy(name)
        with TopContext(collect_actions(decls.decls)):
            IvyDomainSetup(ag.domain)(decls)
            IvyConjectureSetup(ag.domain)(decls)
            IvyARGSetup(ag)(decls)
        ag.domain.macros = decls.macros
        # progress properties are not state symbols -- remove from sig
        for p in ag.domain.progress:
            remove_symbol(p.defines())
        ag.domain.type_check()
        # try instantiating all the actions to type check them
        for name,action in ag.actions.iteritems():
#            print "checking: {} = {}".format(name,action)
            type_check_action(action,ag.domain)
            if not hasattr(action,'lineno'):
                print "no lineno: {}".format(name)
            assert hasattr(action,'formal_params'), action

        # check all mixin declarations

        for name,mixins in ag.mixins.iteritems():
            for mixin in mixins:
                with ASTContext(mixins):
                    action1,action2 = (lookup_action(mixin,ag,a.relname) for a in mixin.args)

        # HACK: code beyond here really does not belong in compile




        # Construct an isolate

        iso = isolate.get()
        if iso:
            isolate_component(ag,iso)
        else:
            # apply all the mixins in no particular order
            for name,mixins in ag.mixins.iteritems():
                for mixin in mixins:
                    action1,action2 = (lookup_action(mixin,ag,a.relname) for a in mixin.args)
                    mixed = ivy_actions.apply_mixin(mixin,action1,action2)
                    ag.actions[mixin.args[1].relname] = mixed
            # find the globally exported actions (all if none specified, for compat)
            if ag.exports:
                ag.public_actions.clear()
                for e in ag.exports:
                    if not e.scope(): # global export
                        ag.public_actions.add(e.exported())
            else:
                for a in ag.actions:
                    ag.public_actions.add(a)

        # Check native interpretations of symbols

        slv.check_compat()

        # Make concept spaces from the conjecture

        for i,cax in enumerate(ag.domain.labeled_conjs):
            fmla = cax.formula
            csname = 'conjecture:'+ str(i)
            variables = list(lu.used_variables_ast(fmla))
            sort = ivy_logic.RelationSort([v.sort for v in variables])
            sym = ivy_logic.Symbol(csname,sort)
            space = NamedSpace(ivy_logic.Literal(0,fmla))
            ag.domain.concept_spaces.append((sym(*variables),space))

            # print "actions:"
            # for x,y in ag.actions.iteritems():
            #     print iu.pretty("action {} = {}".format(x,y))
        if not ag.states:
            ac = ag.context
            with ac:
                if ag.predicates:
                    if not im.module.init_cond.is_true():
                        raise IvyError(None,"init and state declarations are not compatible");
                    for n,p in ag.predicates.iteritems():
                        s = eval_state_facts(p)
                        if s is not None:
                            s.label = n
                else:
                    ag.add_initial_state(im.module.init_cond,ivy_alpha.alpha)

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

def ivy_load_file(f,ag):
    decls = read_module(f)
    ivy_compile(ag,decls)


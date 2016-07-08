#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

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
import ivy_concept_space as ics
from ivy_ast import ASTContext
from collections import defaultdict

show_compiled = iu.BooleanParameter("show_compiled",False)

def lookup_action(ast,mod,name):
    if name not in mod.actions:
        raise iu.IvyError(ast,"action {} undefined".format(name))
    return mod.actions[name]

def add_mixins(mod,actname,action2,assert_to_assume=lambda m:False,use_mixin=lambda:True,mod_mixin=lambda m:m):
    # TODO: mixins need to be in a fixed order
    assert hasattr(action2,'lineno'), action2
    assert hasattr(action2,'formal_params'), action2
    res = action2
    for mixin in mod.mixins[actname]:
        mixin_name = mixin.args[0].relname
        action1 = lookup_action(mixin,mod,mixin_name)
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
            res = ia.apply_mixin(mixin,action1,res)
    return res

def summarize_action(action):
    res = ia.Sequence()
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




interpret_all_sorts = False

def set_interpret_all_sorts(t):
    global interpret_all_sorts
    interpret_all_sorts = t

#def startswith_some(s,prefixes):
#    return any(s.startswith(name+iu.ivy_compose_character) for name in prefixes)

def startswith_some(s,prefixes,mod):
    if s in mod.privates:
        return False
    parts = s.rsplit(iu.ivy_compose_character,1)
    return len(parts)==2 and startswith_eq_some(parts[0],prefixes,mod)

#def startswith_eq_some(s,prefixes):
#    return any(s.startswith(name+iu.ivy_compose_character) or s == name for name in prefixes)

def startswith_eq_some(s,prefixes,mod):
    if s in prefixes:
        return True
    return startswith_some(s,prefixes,mod)

def strip_map_lookup(name,strip_map,with_dot=True):
    for prefix in strip_map:
        if name.startswith(prefix+(iu.ivy_compose_character if with_dot else '')):
            return strip_map[prefix]
    return []

def get_strip_params(name,args,strip_map,strip_binding,ast):
    strip_params = strip_map_lookup(name,strip_map)
    if not(len(args) >= len(strip_params)):
        raise iu.IvyError(ast,"cannot strip isolate parameters from {}".format(name))
    for sp,ap in zip(strip_params,args):
        if ap not in strip_binding or strip_binding[ap] != sp:
            raise iu.IvyError(ast,"cannot strip parameter {} from {}".format(ap,name))
    return strip_params

def strip_sort(sort,strip_params):
    dom = list(sort.dom[len(strip_params):])
    if dom or sort.is_relational():
        return ivy_logic.FunctionSort(*(dom+[sort.rng]))
    return sort.rng

def strip_action(ast,strip_map,strip_binding):
    if isinstance(ast,ia.CallAction):
        name = ast.args[0].rep
        args = [strip_action(arg,strip_map,strip_binding) for arg in ast.args[0].args]
        strip_params = get_strip_params(name,ast.args[0].args,strip_map,strip_binding,ast)
        call = ast.args[0].clone(args[len(strip_params):])
        return ast.clone([call]+[strip_action(arg,strip_map,strip_binding) for arg in ast.args[1:]])
    if (ivy_logic.is_constant(ast) or ivy_logic.is_variable(ast)) and ast in strip_binding:
        sname = strip_binding[ast]
        if sname not in ivy_logic.sig.symbols:
            ivy_logic.add_symbol(sname,ast.sort)
        return ivy_logic.Symbol(sname,ast.sort)
    args = [strip_action(arg,strip_map,strip_binding) for arg in ast.args]
    if ivy_logic.is_app(ast):
        name = ast.rep.name
        strip_params = get_strip_params(name,ast.args,strip_map,strip_binding,ast)
        if strip_params:
            new_sort = strip_sort(ast.rep.sort,strip_params)
            new_args = args[len(strip_params):]
            new_symbol = ivy_logic.Symbol(name,new_sort)
            return new_symbol(*new_args)
    return ast.clone(args)
                
def get_strip_binding(ast,strip_map,strip_binding):
    [get_strip_binding(arg,strip_map,strip_binding) for arg in ast.args]
    if ivy_logic.is_app(ast):
        name = ast.rep.name
        strip_params = strip_map_lookup(name,strip_map)
        if not(len(ast.args) >= len(strip_params)):
            raise iu.IvyError(action,"cannot strip isolate parameters from {}",name)
        for sp,ap in zip(strip_params,ast.args):
            if ap in strip_binding and strip_binding[ap] != sp:
                raise iu.IvyError(action,"cannot strip parameter {} from {}",ap,name)
            strip_binding[ap] = sp
                
def strip_labeled_fmla(lfmla,strip_map):
    fmla = lfmla.formula
    strip_binding = {}
    get_strip_binding(fmla,strip_map,strip_binding)
    fmla = strip_action(fmla,strip_map,strip_binding)
    lbl = lfmla.label
    if lbl:
        lbl = lbl.clone(lbl.args[len(strip_map_lookup(lbl.rep,strip_map,with_dot=False)):])
    return lfmla.clone([lbl,fmla])
    
def strip_labeled_fmlas(lfmlas,strip_map):
    new_lfmlas = [strip_labeled_fmla(f,strip_map) for f in lfmlas]
    del lfmlas[:]
    lfmlas.extend(new_lfmlas)
    
def strip_isolate(mod,isolate):
    strip_map = {}
    for atom in isolate.verified() + isolate.present():
        name = atom.relname
        if atom.args:
            if not all(isinstance(v,ivy_ast.App) and not v.args for v in atom.args):
                raise iu.IvyError(atom,"bad isolate parameter")
            for a in atom.args:
                if a.rep in ivy_logic.sig.symbols:
                    raise iu.IvyError(a,"isolate parameter redefines {}",a.rep)
            strip_map[name] = [a.rep for a in atom.args]
    # strip the actions
    new_actions = {}
    for name,action in mod.actions.iteritems():
        strip_params = strip_map_lookup(name[4:] if name.startswith('ext:') else name,strip_map)
        if not(len(action.formal_params) >= len(strip_params)):
            raise iu.IvyError(action,"cannot strip isolate parameters from {}".format(name))
        strip_binding = dict(zip(action.formal_params,strip_params))
        new_action = strip_action(action,strip_map,strip_binding)
        new_action.formal_params = action.formal_params[len(strip_params):]
        new_action.formal_returns = action.formal_returns
        new_actions[name] = new_action
    mod.actions.clear()
    mod.actions.update(new_actions)

    # strip the axioms and conjectures
    for x in [mod.labeled_axioms,mod.labeled_conjs,mod.labeled_inits]:
        strip_labeled_fmlas(x,strip_map)
    # strip the signature
    new_symbols = {}
    for name,sym in ivy_logic.sig.symbols.iteritems():
        strip_params = strip_map_lookup(name,strip_map)
        if strip_params:
            if not (len(sym.sort.dom) >= len(strip_params)):
                raise iu.IvyError(None,"cannot strip isolate parameters from {}",name)
            new_sort = strip_sort(sym.sort,strip_params)
            sym =  ivy_logic.Symbol(name,new_sort)
        new_symbols[name] = sym
    ivy_logic.sig.symbols.clear()
    ivy_logic.sig.symbols.update(new_symbols)


def isolate_component(mod,isolate_name):
    if isolate_name not in mod.isolates:
        raise iu.IvyError(None,"undefined isolate: {}".format(isolate_name))
    isolate = mod.isolates[isolate_name]
    verified = set(a.relname for a in isolate.verified())
    present = set(a.relname for a in isolate.present())
    present.update(verified)
    if not interpret_all_sorts:
        for type_name in list(ivy_logic.sig.interp):
            if not startswith_eq_some(type_name,present,mod):
                del ivy_logic.sig.interp[type_name]
    delegates = set(s.delegated() for s in mod.delegates if not s.delegee())
    delegated_to = dict((s.delegated(),s.delegee()) for s in mod.delegates if s.delegee())
    derived = set(df.args[0].func.name for df in mod.concepts)
    for name in present:
        if (name not in mod.hierarchy
            and name not in ivy_logic.sig.sorts
            and name not in derived
            and name not in ivy_logic.sig.interp):
            raise iu.IvyError(None,"{} is not a module instance, sort, definition, or interpreted function".format(name))
    
    new_actions = {}
    use_mixin = lambda name: startswith_some(name,present,mod)
    mod_mixin = lambda m: m if startswith_some(name,verified,mod) else m.prefix_calls('ext:')
    all_mixins = lambda m: True
    no_mixins = lambda m: False
    after_mixins = lambda m: isinstance(m,ivy_ast.MixinAfterDef)
    before_mixins = lambda m: isinstance(m,ivy_ast.MixinBeforeDef)
    delegated_to_verified = lambda n: n in delegated_to and startswith_eq_some(delegated_to[n],verified,mod)
    ext_assumes = lambda m: before_mixins(m) and not delegated_to_verified(m.mixer())
    for actname,action in mod.actions.iteritems():
        ver = startswith_some(actname,verified,mod)
        pre = startswith_some(actname,present,mod)
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
            new_actions[actname] = add_mixins(mod,actname,int_action,no_mixins,use_mixin,lambda m:m)
            # external version of the action assumes mixins are ok, unless they
            # are delegated to a currently verified object
            new_action = add_mixins(mod,actname,ext_action,ext_assumes,use_mixin,mod_mixin)
            new_actions['ext:'+actname] = new_action
            # TODO: external version is public if action public *or* called from opaque
            # public_actions.add('ext:'+actname)
        else:
            # TODO: here must check that summarized action does not
            # have a call dependency on the isolated module
            action = summarize_action(action)
            new_actions[actname] = add_mixins(mod,actname,action,after_mixins,use_mixin,mod_mixin)
            new_actions['ext:'+actname] = add_mixins(mod,actname,action,all_mixins,use_mixin,mod_mixin)


    # figure out what is exported:
    exported = set()
    for e in mod.exports:
        if not e.scope() and startswith_some(e.exported(),present,mod): # global scope
            exported.add('ext:' + e.exported())
    for actname,action in mod.actions.iteritems():
        if not startswith_some(actname,present,mod):
            for c in action.iter_calls():
                if startswith_some(c,present,mod):
                    exported.add('ext:' + c)
#    print "exported: {}".format(exported)


    # We allow objects to reference any symbols in global scope, and
    # we keep axioms declared in global scope. Because of the way
    # thigs are named, this gives a different condition for keeping
    # symbols and axioms (in particular, axioms in global scope have
    # label None). Maybe this needs to be cleaned up.

    keep_sym = lambda name: (iu.ivy_compose_character not in name
                            or startswith_eq_some(name,present))
    
    keep_ax = lambda name: (name is None or startswith_eq_some(name.rep,present,mod))


    # filter the conjectures

    new_conjs = [c for c in mod.labeled_conjs if keep_ax(c.label)]
    del mod.labeled_conjs[:]
    mod.labeled_conjs.extend(new_conjs)

    # filter the inits

    new_inits = [c for c in mod.labeled_inits if keep_ax(c.label)]
    del mod.labeled_inits[:]
    mod.labeled_inits.extend(new_inits)
    
    # filter the axioms
    mod.labeled_axioms = [a for a in mod.labeled_axioms if keep_ax(a.label)]

    # filter definitions
    mod.concepts = [c for c in mod.concepts if startswith_eq_some(c.args[0].func.name,present,mod)]

    mod.public_actions.clear()
    mod.public_actions.update(exported)
    mod.actions.clear()
    mod.actions.update(new_actions)

    # filter the signature
    # keep only the symbols referenced in the remaining
    # formulas

    asts = []
    for x in [mod.labeled_axioms,mod.labeled_inits,mod.labeled_conjs]:
        asts += [y.formula for y in x]
    asts += mod.concepts
    asts += [action for action in mod.actions.values()]
    sym_names = set(x.name for x in lu.used_symbols_asts(asts))
    old_syms = list(mod.sig.symbols)
    for sym in old_syms:
        if sym not in sym_names:
            del mod.sig.symbols[sym]

    # TODO: need a better way to filter signature
    # new_syms = set(s for s in mod.sig.symbols if keep_sym(s))
    # for s in list(mod.sig.symbols):
    #     if s not in new_syms:
    #         del mod.sig.symbols[s]



    # strip the isolate parameters

    strip_isolate(mod,isolate)

    # collect the initial condition

    init_cond = ivy_logic.And(*(lf.formula for lf in mod.labeled_inits))
    mod.init_cond = lu.formula_to_clauses(init_cond)



class SortOrder(object):
    def __init__(self,arcs):
        self.arcs = arcs
    def __call__(self,x,y):
        x = x.args[0].relname
        y = y.args[0].relname
        res =  -1 if y in self.arcs[x] else 1 if x in self.arcs[y] else 0   
        return res

# class SortOrder(object):
#     def __init__(self,arcs):
#         self.arcs = arcs
#     def __call__(self,x,y):
#         x = x.args[0].relname
#         y = y.args[0].relname
#         res =  -1 if y in self.arcs[x] else 1 if x in self.arcs[y] else 0   
#         return res


def get_mixin_order(iso,mod):
    arcs = [(rdf.args[0].relname,rdf.args[1].relname) for rdf in mod.mixord]
    actions = mod.mixins.keys()
    for action in actions:
        mixins = mod.mixins[action]
        mixers = iu.topological_sort(list(set(m.mixer() for m in mixins)),arcs)
        keymap = dict((x,y) for y,x in enumerate(mixers))
        key = lambda m: keymap[m.mixer()]
        before = sorted([m for m in mixins if isinstance(m,ivy_ast.MixinBeforeDef)],key=key)
        after = sorted([m for m in mixins if isinstance(m,ivy_ast.MixinAfterDef)],key=key)
#        order = SortOrder(arcs)
#        before = sorted([m for m in mixins if isinstance(m,ivy_ast.MixinBeforeDef)],order)
#        after = sorted([m for m in mixins if isinstance(m,ivy_ast.MixinAfterDef)],order)
        before.reverse() # add the before mixins in reverse order
        mixins = before + after
#        print 'mixin order for action {}:'
#        for m in mixins:
#            print m.args[0]
        mod.mixins[action] = mixins
        

ext_action = iu.Parameter("ext",None)

def hide_action_params(action):
    params = action.formal_params + action.formal_returns
    res = ia.LocalAction(*(params + [action]))
    return res

def labeled_fmlas_to_str(kwd,lfmlas):
    res = ''
    for f in lfmlas:
        res += kwd + ' '
        if f.label:
            res += '[{}] '.format(f.label)
        res += str(f.formula) + '\n'
    return res

def create_isolate(iso,mod = None,**kwargs):

        mod = mod or im.module

        # check all mixin declarations

        for name,mixins in mod.mixins.iteritems():
            for mixin in mixins:
                with ASTContext(mixins):
                    action1,action2 = (lookup_action(mixin,mod,a.relname) for a in mixin.args)

        # check all the delagate declarations

        for dl in mod.delegates:
            lookup_action(dl.args[0],mod,dl.delegated())
            if dl.delegee() and dl.delegee() not in mod.hierarchy:
                raise iu.IvyError(dl.args[1],"{} is not a module instance".format(name))

        # Determine the mixin order (as a side effect on module.mixins)

        get_mixin_order(iso,mod)

        # Construct an isolate

        if iso:
            isolate_component(mod,iso)
        else:
            if mod.isolates:
                raise iu.IvyError(None,'no isolate specified on command line')
            # apply all the mixins in no particular order
            for name,mixins in mod.mixins.iteritems():
                for mixin in mixins:
                    action1,action2 = (lookup_action(mixin,mod,a.relname) for a in mixin.args)
                    mixed = ia.apply_mixin(mixin,action1,action2)
                    mod.actions[mixin.args[1].relname] = mixed
            # find the globally exported actions (all if none specified, for compat)
            if mod.exports:
                mod.public_actions.clear()
                for e in mod.exports:
                    if not e.scope(): # global export
                        mod.public_actions.add(e.exported())
            else:
                for a in mod.actions:
                    mod.public_actions.add(a)

        # Create one big external action if requested


        ext = kwargs['ext'] if 'ext' in kwargs else ext_action.get()
        if ext is not None:
            ext_acts = [mod.actions[x] for x in sorted(mod.public_actions)]
            ext_act = ia.EnvAction(*ext_acts)
            mod.public_actions.add(ext);
            mod.actions[ext] = ext_act;

        # Check native interpretations of symbols

        slv.check_compat()

        # Make concept spaces from the conjecture

        for i,cax in enumerate(mod.labeled_conjs):
            fmla = cax.formula
            csname = 'conjecture:'+ str(i)
            variables = list(lu.used_variables_ast(fmla))
            sort = ivy_logic.RelationSort([v.sort for v in variables])
            sym = ivy_logic.Symbol(csname,sort)
            space = ics.NamedSpace(ivy_logic.Literal(0,fmla))
            mod.concept_spaces.append((sym(*variables),space))

        ith.check_theory()

        if show_compiled.get():
            print ivy_logic.sig
            for kwd,lst in [('axiom',mod.labeled_axioms),
                            ('init',mod.labeled_inits),
                            ('conjecture',mod.labeled_conjs),]:
                print labeled_fmlas_to_str(kwd,lst)
            for x,y in mod.actions.iteritems():
                print iu.pretty(ia.action_def_to_str(x,y))


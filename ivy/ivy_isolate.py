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
from ivy_ast import ASTContext
from collections import defaultdict
import ivy_printer

show_compiled = iu.BooleanParameter("show_compiled",False)
cone_of_influence = iu.BooleanParameter("coi",True)
filter_symbols = iu.BooleanParameter("filter_symbols",True)
create_imports = iu.BooleanParameter("create_imports",False)
enforce_axioms = iu.BooleanParameter("enforce_axioms",False)
do_check_interference = iu.BooleanParameter("interference",True)
pedantic = iu.BooleanParameter("pedantic",False)
opt_prefer_impls = iu.BooleanParameter("prefer_impls",False)
opt_keep_destructors = iu.BooleanParameter("keep_destructors",False)
isolate_mode = iu.Parameter("isolate_mode","check")

# Used by extractor to switch off assumption of present invariants
assume_invariants = iu.BooleanParameter("assume_invariants",True)

def lookup_action(ast,mod,name):
    if name not in mod.actions:
        raise iu.IvyError(ast,"action {} undefined".format(name))
    return mod.actions[name]

def add_mixins(mod,actname,action2,assert_to_assume=lambda m:[],use_mixin=lambda:True,mod_mixin=lambda name,m:m):
    # TODO: mixins need to be in a fixed order
    res = action2
    if create_imports.get():
        res = res.drop_invariants()
    for mixin in mod.mixins[actname]:
        mixin_name = mixin.mixer()
        action1 = lookup_action(mixin,mod,mixin_name)
        if use_mixin(mixin_name):
            ata = assert_to_assume(mixin)
            if ata:
                action1 = action1.assert_to_assume(ata)
            action1 = mod_mixin(mixin,action1)
            res = ia.apply_mixin(mixin,action1,res)
    return res

def summarize_action(action):
    res = ia.Sequence()
    res.lineno = action.lineno
    res.formal_params = action.formal_params
    res.formal_returns = action.formal_returns
    if hasattr(action,'labels'):
        res.labels = action.labels
    # have to havoc the in/out parameters, other outs are non-deterministic anyway
    if isolate_mode.get() != 'test':
        for x in res.formal_returns:
            if x in res.formal_params:
                res.args.append(ia.HavocAction(x))
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

def startswith_some_rec(s,prefixes,mod):
    if s in mod.privates:
        return False
    parts = s.rsplit(iu.ivy_compose_character,1)
    return startswith_eq_some_rec(parts[0],prefixes,mod) if len(parts)==2 else 'this' in prefixes

#def startswith_eq_some(s,prefixes):
#    return any(s.startswith(name+iu.ivy_compose_character) or s == name for name in prefixes)

def startswith_eq_some_rec(s,prefixes,mod):
    if s in prefixes:
        return True
    return startswith_some_rec(s,prefixes,mod)

def startswith_some(s,prefixes,mod):
    s = implementation_map.get(s,s)
    return startswith_some_rec(s,prefixes,mod)

def startswith_eq_some(s,prefixes,mod):
    s = implementation_map.get(s,s)
    return startswith_eq_some_rec(s,prefixes,mod)

def vstartswith_some_rec(s,prefixes,mod):
    if s in mod.privates or s in vprivates:
        return False
    parts = s.rsplit(iu.ivy_compose_character,1)
    return vstartswith_eq_some_rec(parts[0],prefixes,mod) if len(parts)==2 else 'this' in prefixes

def vstartswith_eq_some_rec(s,prefixes,mod):
    if s in prefixes:
        return True
    return vstartswith_some_rec(s,prefixes,mod)

def vstartswith_eq_some(s,prefixes,mod):
    if iu.version_le(iu.get_string_version(),"1.6"):
        return startswith_eq_some(s,prefixes,mod)
    s = implementation_map.get(s,s)
    res = vstartswith_eq_some_rec(s,prefixes,mod)
    return res

def strip_map_lookup(name,strip_map,with_dot=False):
    name = canon_act(name)
    for prefix in strip_map:
        if (name+iu.ivy_compose_character).startswith(prefix+iu.ivy_compose_character):
            return strip_map[prefix]
    return []

def presentable(name):
    return str(name).split(':')[-1]

def get_strip_params(name,args,strip_map,strip_binding,ast):
    strip_params = strip_map_lookup(name,strip_map)
    if not(len(args) >= len(strip_params)):
        raise iu.IvyError(ast,"cannot strip isolate parameters from {}".format(presentable(name)))
    for sp,ap in zip(strip_params,args):
        if ap not in strip_binding or strip_binding[ap] != sp:
            raise iu.IvyError(ast,"cannot strip parameter {} from {}".format(presentable(ap),presentable(name)))
    return strip_params

def strip_sort(sort,strip_params):
    dom = list(sort.dom[len(strip_params):])
    if dom or sort.is_relational():
        return ivy_logic.FunctionSort(*(dom+[sort.rng]))
    return sort.rng

def strip_action(ast,strip_map,strip_binding,is_init=False,init_params=[]):
    if isinstance(ast,ia.CallAction):
        name = canon_act(ast.args[0].rep)
        args = [strip_action(arg,strip_map,strip_binding,is_init,init_params) for arg in ast.args[0].args]
        strip_params = get_strip_params(name,ast.args[0].args,strip_map,strip_binding,ast)
        call = ast.args[0].clone(args[len(strip_params):])
        return ast.clone([call]+[strip_action(arg,strip_map,strip_binding,is_init,init_params) for arg in ast.args[1:]])
    if isinstance(ast,ia.Action):
        for sym in ast.modifies():
            if sym.name in ivy_logic.sig.symbols:
                lhs_params = strip_map_lookup(sym.name,strip_map)
                if len(lhs_params) != num_isolate_params:
                    if not (len(lhs_params) == 0 and len(strip_binding) == 0 and is_init):
                        raise iu.IvyError(ast,"assignment may be interfering")
    if isinstance(ast,ia.AssignAction) and len(init_params) > 0:
        lhs = ast.args[0]
        xtra_bindings = zip(lhs.args[len(strip_binding):],init_params)
        if any(not ivy_logic.is_variable(x) for x,y in xtra_bindings):
            raise iu.IvyError(ast,"assignment may be interfering")
        strip_binding = strip_binding.copy()
        strip_binding.update(xtra_bindings)    
#        print 'strip_binding = {}'.format([(str(x),str(y)) for x,y in strip_binding.iteritems()]) 
    if (ivy_logic.is_constant(ast) or ivy_logic.is_variable(ast)) and ast in strip_binding:
        sname = strip_binding[ast]
        if sname not in ivy_logic.sig.symbols:
            ivy_logic.add_symbol(sname,ast.sort)
            strip_added_symbols.append(ivy_logic.Symbol(sname,ast.sort))
        return ivy_logic.Symbol(sname,ast.sort)
    args = [strip_action(arg,strip_map,strip_binding,is_init,init_params) for arg in ast.args]
    if ivy_logic.is_app(ast) and ast not in im.module.sig.constructors:
        name = ast.rep.name
        strip_params = get_strip_params(name,ast.args,strip_map,strip_binding,ast)
        if strip_params:
            new_sort = strip_sort(ast.rep.sort,strip_params)
            new_args = args[len(strip_params):]
            new_symbol = ivy_logic.Symbol(name,new_sort)
            return new_symbol(*new_args)
    if isinstance(ast,ivy_ast.Atom) and ast.rep not in im.module.sig.sorts:
        name = ast.rep
        strip_params = get_strip_params(name,ast.args,strip_map,strip_binding,ast)
        if strip_params:
            new_args = args[len(strip_params):]
            return ast.clone(new_args)
    return ast.clone(args)
                
def get_strip_binding(ast,strip_map,strip_binding):
    [get_strip_binding(arg,strip_map,strip_binding) for arg in ast.args]
    name = ast.rep.name if ivy_logic.is_app(ast) else ast.rep if isinstance(ast,ivy_ast.Atom) else None
    if name:
        strip_params = strip_map_lookup(name,strip_map)
        if not(len(ast.args) >= len(strip_params)):
            raise iu.IvyError(ast,"cannot strip isolate parameters from {}".format(presentable(name)))
        for sp,ap in zip(strip_params,ast.args):
            if ap in strip_binding and strip_binding[ap] != sp:
                raise iu.IvyError(action,"cannot strip parameter {} from {}",presentable(ap),presentable(name))
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
    if not strip_map:
        return
    for f in lfmlas:
        if isinstance(f.formula,ivy_ast.SchemaBody):
            raise IvyError(f,'cannot strip parameter from a theorem')
    new_lfmlas = [strip_labeled_fmla(f,strip_map) for f in lfmlas]
    del lfmlas[:]
    lfmlas.extend(new_lfmlas)
    
def strip_native(native,strip_map):
    strip_binding = {}
    for a in native.args[2:]:
        get_strip_binding(a,strip_map,strip_binding)
    fmlas = [strip_action(fmla,strip_map,strip_binding) for fmla in native.args[2:]]
    lbl = native.args[0]
    if lbl:
        lbl = lbl.clone(lbl.args[len(strip_map_lookup(lbl.rep,strip_map,with_dot=False)):])
    return native.clone([lbl,native.args[1]] + fmlas)
    
def strip_natives(natives,strip_map):
    new_natives = [strip_native(f,strip_map) for f in natives]
    del natives[:]
    natives.extend(new_natives)

def canon_act(name):
    return name[4:] if name.startswith('ext:') else name

def strip_isolate(mod,isolate,impl_mixins,all_after_inits,extra_strip):
    global strip_added_symbols
    global num_isolate_params
    ipl = isolate.params()
    if any (isinstance(p,ivy_ast.Variable) for p in ipl):
        subst = dict()
        for p in ipl:
            if isinstance(p,ivy_ast.Variable):
                v = ivy_ast.App('iso:'+p.rep)
                v.sort = p.sort
                subst[p.rep] = v
        isolate = ivy_ast.substitute_ast(isolate,subst)

    num_isolate_params = len(isolate.params())
    ips = set(p.rep for p in isolate.params())
    for atom in isolate.verified()+isolate.present():
        for p in atom.args:
            if p.rep not in ips:
                raise iu.IvyError(p,'unbound isolate parameter: {}'.format(p))
    strip_added_symbols = []
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
    for ms in impl_mixins.values():
        for m in ms:
            if isinstance(m,ivy_ast.MixinImplementDef):
                strip_params = strip_map_lookup(canon_act(m.mixer()),strip_map)
                strip_map[m.mixee()] = strip_params
    strip_map.update(extra_strip)
#    for imp in mod.imports:
#        strip_map[imp.imported()] = [a.rep for a in isolate.params()]
    # strip the actions
    new_actions = {}
    for name,action in mod.actions.iteritems():
        strip_params = strip_map_lookup(canon_act(name),strip_map,with_dot=False)
        orig_name = name[4:] if name.startswith('ext:') else name
        is_init=(orig_name in all_after_inits)
        init_params = []
        if not(len(action.formal_params) >= len(strip_params)):
            if is_init:
                init_params = strip_params[len(action.formal_params):]
            else:
                raise iu.IvyError(action,"cannot strip isolate parameters from {}".format(name))
        strip_binding = dict(zip(action.formal_params,strip_params))
#        if isinstance(action,ia.NativeAction) and len(strip_params) != num_isolate_params:
#            raise iu.IvyError(None,'foreign function {} may be interfering'.format(name))
        new_action = strip_action(action,strip_map,strip_binding,is_init=is_init,init_params=init_params)
        new_action.formal_params = action.formal_params[len(strip_params):]
        new_action.formal_returns = action.formal_returns
        if hasattr(action,'labels'):
            new_action.labels = action.labels
        new_actions[name] = new_action
    mod.actions.clear()
    mod.actions.update(new_actions)

    # strip the axioms and conjectures
    for x in [mod.labeled_axioms,mod.labeled_props,mod.labeled_conjs,mod.labeled_inits,mod.definitions]:
        strip_labeled_fmlas(x,strip_map)

    # strip the native quotes
    strip_natives(mod.natives,strip_map)

    # strip the signature
    new_symbols = {}
    for name,sym in ivy_logic.sig.symbols.iteritems():
        if sym not in im.module.sig.constructors:
            strip_params = strip_map_lookup(name,strip_map)
            if strip_params:
                if not (len(sym.sort.dom) >= len(strip_params)):
                    raise iu.IvyError(None,"cannot strip isolate parameters from {}".format(name))
                new_sort = strip_sort(sym.sort,strip_params)
                sym =  ivy_logic.Symbol(name,new_sort)
        new_symbols[name] = sym
    ivy_logic.sig.symbols.clear()
    ivy_logic.sig.symbols.update(new_symbols)
    
    # strip the parameters
    old_params = list(mod.params)
    mod.params = []
    for sym in old_params:
        name = sym.name
        strip_params = strip_map_lookup(name,strip_map)
        if strip_params:
            if not (len(sym.sort.dom) >= len(strip_params)):
                raise iu.IvyError(None,"cannot strip isolate parameters from {}".format(name))
            new_sort = strip_sort(sym.sort,strip_params)
            sym =  ivy_logic.Symbol(name,new_sort)
        mod.params.append(sym)



    if iu.version_le(iu.get_string_version(),"1.6"):
        del mod.params[:]
    add_map = dict((s.name,s) for s in strip_added_symbols)
    used = set()
    for s in isolate.params():
        if not(isinstance(s,ivy_ast.App) and not s.args):
            raise iu.IvyError(isolate,"bad isolate parameter")
        if s.rep in used:
            raise iu.IvyError(isolate,"repeated isolate parameter: {}".format(s.rep))
        used.add(s.rep)
        if s.rep not in add_map:
            if s.sort not in mod.sig.sorts:
                raise iu.IvyError(isolate,"bad type {} in isolate parameter".format(s.sort))
            sym = ivy_logic.add_symbol(s.rep,mod.sig.sorts[s.sort]) 
            mod.params.append(sym)
        else:
            mod.params.append(add_map[s.rep])
        mod.param_defaults.append(None)
            
def has_side_effect_rec(mod,new_actions,actname,memo):
    if actname in memo:
        return False
    memo.add(actname)
    action = new_actions[actname]
    for sub in action.iter_subactions():
        if isinstance(sub,ia.NativeAction):
            if sub.impure:
                return True
        for sym in sub.modifies():
            if sym.name in mod.sig.symbols:
                return True
        if isinstance(sub,ia.AssertAction):
            return True
        if isinstance(sub,ia.Ranking):
            return True
        if isinstance(sub,ia.CallAction):
            if has_side_effect_rec(mod,new_actions,sub.args[0].rep,memo):
                return True
    return False

def has_side_effect(mod,new_actions,actname):
    return has_side_effect_rec(mod,new_actions,actname,set())


def get_calls_mods(mod,summarized_actions,actname,calls,mods,mixins,loops,interf_syms):
    if actname in calls or actname not in summarized_actions:
        return
    action = mod.actions[actname]
    acalls = set()
    amods = set()
    amixins = set()
    aloops = set()
    calls[actname] = acalls
    mods[actname] = amods
    mixins[actname] = amixins
    loops[actname] = aloops
    for sub in action.iter_subactions():
        for sym in sub.modifies():
            if sym in interf_syms:
                amods.add(sym)
        if isinstance(sub,ia.CallAction):
            calledname = sub.args[0].rep
            if calledname not in summarized_actions:
                acalls.add(calledname)
            get_calls_mods(mod,summarized_actions,calledname,calls,mods,mixins,loops,interf_syms)
            if calledname in calls:
                acalls.update(calls[calledname])
                acalls.update(mixins[calledname]) # tricky -- mixins of callees count as callees
                amods.update(mods[calledname])
                aloops.update(loops[calledname])
        if isinstance(sub,ia.WhileAction) and not isinstance(sub.args[-1],ia.Ranking):
            aloops.add(sub)
    for mixin in mod.mixins[actname]:
        calledname = mixin.args[0].relname
        if calledname not in summarized_actions:
            amixins.add(calledname)
        get_calls_mods(mod,summarized_actions,calledname,calls,mods,mixins,loops,interf_syms)
        if calledname in calls:
            acalls.update(calls[calledname])
            amixins.update(mixins[calledname]) # mixins of mixins count as mixins
            amods.update(mods[calledname])
            aloops.update(loops[calledname])
        

def has_unsummarized_mixins(mod,actname,summarized_actions,kind):
    return any(isinstance(mixin,kind) and mixin.args[0].relname not in summarized_actions
               for mixin in mod.mixins[actname])

def get_callouts_action(mod,new_actions,summarized_actions,callouts,action,acallouts,head,tail):
    if isinstance(action,ia.Sequence):
        for idx,sub in enumerate(action.args):
            get_callouts_action(mod,new_actions,summarized_actions,callouts,sub,acallouts,
                                head and idx==0, tail and idx == len(action.args)-1)
    elif isinstance(action,ia.CallAction):
        calledname = action.args[0].rep
        if calledname in summarized_actions:
            if has_unsummarized_mixins(mod,calledname,summarized_actions,ivy_ast.MixinBeforeDef):
                head = False
            if has_unsummarized_mixins(mod,calledname,summarized_actions,ivy_ast.MixinAfterDef):
                tail = False
            acallouts[(3 if tail else 1) if head else (2 if tail else 0)].add(calledname)
        else:
            get_callouts(mod,new_actions,summarized_actions,calledname,callouts)
            # TODO update acallouts correctly
            for a,b in zip(acallouts,callouts[calledname]):
                a.update(b)
    else:
        for sub in action.args:
            if isinstance(sub,ia.Action):
                get_callouts_action(mod,new_actions,summarized_actions,callouts,sub,acallouts,head,tail)
        

def get_callouts(mod,new_actions,summarized_actions,actname,callouts):
    if actname in callouts or actname in summarized_actions:
        return
    acallouts = (set(),set(),set(),set())
    callouts[actname] = acallouts
    action = new_actions[actname]
    get_callouts_action(mod,new_actions,summarized_actions,callouts,action,acallouts,True,True)
    

def get_loc_mods(mod,actname):
    action = mod.actions[actname]
    res = [s for s in action.modifies() if s.name.startswith('fml:')]
    return res

def find_references(mod,syms,new_actions):
    syms = set(syms)
    refs = set()
    for x in mod.labeled_axioms+mod.labeled_props+mod.labeled_inits+mod.labeled_conjs+mod.definitions:
        if syms.intersection(lu.used_symbols_ast(x.formula)):
            refs.add(x.lineno)
    for x in new_actions.values():
        if syms.intersection(lu.used_symbols_ast(x)):
            refs.add(x.lineno)
    return refs
    

def check_interference(mod,new_actions,summarized_actions,impl_mixins,check_term,interf_syms,
                       after_inits,all_after_inits):
    calls = dict()
    mods = dict()
    mixins = dict()
    locmods = dict()
    loops = dict()
    for actname in summarized_actions:
        get_calls_mods(mod,summarized_actions,actname,calls,mods,mixins,loops,interf_syms)
        locmods[actname] = get_loc_mods(mod,actname)
    callouts = dict()  # these are triples (midcalls,headcalls,tailcalls,bothcalls)
    for actname in new_actions:
        get_callouts(mod,new_actions,summarized_actions,actname,callouts)
    for actname,action in new_actions.iteritems():
        if actname not in summarized_actions:
            for called_name in action.iter_calls():
                called_name = canon_act(called_name)
                pre_refed = set()
                for m in mod.mixins[called_name]:
                    if isinstance(m,ivy_ast.MixinBeforeDef) and m.mixer() not in summarized_actions:
                        pre_refed.update(lu.used_symbols_ast(mod.actions[m.mixer()]))
                all_calls = ([called_name] + [m.mixer() for m in mod.mixins[called_name]]
                                           + [m.mixer() for m in impl_mixins[called_name]])
                for called in all_calls:
                    if called in summarized_actions:
                        cmods = set(mods[called])
                        for loc in locmods[called]:
                            if loc in pre_refed:
                                cmods.add(loc)
                        if cmods:
                            things = ','.join(sorted(map(str,cmods)))
                            refs = ''.join('\n' + str(ln) + 'referenced here' for ln in find_references(mod,cmods,new_actions))
                            raise iu.IvyError(action,"Call out to {} may have visible effect on {}{}"
                                              .format(called,things,refs))
                        cloops = loops[called]
                        if check_term and cloops:
                            refs = ''.join('\n' + str(lp.lineno) + 'loop here' for lp in cloops)
                            raise iu.IvyError(action,"Call out to {} may not terminate (needs a decreases clause){}"
                                              .format(called,refs))
            if actname in callouts:
                for midcall in sorted(callouts[actname][0]):
                    if midcall in calls:
                        callbacks = calls[midcall]
                        if callbacks and mods[midcall]:
                            raise iu.IvyError(action,"Call to {} may cause interfering callback to {}"
                                              .format(midcall,','.join(callbacks)))
                
    after_init_refs = set()
    for ainame in after_inits:
        after_init_refs.update(lu.used_symbols_ast(new_actions[ainame]))

    for e in mod.exports:
        called_name = canon_act(e.exported())
        all_calls = ([called_name] + [m.mixer() for m in mod.mixins[called_name]]
                                   + [m.mixer() for m in impl_mixins[called_name]])
        for called in all_calls:
            if called in summarized_actions:
                cmods = set(mods[called])
                if called in all_after_inits:
                    cmods = set(sym for sym in cmods if sym in after_init_refs)
                if cmods:
                    things = ','.join(sorted(map(str,cmods)))
                    refs = ''.join('\n' + str(ln) + 'referenced here' for ln in find_references(mod,cmods,new_actions))
                    raise iu.IvyError(None,"External call to {} may have visible effect on {}{}"
                                      .format(called,things,refs))
            


def ancestors(s):
    while iu.ivy_compose_character in s:
        yield s
        s,_ = s.rsplit(iu.ivy_compose_character,1)
    yield s

def spec_ancestors(s):
    while iu.ivy_compose_character in s:
        yield s
        s,t = s.rsplit(iu.ivy_compose_character,1)
        if t == "spec":
            break
    yield s

def get_prop_dependencies(mod):
    """ get a list of pairs (p,ds) where p is a property ds is a list
    of objects its proof depends on """
    depmap = defaultdict(list)
    for iso in mod.isolates.values():
        for v in iso.verified():
            depmap[v.rep].extend(w.rep for w in iso.verified()+iso.present())
    objs = set()
    for ax in mod.labeled_axioms:
        if ax.label:
            for n in ancestors(ax.label.rep):
                objs.add(n)
    for itps in mod.interps.values():
        for itp in itps:
            if itp.label:
                for n in ancestors(itp.label.rep):
                    objs.add(n)        
    res = []
    for prop in mod.labeled_props:
        if prop.label:
            ds = []
            for n in spec_ancestors(prop.label.rep):
                ds.extend(d for d in depmap[n] if d in objs)
            res.append((prop,ds))
    return res

def set_privates_prefer(mod,isolate,preferred):
    verified = set(a.relname for a in (isolate.verified()))
    suff = "impl" if preferred == "spec" else "spec"
    mod.privates = set(mod.privates)
    if 'this' not in verified and suff in mod.hierarchy and preferred in mod.hierarchy:
        mod.privates.add(suff)
    for n,l in mod.hierarchy.iteritems():
        if n not in verified:
            if suff in l and preferred in l:
                mod.privates.add(iu.compose_names(n,suff))

def get_private_from_attributes(mod,name,suff):
    attrname = iu.compose_names(name,isolate_mode.get())
    if attrname in mod.attributes:
        aval = mod.attributes[attrname].rep
        if aval not in ['spec','impl']:
            raise iu.IvyError(None,'attribute {} has bad value "{}". should be "spec" or "impl"'.format(attrname,aval))
        suff = 'spec' if aval == 'impl' else 'impl'
    return suff

def set_privates(mod,isolate,suff=None):
    if suff == None and opt_prefer_impls.get():
        set_privates_prefer(mod,isolate,"impl")
        return
    suff = suff or ("spec" if isinstance(isolate,ivy_ast.ExtractDef) else "impl")
    mod.privates = set(mod.privates)
    if suff in mod.hierarchy:
        mod.privates.add(suff)
    for n,l in mod.hierarchy.iteritems():
        nsuff = get_private_from_attributes(mod,n,suff)
        if nsuff in l:
            mod.privates.add(iu.compose_names(n,nsuff))
    for name in mod.attributes:
        p,c = iu.parent_child_name(name)
        if c in ['spec','impl','private']:
            pp,pc = iu.parent_child_name(p)
            nsuff = get_private_from_attributes(mod,pp,suff)
            if c == nsuff or c == "private":
                mod.privates.add(p)
    global vprivates
    vprivates = set()
    for isol in mod.isolates.values():
        for v in isol.verified():
            vprivates.add(v.rep)
            
def get_props_proved_in_isolate_orig(mod,isolate):
    save_privates = mod.privates
    mod.privates = set()
    set_privates(mod,isolate,'spec')
    verified,present = get_isolate_info(mod,isolate,'spec')
    check_pr = lambda name: (name is None or vstartswith_eq_some(name.rep,verified,mod))
    not_proved = [a for a in mod.labeled_props if not check_pr(a.label)]
    proved = [a for a in mod.labeled_props if check_pr(a.label)]
    mod.privates = save_privates
    return proved,not_proved

def get_props_proved_in_isolate(mod,isolate):
    if iu.version_le(iu.get_string_version(),"1.6"):
        proved,not_proved = get_props_proved_in_isolate_orig(mod,isolate)
    else:
        save_privates = mod.privates
        mod.privates = set()
        set_privates(mod,isolate,'impl')
        verified,present = get_isolate_info(mod,isolate,'impl')
        if not iu.version_le(iu.get_string_version(),"1.6"):
            for other_iso in mod.isolates.values():
                if other_iso is not isolate:
                    for other_verified in other_iso.verified():
                        ovn = other_verified.relname
                        if startswith_some(ovn,verified,mod):
                            mod.privates.add(ovn)
        check_pr = lambda name: (name is None or vstartswith_eq_some(name.rep,verified,mod))
        not_proved = [a for a in mod.labeled_props if not check_pr(a.label)]
        proved = [a for a in mod.labeled_props if check_pr(a.label)]
        mod.privates = save_privates
    # remove the subgoals from not_proved
    subs = set(sg.id for p,sgs in mod.subgoals for sg in sgs)
    not_proved = [a for a in not_proved if a.id not in subs]
    return proved,not_proved
    

def check_with_parameters(mod,isolate_name):
    if isolate_name not in mod.isolates:
        raise iu.IvyError(None,"undefined isolate: {}".format(isolate_name))
    isolate = mod.isolates[isolate_name]

    verified = set(a.relname for a in isolate.verified())
    present = set(a.relname for a in isolate.present())
    present.update(verified)

    if iu.version_le(iu.get_string_version(),"1.6"):
        derived = set(ldf.formula.args[0].rep.name for ldf in mod.definitions)
    else:
        derived = set(ldf.name for ldf in mod.definitions)
        
    propnames = set(x.label.rep for x in (mod.labeled_props+mod.labeled_axioms+mod.labeled_conjs) if x.label is not None)
    for name in present:
        if (name != 'this' and name not in mod.hierarchy
            and name not in ivy_logic.sig.sorts
            and name not in derived
            and name not in ivy_logic.sig.interp
            and name not in mod.actions
            and name not in ivy_logic.sig.symbols
            and name not in propnames):
            raise iu.IvyError(None,"{} is not an object, action, sort, definition, interpreted function or property".format(name))


def get_isolate_info(mod,isolate,kind,extra_with=[]):
    verified = set(a.relname for a in (isolate.verified()+tuple(extra_with)))
    present = set(a.relname for a in isolate.present())
    present.update(verified)


    xtra = set(iu.compose_names(a.relname,kind) for a in isolate.verified())
    verified.update(xtra)
    present.update(xtra)

    vp = set()
    for isol in mod.isolates.values():
        for v in isol.verified():
            vp.add(v.rep)
    for name in mod.attributes:
        p,c = iu.parent_child_name(name)
        if c == kind or c == "private":
            p1,c1 = iu.parent_child_name(p)
            if p1 in verified:
                if p not in vp:
                    verified.add(p)
                present.add(p)
    

    return verified,present


def follow_definitions_rec(sym,dmap,all_syms,memo):
    all_syms.add(sym)
    if sym in dmap and sym not in memo:
        memo.add(sym)
        for s in lu.used_symbols_ast(dmap[sym]):
            follow_definitions_rec(s,dmap,all_syms,memo)

def follow_definitions(ldfs,all_syms):
    dmap = dict((ldf.formula.args[0].rep,ldf.formula.args[1]) for ldf in ldfs)
    for sym in list(all_syms):
        follow_definitions_rec(sym,dmap,all_syms,set())

def empty_clone(action):
    res = ia.Sequence()
    res.lineno = action.lineno
    action.copy_formals(res)
    return res

def collect_sort_destructors(sort,res,memo):
    if sort.name in memo:
        return
    memo.add(sort.name)
    if sort.name in im.module.sort_destructors:
        for dstr in im.module.sort_destructors[sort.name]:
            res.add(dstr)
            collect_relevant_destructors(dstr,res,memo)
    elif sort.name in im.module.variants:
        for sort2 in im.module.variants[sort.name]:
            collect_sort_destructors(sort2,res,memo)

def collect_relevant_destructors(sym,res,memo):
    if not hasattr(sym.sort,'rng'):
        return 
    collect_sort_destructors(sym.sort.rng,res,memo)

           
def add_extern_precond(mod,subaction,preconds):
    called = mod.actions[subaction.args[0].rep]
    conjs = []
    for fml,act in zip(called.formal_params,subaction.args[0].args):
        if ivy_logic.is_numeral(act) or ivy_logic.is_constant(act) and act in mod.sig.constructors:
            conjs.append(ivy_logic.Equals(fml,act))
    if len(conjs) == 0:
        del preconds[:]  # anything or true is true
    preconds.append(ivy_logic.And(*conjs))


def isolate_component(mod,isolate_name,extra_with=[],extra_strip=None,after_inits=None):

    global implementation_map
    implementation_map = {}
    if isolate_name == None:
        isolate = ivy_ast.IsolateDef(ivy_ast.Atom('iso'),ivy_ast.Atom('this'))
        isolate.with_args = 0
    else:
        if isolate_name not in mod.isolates:
            raise iu.IvyError(None,"undefined isolate: {}".format(isolate_name))
        isolate = mod.isolates[isolate_name]
    set_privates(mod,isolate)
    verified,present = get_isolate_info(mod,isolate,'impl',extra_with)

    if not interpret_all_sorts:
        for type_name in list(ivy_logic.sig.interp):
            if not (type_name in present and type_name not in mod.hierarchy or any(startswith_eq_some(itp.label.rep,present,mod) for itp in mod.interps[type_name] if itp.label)):
                del ivy_logic.sig.interp[type_name]
    delegates = set(s.delegated() for s in mod.delegates if not s.delegee())
    delegated_to = dict((s.delegated(),s.delegee()) for s in mod.delegates if s.delegee())
    
    mod.isolate_info = im.IsolateInfo()

    impl_mixins = defaultdict(list)
    # delegate all the stub actions to their implementations
    for actname,ms in mod.mixins.iteritems():
        implements = [m for m in ms if isinstance(m,ivy_ast.MixinImplementDef)]
        impl_mixins[actname].extend(implements)
        before_after = [m for m in ms if not isinstance(m,ivy_ast.MixinImplementDef)]
        del ms[:]
        ms.extend(before_after)
        for m in implements:
            for foo in (m.mixee(),m.mixer()):
                if foo not in mod.actions:
                    raise IvyError(m,'action {} not defined'.format(foo))
            if startswith_eq_some(m.mixer(),present,mod):
                action = mod.actions[m.mixee()]
                if not (isinstance(action,ia.Sequence) and len(action.args) == 0):
                    raise iu.IvyError(m,'multiple implementations of action {}'.format(m.mixee()))
                action = ia.apply_mixin(m,mod.actions[m.mixer()],action)
                mod.actions[m.mixee()] = action
                mod.isolate_info.implementations.append((m.mixer(),m.mixee(),action))
            implementation_map[m.mixee()] = m.mixer()

    new_actions = {}
    use_mixin = lambda name: startswith_some(name,present,mod)
    def prefix_call_ext(name):
        return 'ext:'+name if startswith_some(name,verified,mod) else name
    mod_mixin = lambda mixin,m: m if startswith_some(mixin.mixer(),verified,mod) else m.prefix_calls(prefix_call_ext)
    def ext_mod_mixin(ea):
        return lambda mixin,m: m if startswith_some(mixin.mixer(),verified,mod) and not ea(mixin) else m.prefix_calls(prefix_call_ext)
    all_mixins = lambda m: True
    no_mixins = lambda m: False
    after_mixins = lambda m: isinstance(m,ivy_ast.MixinAfterDef)
    before_mixins = lambda m: isinstance(m,ivy_ast.MixinBeforeDef)
    delegated_to_verified = lambda n: n in delegated_to and vstartswith_eq_some(delegated_to[n],verified,mod)

    # for verified external actions, we assume the asserts in before mixins
    # Require behaves like assert in before mixin

    ext_assumes = lambda m: ([ia.RequiresAction] + 
                             ([ia.AssertAction]
                              if before_mixins(m) and not delegated_to_verified(m.mixer())
                              else []))

    # for unverified internal actions, we assume the asserts in after mixins
    # Ensure behaves like assert in after mixins

    int_assumes = lambda m: ([ia.EnsuresAction] + 
                             ([ia.AssertAction]
                              if after_mixins(m) and not delegated_to_verified(m.mixer())
                              else []))

    # for unverified external, everything is assumed

    ext_assumes_no_ver = lambda m: ([ia.EnsuresAction,ia.RequiresAction] +
                                    ([ia.AssertAction]
                                     if not delegated_to_verified(m.mixer())
                                     else []))

    # for an internal summarized action, we assume the asserts in after mixins
    # Ensure behaves like assert in after mixins

    int_sum_assumes = lambda m: ([ia.EnsuresAction] + 
                                 ([ia.AssertAction]
                                  if after_mixins(m)
                                  else []))

    summarized_actions = set()
    for actname,action in mod.actions.iteritems():
        ver = vstartswith_eq_some(actname,verified,mod)
        pre = startswith_eq_some(actname,present,mod)
        if pre: 
            if not ver or actname in delegates:
                ext_kinds = [ia.AssertAction,ia.EnsuresAction,ia.RequiresAction] 
                ext_action = action.assert_to_assume(ext_kinds).prefix_calls('ext:')
                if actname in delegates:
                    int_action = action.prefix_calls('ext:')
                else:
                    int_kinds = [ia.AssertAction,ia.EnsuresAction] 
                    int_action = action.assert_to_assume(int_kinds).prefix_calls('ext:')
            else:
                ext_kinds = [ia.RequiresAction] 
                ext_action = action.assert_to_assume(ext_kinds)
                int_action = action
            # internal version of the action has mixins checked
            ea = no_mixins if ver else int_assumes
            new_actions[actname] = add_mixins(mod,actname,int_action,ea,use_mixin,lambda mixin,m:m)
            # external version of the action assumes mixins are ok, unless they
            # are delegated to a currently verified object
            ea = ext_assumes if ver else ext_assumes_no_ver
            new_action = add_mixins(mod,actname,ext_action,ea,use_mixin,ext_mod_mixin(ea))
            new_actions['ext:'+actname] = new_action
            # TODO: external version is public if action public *or* called from opaque
            # public_actions.add('ext:'+actname)

            # record info on usage of implementations and monitors for user
            if actname not in implementation_map:
                mod.isolate_info.implementations.append((actname,actname,action))
        else:
            # TODO: here must check that summarized action does not
            # have a call dependency on the isolated module
            summarized_actions.add(actname)
            action = summarize_action(action)
            new_actions[actname] = add_mixins(mod,actname,action,int_sum_assumes,use_mixin,ext_mod_mixin(after_mixins))
            new_actions['ext:'+actname] = add_mixins(mod,actname,action,ext_assumes_no_ver,use_mixin,ext_mod_mixin(all_mixins))

        for mixin in mod.mixins[actname]:
            if use_mixin(mixin.mixer()):
                mod.isolate_info.monitors.append((mixin.mixer(),mixin.mixee(),mod.actions[mixin.mixer()]))
            

    # figure out what is exported:
    exported = set()
    export_preconds = defaultdict(list)
#    save_implementation_map = implementation_map
#    implementation_map = {}

    def make_before_export(actname):
            ver = vstartswith_eq_some(actname,verified,mod)
            action = mod.actions[actname]
            if not ver or actname in delegates:
                act = action.assert_to_assume([ia.AssertAction,ia.RequiresAction]).prefix_calls('ext:')
            else:
                act = empty_clone(action)
            for mixin in mod.mixins[actname]:
                mixin_name = mixin.args[0].relname
                action1 = lookup_action(mixin,mod,mixin_name)
                if use_mixin(mixin_name) and before_mixins(mixin):
                    action1 = action1.assert_to_assume([ia.AssertAction,ia.RequiresAction])
                    action1 = ext_mod_mixin(all_mixins)(mixin,action1)
                    act = ia.apply_mixin(mixin,action1,act)
            mod.before_export['ext:' + actname] = act

    for e in mod.exports:
        if not e.scope() and startswith_eq_some(e.exported(),present,mod): # global scope
            exported.add('ext:' + e.exported())
            make_before_export(e.exported())
            
    explicit_exports = set(exported)

    with_effects = set()
    for actname,action in mod.actions.iteritems():
        if not startswith_eq_some(actname,present,mod):
            for subaction in action.iter_subactions():
                if isinstance(subaction,ia.CallAction):
                    c = subaction.args[0].rep
                    if (startswith_eq_some(c,present,mod)
                        or any(startswith_some(m.mixer(),present,mod) for m in mod.mixins[c])) :
                            if ('ext:' + c) not in explicit_exports:
                                add_extern_precond(mod,subaction,export_preconds['ext:' + c])
                            if ('ext:' + c) in exported or c in with_effects:
                                continue
                            if not has_side_effect(mod,new_actions,c):
                                with_effects.add(c)
                                continue
                            exported.add('ext:' + c)
                            make_before_export(c)


    for actname in export_preconds:
        pcs = export_preconds[actname]
        mod.ext_preconds[actname] = pcs[0] if len(pcs) == 1 else ivy_logic.Or(*pcs)

#    implementation_map = save_implementation_map


    # We allow objects to reference any symbols in global scope, and
    # we keep axioms declared in global scope. Because of the way
    # thigs are named, this gives a different condition for keeping
    # symbols and axioms (in particular, axioms in global scope have
    # label None). Maybe this needs to be cleaned up.

        
    keep_ax = lambda name: (name is None or startswith_eq_some(name.rep,present,mod))

    prop_deps = get_prop_dependencies(mod)

    # filter the conjectures

    global vprivates

    if iu.version_le(iu.get_string_version(),"1.6"):
        new_conjs = [c for c in mod.labeled_conjs if keep_ax(c.label)]
    else:
        new_conjs = [c for c in mod.labeled_conjs if vstartswith_eq_some(c.label.rep,verified,mod)]
        assumed_conjs = [c for c in mod.labeled_conjs if startswith_eq_some(c.label.rep,present,mod) and not vstartswith_eq_some(c.label.rep,verified,mod)]
        
    del mod.labeled_conjs[:]
    if not create_imports.get(): # no conjectures if compiling
        mod.labeled_conjs.extend(new_conjs)

    # filter the inits

    new_inits = [c for c in mod.labeled_inits if keep_ax(c.label)]
    del mod.labeled_inits[:]
    mod.labeled_inits.extend(new_inits)
    
    # filter the axioms
    dropped_axioms = [a for a in mod.labeled_axioms if not keep_ax(a.label)]
    mod.labeled_axioms = [a for a in mod.labeled_axioms if keep_ax(a.label)]
    mod.labeled_props = [a for a in mod.labeled_props if keep_ax(a.label)]

    # convert the properties not being verified to axioms
    
    exact_present = set(a.relname for a in isolate.present())
    proved,not_proved = get_props_proved_in_isolate(mod,isolate)
    # mod.labeled_axioms.extend(not_proved)
    mod.labeled_axioms = [m for m in mod.labeled_axioms if not m.explicit or m.name in exact_present]
    new_props = []
    proved_ids = set(p.id for p in proved)
    not_proved_ids = set(p.id for p in not_proved)
    for p in mod.labeled_props:
        p = p.clone(p.args)
        if p.id in not_proved_ids:
            p.assumed = True
            p.explicit = p.explicit and p.name not in exact_present
            new_props.append(p)
        elif p.id in proved_ids:
            new_props.append(p)
            
    mod.labeled_props = new_props

    # filter natives

    mod.natives = [c for c in mod.natives if keep_ax(c.args[0])]

    # filter initializers

    if after_inits:
        for actname in after_inits:
            if not startswith_eq_some(actname,present,mod):
                extname='ext:'+actname
                del new_actions[actname]
                del new_actions[extname]
                if actname in exported:
                    del exported[actname]
                if extname in exported:
                    del exported[extname]

    all_after_inits = set(after_inits)
    after_inits = [a for a in after_inits if startswith_eq_some(a,present,mod)]
    
    def pname(s):
        return s.label if s.label else ""

    # check for interference

    # If we are generating code, we want to remove all the unreferenced actions.
    # We start with the exported actions and the actions referenced by natives and initializers
    # as roots. 

    # Get rid of the inaccessible actions

    cone = get_mod_cone(mod,actions=new_actions,roots=exported,after_inits=after_inits)        
    new_actions = dict((x,y) for x,y in new_actions.iteritems() if x in cone)
    mod.isolate_info.implementations = [(impl,actname,action) for impl,actname,action in mod.isolate_info.implementations
                                       if actname in new_actions or 'ext:'+actname in new_actions]
    mod.isolate_info.monitors = [(mixer,mixee,action) for mixer,mixee,action in mod.isolate_info.monitors
                                if mixee in new_actions or 'ext:'+mixee in new_actions]

    # Now that we have the accessible axioms, propteries inits, conjectures and actions,
    # action, we can find the accessible definitions. 

    # filter definitions and native definitions

    asts = []
    for x in [mod.labeled_axioms,mod.labeled_props,mod.labeled_inits,mod.labeled_conjs]:
        asts += [y.formula for y in x if not isinstance(y.formula,ivy_ast.SchemaBody)]
    asts += [action for action in new_actions.values()]
    for a in mod.actions.values():
        asts.extend(a.formal_params)
        asts.extend(a.formal_returns)
    for tmp in mod.natives:
        asts.extend(tmp.args[2:])
#    all_syms = set(lu.used_symbols_asts(asts))
    all_syms = set(map(ivy_logic.normalize_symbol,lu.used_symbols_asts(asts)))
    follow_definitions(mod.definitions,all_syms)
    if opt_keep_destructors.get():
        for sym in list(all_syms):
            collect_relevant_destructors(sym,all_syms,set())

    # check that any dropped axioms do not refer to the isolate's signature

    if enforce_axioms.get():
        determined = set()
        for dfn in mod.definitions:
            if ivy_logic.is_deterministic_fmla(dfn.formula.args[1]):
                determined.add(dfn.formula.defines())
        determined.update(mod.params)
        for a in dropped_axioms:
            for x in lu.used_symbols_ast(a.formula):
                if x in all_syms and not ivy_logic.is_interpreted_symbol(x) and x not in determined:
                    raise iu.IvyError(a,"relevant axiom {} not enforced (uses symbol {})".format(pname(a),x))
        for actname,action in mod.actions.iteritems():
            if startswith_eq_some(actname,present,mod):
                for c in action.iter_calls():
                    imp = implementation_map.get(c,c)
                    called = mod.actions[imp]
                    if not startswith_eq_some(c,present,mod) and c not in extra_with and not c.startswith('imp__'):
                        if not(type(called) == ia.Sequence and not called.args):
                            if (isinstance(called,ia.NativeAction) or 
                                any(p.sort.name not in mod.ghost_sorts for p in called.formal_returns)):
                                raise iu.IvyError(None,"No implementation for action {}".format(c))
        for c in mod.definitions + mod.native_definitions:
            if not keep_ax(c.label) and c.formula.args[0].rep in all_syms:
                raise iu.IvyError(c,"Definition of {} is referenced, but not present in extract".format(c.formula.args[0].rep)) 


    orig_defs = mod.definitions

    mod.definitions = [c for c in mod.definitions if (keep_ax(c.label) or c.formula.defines().name in exact_present)  and c.formula.args[0].rep in all_syms]
    mod.native_definitions = [c for c in mod.native_definitions if keep_ax(c.label) and c.formula.args[0].rep in all_syms]

    # pull in definition schemata explicitly named in 'with'

    new_defs = []
    for y in mod.definitions:
        sch = y.formula
        if isinstance(sch,ivy_logic.DefinitionSchema) and (
                sch.defines().name in exact_present or y.name in exact_present):
            y = y.clone([y.label,ivy_logic.Definition(*sch.args)])
        new_defs.append(y)
    mod.definitions = new_defs

    # After checking, we can put in place the new action definitions

    old_actions = dict()
    old_actions.update(mod.actions)
    mod.public_actions.clear()
    mod.public_actions.update(exported)
    mod.actions.clear()
    mod.actions.update(new_actions)
    
    # filter the signature
    # keep only the symbols referenced in the remaining
    # formulas

    asts = []
    for x in [mod.labeled_axioms,mod.labeled_props,mod.labeled_inits,mod.labeled_conjs,mod.definitions]:
        asts.extend(y.formula for y in x if not isinstance(y.formula,ivy_ast.SchemaBody))
    asts.extend(action for action in mod.actions.values())
    if opt_keep_destructors.get():
        asts.extend(mod.params) # if compiling, keep all of the parameters
    for a in mod.actions.values():
        asts.extend(a.formal_params)
        asts.extend(a.formal_returns)
    for tmp in mod.natives:
        asts.extend(tmp.args[2:])
    # in case a symbol is used only in a proof
    asts.extend(x[1] for x in mod.proofs)

    # Tricky: some symbols in proofs are not compiled. Keep
    # the symbols whose names are referred to.
    
    all_names = set()
    for x in mod.proofs:
        x[1].vocab(all_names)
    
    all_syms = set(lu.used_symbols_asts(asts))

    if opt_keep_destructors.get():
        for sym in list(all_syms):
            collect_relevant_destructors(sym,all_syms,set())
    
    if filter_symbols.get() or cone_of_influence.get():
        old_syms = list(mod.sig.all_symbols())
        for sym in old_syms:
            if sym not in all_syms and sym.name not in all_names:
                mod.sig.remove_symbol(sym)

    # check that any properties have dependencies present

    if enforce_axioms.get():
        all_syms_norm = map(ivy_logic.normalize_symbol,all_syms)
        for p,ds in prop_deps:
            for d in ds:
                if not startswith_eq_some(d,present,mod):
                    for x in lu.used_symbols_ast(p.formula):
                        if ivy_logic.normalize_symbol(x) in all_syms_norm:
                            raise iu.IvyError(p,"property {} depends on abstracted object {}"
                                              .format(pname(p),d))

#    for x,y in new_actions.iteritems():
#        print iu.pretty(ia.action_def_to_str(x,y))


    #check non-interference (temporarily put back in old_actions)

    if do_check_interference.get():
        interf_syms = set(x for x in ivy_logic.all_symbols() if x in all_syms)
        follow_definitions(orig_defs,interf_syms)
        save_new_actions = mod.actions
        mod.actions = old_actions
        check_term = enforce_axioms.get() and iu.version_le("1.7",iu.get_string_version())
        check_interference(mod,new_actions,summarized_actions,impl_mixins,check_term,interf_syms,
                           after_inits,all_after_inits)
        mod.actions = save_new_actions

    # filter the sorts

    if filter_symbols.get() or cone_of_influence.get():
        all_sorts = set()
        def add_deps(s):
            if s not in all_sorts:
                all_sorts.add(s)
                for x in im.sort_dependencies(mod,s):
                    add_deps(x)
        for sym in all_syms:
            sort = sym.sort
            if isinstance(sort,ivy_logic.FunctionSort):
                for s in sort.dom:
                    add_deps(s.name)
                add_deps(sort.rng.name)
            else:
                add_deps(sort.name)
        for s in isolate.params():
            if s.sort not in mod.sig.sorts:
                raise iu.IvyError(isolate,"bad type {} in isolate parameter".format(s.sort))
            add_deps(s.sort)
        old_sorts = list(mod.sig.sorts.keys())
        for sort in old_sorts:
            if sort not in all_sorts and sort != 'bool':
                del mod.sig.sorts[sort]
        mod.sort_order = [s for s in mod.sort_order if s in mod.sig.sorts]
        old_destrs = list(mod.sort_destructors.keys())
        for destr in old_destrs:
            if destr not in all_sorts:
                del mod.sort_destructors[destr]
        old_destrs = list(mod.destructor_sorts.keys())
        for destr in old_destrs:
            if mod.destructor_sorts[destr].name not in all_sorts:
                del mod.destructor_sorts[destr]



    # check that native code does not occur in an untrusted isolate

    if type(isolate) == ivy_ast.IsolateDef and isolate_mode.get() != 'test':
        for action in mod.actions.values():
            if isinstance(action,ia.NativeAction):
                raise iu.IvyError(action,'trusted code used in untrusted isolate')
        for ldf in mod.definitions:
            if isinstance(ldf.formula.args[1],ivy_ast.NativeExpr):
                raise iu.IvyError(action,'trusted code used in untrusted isolate')


    # TODO: need a better way to filter signature
    # new_syms = set(s for s in mod.sig.symbols if keep_sym(s))
    # for s in list(mod.sig.symbols):
    #     if s not in new_syms:
    #         del mod.sig.symbols[s]



    # strip the isolate parameters

    strip_isolate(mod,isolate,impl_mixins,all_after_inits,extra_strip)

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
        implements = [m for m in mixins if isinstance(m,ivy_ast.MixinImplementDef)]
        if len(implements) > 1:
            raise iu.IvyError(implements[1],'Multiple implementations for {}'.format(action))
        mixins = [m for m in mixins if not isinstance(m,ivy_ast.MixinImplementDef)]
        mixers = iu.topological_sort(list(iu.unique(m.mixer() for m in mixins)),arcs)
        keymap = dict((x,y) for y,x in enumerate(mixers))
        key = lambda m: keymap[m.mixer()]
        before = sorted([m for m in mixins if isinstance(m,ivy_ast.MixinBeforeDef)],key=key)
        after = sorted([m for m in mixins if isinstance(m,ivy_ast.MixinAfterDef)],key=key)
#        order = SortOrder(arcs)
#        before = sorted([m for m in mixins if isinstance(m,ivy_ast.MixinBeforeDef)],order)
#        after = sorted([m for m in mixins if isinstance(m,ivy_ast.MixinAfterDef)],order)
        before.reverse() # add the before mixins in reverse order
        mixins = implements + before + after
#        print 'mixin order for action {}:'
#        for m in mixins:
#            print m.args[0]
        mod.mixins[action] = mixins
        

ext_action = iu.Parameter("ext",None)

def hide_action_params(action):
    params = action.formal_params + action.formal_returns
    res = ia.LocalAction(*(params + [action]))
    return res

def get_cone(actions,action_name,cone):
    if action_name not in cone:
#        print '({} '.format(action_name)
        cone.add(action_name)
        for a in actions[action_name].iter_subactions():
            if isinstance(a,ia.CallAction):
                get_cone(actions,a.callee(),cone)
            elif isinstance(a,ia.NativeAction):
                for arg in a.args[1:]:
                    if isinstance(arg,ivy_ast.Atom):
                        n = arg.relname
                        if n in actions:
                            get_cone(actions,n,cone)
#        print ')'
            
# Get the names of the actions that accessible from a given set of
# roots (normally the exported actions). An action is accessible if
# if is a root, or is referenced from native code, or is called in
# an intializer. 

def get_mod_cone(mod,actions=None,roots=None,after_inits=[]):
    actions = actions if actions is not None else mod.actions
    roots = roots if roots is not None else mod.public_actions
    cone = set()
    for a in roots:
        get_cone(actions,a,cone)
    for n in mod.natives:
        for a in n.args[2:]:
            if isinstance(a,ivy_ast.Atom) and a.rep in mod.actions:
                get_cone(actions,a.rep,cone)
    for ai in after_inits:
        get_cone(actions,ai,cone)
    return cone

def loop_action(action,mod):
    subst = dict((p,ivy_logic.Variable('Y'+p.name,p.sort)) for p in action.formal_params)
    action = lu.substitute_constants_ast(action,subst)
    ia.type_check_action(action,mod) # make sure all is legal
    return action

def fix_initializers(mod,after_inits):
        things = set()
        for m in after_inits:
            name = m.mixer()
            extname = 'ext:'+name
            action = mod.actions[extname] if extname in mod.actions else mod.actions.get(name,None)
            if action == None or not ia.has_code(action):
                continue
            mod.initializers.append((name,loop_action(action,mod)))
            if name in mod.actions:
                del mod.actions[name]
            if name in mod.public_actions:
                mod.public_actions.remove(name)
            if extname in mod.actions:
                del mod.actions[extname]
            if extname in mod.public_actions:
                mod.public_actions.remove(extname)
            things.add(name)
            things.add(extname)
        ais = set(m.mixer() for m in after_inits)
        mod.exports = [e for e in mod.exports if e.exported() not in ais]
        mod.isolate_info.implementations = [(impl,actname,action) for impl,actname,action in mod.isolate_info.implementations
                                            if actname not in things]

def set_up_implementation_map(mod):
    global implementation_map
    implementation_map = {}
    for actname,ms in mod.mixins.iteritems():
        implements = [m for m in ms if isinstance(m,ivy_ast.MixinImplementDef)]
        for m in implements:
            implementation_map[m.mixee()] = m.mixer()


def conj_to_assume(c):
    res = ia.AssumeAction(c.formula)
    res.lineno = c.lineno
    return res

def bracket_action_int(mod,actname,before,after):
    if actname in mod.actions:
        action = mod.actions[actname]
        thing = empty_clone(action)
        thing.args.extend(before+[action]+after)
        mod.actions[actname] = thing

def bracket_action(mod,actname,before,after):
    bracket_action_int(mod,actname,before,after)
    bracket_action_int(mod,'ext:'+actname,before,after)

def apply_present_conjectures(isol,mod):
    if not assume_invariants.get():
        return []
    brackets = []
    conjs = get_isolate_conjs(mod,isol,verified=False)
    mod.assumed_invariants = list(conjs)
    conjs = [c for c in conjs if not c.explicit]
    cg = mod.call_graph()  # TODO: cg should be cached
    myexports = get_isolate_exports(mod,cg,isol)
    for actname in myexports:
        assumes = map(conj_to_assume,conjs)
        brackets.append((actname,assumes,[]))
    posts = defaultdict(list)
    for conj in conjs:
        for actname in mod.conj_actions[conj.label.rep]:
            if actname not in myexports:
                posts[actname].append(conj_to_assume(conj))
    for actname,assumes in posts.iteritems():
        brackets.append((actname,[],assumes))
    return brackets

def create_isolate(iso,mod = None,**kwargs):

        mod = mod or im.module

        # from version 1.7, if no isolate specified on command line and
        # there is only one, use it.
        if iso is None and iu.version_le("1.7",iu.get_string_version()):
            isos = list(mod.isolates)
            if len(isos) == 1:
                iso = isos[0]
            
        if iso is not None:
            check_with_parameters(mod,iso)

        # Apply the present conjectures
        if iso and iso in mod.isolates and iu.version_le("1.7",iu.get_string_version()):
            brackets = apply_present_conjectures(mod.isolates[iso],mod)

        # treat initializers as exports
        after_inits = mod.mixins["init"]
        del  mod.mixins["init"]
        mod.exports.extend(ivy_ast.ExportDef(ivy_ast.Atom(a.mixer()),ivy_ast.Atom('')) for a in after_inits)

        # check all mixin declarations

        for name,mixins in mod.mixins.iteritems():
            for mixin in mixins:
                with ASTContext(mixin):
                    action1,action2 = (lookup_action(mixin,mod,a.relname) for a in mixin.args)

        # check all the delagate declarations

        for dl in mod.delegates:
            lookup_action(dl.args[0],mod,dl.delegated())
            if dl.delegee() and dl.delegee() not in mod.hierarchy:
                raise iu.IvyError(dl.args[1],"{} is not an object".format(dl.args[1]))

        # check all the export declarations
        for exp in mod.exports:
            expname = exp.args[0].rep
            if expname not in mod.actions:
                raise iu.IvyError(exp,"undefined action: {}".format(expname))

        # create the import actions, if requested

        orig_exports = set(e.exported() for e in mod.exports)
        orig_imports = set(e.imported() for e in mod.imports)

        extra_with = []
        extra_strip = {}
        if create_imports.get():
            set_up_implementation_map(mod)
            newimps = []
            outcalls = set()
            for imp in mod.imports:
                if imp.args[1].rep == '':
                    impname = imp.args[0].rep
                    if impname not in mod.actions:
                        raise iu.IvyError(imp,"undefined action: {}".format(impname))
                    action = mod.actions[impname]
                    if not(type(action) == ia.Sequence and not action.args):
                        raise iu.IvyError(imp,"cannot import implemented action: {}".format(impname))
                    outcalls.add(impname)
                else:
                    newimps.append(imp)

            if iso and iso in mod.isolates:
                isolate = mod.isolates[iso]
                verified,present = get_isolate_info(mod,isolate,'impl')
                save_privates = mod.privates
                set_privates(mod,isolate)
                verified_actions = set(a for a in mod.actions if vstartswith_eq_some(a,verified,mod))
                present_actions = set(a for a in mod.actions if startswith_eq_some(a,present,mod))
                present_actions.update(verified_actions)
                mod.privates = save_privates
                for actname in present_actions:
                    for called in im.module.actions[actname].iter_calls():
                        if called not in present_actions:
                            outcalls.add(called)
            for name in outcalls:
                impname = name
                extname = 'imp__' + impname
                if impname in implementation_map:
                    impname = implementation_map[impname]
                action = im.module.actions[impname]
                call = ia.CallAction(*([ivy_ast.Atom(extname,action.formal_params)] + action.formal_returns))
                call.formal_params = action.formal_params
                call.formal_returns = action.formal_returns
                call.lineno = action.lineno
                mod.actions[impname] = call
                mod.actions[extname] = action
                if name in orig_imports or not(iso and iso in mod.isolates
                                               and isinstance(mod.isolates[iso],ivy_ast.ExtractDef)):
                    newimps.append(ivy_ast.ImportDef(ivy_ast.Atom(extname),ivy_ast.Atom('')))
                    extra_with.append(ivy_ast.Atom(impname))
#                    extra_with.append(ivy_ast.Atom(extname))
                if iso and iso in mod.isolates and name in orig_imports:
                    ps = mod.isolates[iso].params()
                    extra_strip[impname] = [a.rep for a in ps]
                    extra_strip[extname] = [a.rep for a in ps]
            mod.imports = newimps

        mixers = set()
        for ms in mod.mixins.values():
            for m in ms:
                mixers.add(m.mixer())

        # Determine the mixin order (as a side effect on module.mixins)

        get_mixin_order(iso,mod)

        # Construct an isolate

        if iso:
            isolate_component(mod,iso,extra_with=extra_with,extra_strip=extra_strip,
                              after_inits=set(a.mixer() for a in after_inits))
        else:
            if mod.isolates and cone_of_influence.get():
                raise iu.IvyError(None,'no isolate specified on command line')
            # apply all the mixins in no particular order
            mod.isolate_info = im.IsolateInfo()
            implemented = set()
            for name,mixins in mod.mixins.iteritems():
                for mixin in mixins:
                    action1,action2 = (lookup_action(mixin,mod,a.relname) for a in mixin.args)
                    mixed_name = mixin.args[1].relname
                    if mixed_name in orig_exports and isinstance(mixin,ivy_ast.MixinBeforeDef):
                        action1 = action1.assert_to_assume([ia.AssertAction])
                    mixed = ia.apply_mixin(mixin,action1,action2)
                    mod.actions[mixed_name] = mixed
                    triple = (mixin.mixer(),mixin.mixee(),mod.actions[mixin.mixer()])
                    if isinstance(mixin,ivy_ast.MixinImplementDef):
                        mod.isolate_info.implementations.append(triple)
                        implemented.add(mixin.mixee())
                    else:
                        mod.isolate_info.monitors.append(triple)
                    implemented.add(mixin.mixer())
            for actname,action in mod.actions.iteritems():
                if actname not in implemented:
                    mod.isolate_info.implementations.append((actname,actname,action))
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


        for name in mod.public_actions:
            mod.actions[name].label = name
        ext = kwargs['ext'] if 'ext' in kwargs else ext_action.get()
        if ext is not None:
            ais = set(m.mixer() for m in after_inits)
            ext_acts = [mod.actions[x] for x in sorted(mod.public_actions) if canon_act(x) not in ais]
            ext_act = ia.EnvAction(*ext_acts)
            mod.public_actions.add(ext);
            mod.actions[ext] = ext_act;

        # Check native interpretations of symbols

        slv.check_compat()

        # Make concept spaces from the conjecture

        mod.update_conjs()

        # get rid of useless actions

        cone = get_mod_cone(mod)        
        if cone_of_influence.get():
            for a in list(mod.actions):
                if a not in cone:
                    del mod.actions[a]
        else:
            if pedantic.get():
                for a in list(mod.actions):
                    if a not in cone and not a.startswith('ext:') and a not in mixers:
                        ea = 'ext:' + a
                        if ea in mod.actions and ea not in cone:
                            if ia.has_code(mod.actions[a]) and not mod.actions[a].lineno.filename.startswith('/'):
                                iu.warn(mod.actions[a],"action {} is never called".format(a))
            if iso and isinstance(mod.isolates[iso],ivy_ast.ExtractDef):
                for a in sorted(mod.public_actions):
                    anorm = a[4:] if a.startswith('ext:') else a
                    if anorm not in orig_exports:
                        iu.warn(mod.actions[a],"action {} is implicitly exported".format(anorm))
                    

        fix_initializers(mod,after_inits)

        mod.canonize_types()

        # Apply the present conjectures
        if iso and iso in mod.isolates and iu.version_le("1.7",iu.get_string_version()):
            for actname,before,after in brackets:
                bracket_action(mod,actname,before,after)

        mod.isolate_proof = mod.isolate_proofs[iso] if iso in mod.isolate_proofs else None

        # show the compiled code if requested

        if show_compiled.get():
            ivy_printer.print_module(mod)


def has_assertions(mod,callee):
    assert callee in mod.actions, callee
    return any(isinstance(action,ia.AssertAction) for action in mod.actions[callee].iter_subactions())

def has_requires(mod,callee):
    assert callee in mod.actions, callee
    return any(isinstance(action,ia.RequiresAction) for action in mod.actions[callee].iter_subactions())

def find_some_assertion(mod,actname,kind=None):
    for action in mod.actions[actname].iter_subactions():
        if isinstance(action, kind if kind is not None else ia.AssertAction):
            return action
    return None

def find_some_call(mod,actname,callee):
    for action in mod.actions[actname].iter_subactions():
        if isinstance(action,ia.CallAction) and action.callee() == callee:
            return action
    return None

def check_isolate_completeness(mod = None):
    mod = mod or im.module
    checked = set()
    checked_props = set()
    checked_context = defaultdict(set) # maps action name to set of delegees
    delegates = set(s.delegated() for s in mod.delegates if not s.delegee())
    delegated_to = dict((s.delegated(),s.delegee()) for s in mod.delegates if s.delegee())


    # delegate all the stub actions to their implementations
    global implementation_map
    implementation_map = {}
    impl_mixins = defaultdict(list)
    for actname,ms in mod.mixins.iteritems():
        implements = [m for m in ms if isinstance(m,ivy_ast.MixinImplementDef)]
        impl_mixins[actname].extend(implements)
        for m in implements:
            for foo in (m.mixee(),m.mixer()):
                if foo not in mod.actions:
                    raise IvyError(m,'action {} not defined'.format(foo))
            implementation_map[m.mixee()] = m.mixer()
    
    for iso_name,isolate in mod.isolates.iteritems():
        verified,present = get_isolate_info(mod,isolate,'impl')
        save_privates = mod.privates
        set_privates(mod,isolate)
        verified_actions = set(a for a in mod.actions if vstartswith_eq_some(a,verified,mod))
        present_actions = set(a for a in mod.actions if startswith_eq_some(a,present,mod))
        mod.privates = save_privates

        for a in verified_actions:
            if a not in delegates:
                checked.add(a)
        for a in present_actions:
            checked_context[a].update(verified_actions)
        # for prop in mod.labeled_props:
        #     if prop.label:
        #         label = prop.label.relname
        #         if startswith_eq_some(label,verified,mod):
        #             checked_props.add(label)
        proved,not_proved = get_props_proved_in_isolate(mod,isolate)
        for prop in proved:
            if prop.label:
                label = prop.label.relname
                checked_props.add(label)
            
    missing = []
    trusted = set()
    for n in mod.natives:
        lbl = n.args[0]
        if lbl:
            trusted.add(lbl.rep)
            
    for actname,action in mod.actions.iteritems():
        if startswith_eq_some(actname,trusted,mod):
            continue
        for callee in action.iter_calls():
            if not (callee in checked or not has_assertions(mod,callee)
                    or callee in delegates and actname in checked_context[callee]):
                missing.append((actname,callee,None))
            if has_requires(mod,callee) and not actname in checked_context[callee]:
                missing.append((actname,callee,ia.RequiresAction))
            for mixin in mod.mixins[callee]:
                mixed = mixin.args[0].relname
                if has_requires(mod,mixed):
                    verifier = implementation_map.get(actname,actname)
                    if verifier not in checked_context[mixed]:
                        missing.append((actname,mixin,ia.RequiresAction))
                if not has_assertions(mod,mixed) or isinstance(mixin,ivy_ast.MixinImplementDef):
                    continue
                if not isinstance(mixin,ivy_ast.MixinBeforeDef) and startswith_eq_some(callee,trusted,mod):
                    continue
                verifier = actname if isinstance(mixin,ivy_ast.MixinBeforeDef) else callee
                verifier = implementation_map.get(verifier,verifier)
                if verifier not in checked_context[mixed]:
                    missing.append((actname,mixin,None))
    for e in mod.exports:
        if e.scope(): # global export
            continue
        callee = e.exported()
        if not (callee in checked or not has_assertions(mod,callee) or actname in delegates):
            missing.append(("external",callee,None))
        for mixin in mod.mixins[callee]:
            mixed = mixin.args[0].relname
            if has_assertions(mod,mixed) and not isinstance(mixin,ivy_ast.MixinBeforeDef):
                if callee not in checked_context[mixed]:
                    missing.append(("external",mixin,None))
                
    if missing:
        for x,y,z in missing:
            mixer = y.mixer() if isinstance(y,ivy_ast.MixinDef) else y
            mixee = y.mixee() if isinstance(y,ivy_ast.MixinDef) else y
            print iu.IvyError(find_some_assertion(mod,mixer,kind=z),"assertion is not checked")
            if mixee != mixer:
                print iu.IvyError(mod.actions[mixee],"...in action {}".format(mixee))
            if x == "external":
                print "error: ...when called from the environment"
            else:
                print iu.IvyError(find_some_call(mod,x,mixee),"...when called from {}".format(x))
    
    done = set()
    for prop in mod.labeled_props:
        if prop.label:
            label = prop.label.relname
            if label not in checked_props and label not in done:
                print iu.IvyError(prop,"property {} not checked".format(label))
                missing.append((label,None,None))
                done.add(label)
        
    return missing


# Iterate over all the components of and isolate iso in module mod,
# applying a function fun. If verified is true, include the verified
# components. If present is true, include the the present components.
#
# This is a little tricky, because of sub-isolates. That is, a sub-isolate
# is considered to be 'present', not 'verified'. 
#
# Note that a component may be touched more that once if there are
# redundant entries in the isolate's 'verified' or 'present' list.


def iter_isolate(mod,iso,fun,verified=True,present=True):
    suff = "spec" if isinstance(iso,ivy_ast.ExtractDef) else "impl"

    # Record all the isolate roots, so we can detect sub-isolates

    vp = set()
    for isol in mod.isolates.values():
        for v in isol.verified():
            vp.add(v.rep)
            
    # Iterate over all the public (non-strict) descendants of a root 'name'.
    # The parameter 'in_sub' indicidates that we are in a 'present' component.
    # This parameter is set when we descend into a sub-isolate.

    def recur(name, in_sub=False):
        if (present if in_sub else verified):
            fun(name)
        assert not isinstance(name,ivy_ast.This)
        if name in mod.hierarchy:
            for child in mod.hierarchy[name]:
                cname = iu.compose_names(name,child)
                if not in_sub or not(child == suff
                       or iu.compose_names(cname,suff) in mod.attributes
                       or iu.compose_names(cname,'private') in mod.attributes):
                    recur(cname, in_sub or cname in vp)
        
    for ver in iso.verified():
        recur(ver.rep)

    if present:
        for pres in iso.present():
            recur(pres.rep,True)
    

# Get the set of actions present in an isolate. 

def get_isolate_actions(mod,iso):
    actions = set()
    def fun(name):
        if name in mod.actions:
            actions.add(name)
    iter_isolate(mod,iso,fun)
    return actions

def get_isolate_lfs(mod,iso,lfs,verified=True,present=True):
    lf_map = dict((lf.label.rep,lf) for lf in lfs)
    memo = set()
    lfs = []
    def fun(name):
        if name in lf_map:
            if name not in memo:
                lfs.append(lf_map[name])
            memo.add(name)
    iter_isolate(mod,iso,fun,verified,present)
    return lfs


def get_isolate_conjs(mod,iso,verified=True,present=True):
    return get_isolate_lfs(mod,iso,mod.labeled_conjs,verified,present)


def get_isolate_exports(mod,cg,iso):
    actions = get_isolate_actions(mod,iso)
    mod_exports = set(exp.exported() for exp in mod.exports)
    exports = set(act for act in actions if act in mod_exports
                  or any((x not in actions) for x in cg[act]))
    return exports

# This creates a map that takes each name in the hierarchy to
# a list of the isolates in which it is present/verified

def get_isolate_map(mod,verified=True,present=True):
    res = defaultdict(list)
    for ison,isol in mod.isolates.iteritems():
        def fun(name):
            res[name].append(ison)
        iter_isolate(mod,isol,fun,verified,present)
    return res

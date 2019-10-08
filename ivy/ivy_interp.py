#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Symbolic interpreter for Ivy
"""

import sys
import z3
import string
from collections import defaultdict

from ivy_logic import *
from ivy_logic_utils import *
from ivy_solver import unsat_core, clauses_imply, clauses_imply_formula, clauses_imply_list, clauses_model_to_clauses, clauses_model_to_diagram, get_model_clauses
from ivy_transrel import compose_state_action, forward_interpolant, reverse_image, interpolant, \
    join_state, implies_state, ActionFailed, null_update, forward_image, reverse_interpolant_case, \
    is_skolem, interpolant_case, History, top_state, action_failure
from ivy_actions import type_check,Action,RME
import ivy_ast as ia
import ivy_actions
import ivy_transrel as tr
import ivy_utils as iu
import ivy_module as im
import ivy_solver as islvr
  
def type_check_list(domain,l):
    for x in l:
        if isinstance(x,list):
            type_check_list(domain,x)
        else:
            type_check(domain,x)

Interp = im.Module

def module_type_check(self):
#        type_check_list(self,[y for x,y in self.concepts]) 
#        for a in self.axioms:
#            print "axiom: {}".format(a)
    type_check_list(self,self.axioms)
#        type_check_list(self,self.updates)
#        type_check_list(self,[y for x,y in self.schemata.iteritems()])
    self.type_check_concepts()



def module_type_check_concepts(self):
    # tricky because we must consider concepts as relations
    relations = self.relations
    self.relations = dict(relations.iteritems())
    self.relations.update((x.rep,len(x.args)) for x,y in self.concept_spaces)
    type_check_list(self,[y for x,y in self.concept_spaces])
    self.relations = relations

def module_new_state(self, clauses):
    if isinstance(clauses,Clauses) and clauses.annot is None:
        clauses = Clauses(clauses.fmlas,clauses.defs,ivy_actions.EmptyAnnotation())
    return State(self, clauses)

def module_new_state_with_value(self, value):
    res = State(self)
    res.value = value
    return res

def module_order(self,state1, state2):
    """True if state1 is a subset of state2 """
    axioms = self.background_theory(state1.in_scope) 
    return implies_state(state1.value,state2.value,axioms,self.relations)

def module_skolemizer(self):
    rn = UniqueRenamer('',self.functions)
    return lambda v, rn=rn: var_to_constant(v,rn())

im.Module.type_check = module_type_check
im.Module.type_check_concepts = module_type_check_concepts
im.Module.new_state = module_new_state
im.Module.new_state_with_value = module_new_state_with_value
im.Module.skolemizer = module_skolemizer
im.Module.order = module_order

class State(object):
    def __init__(self, domain = None, value = None, expr = None, label = None):
        """An abstract state.
        """
        if value == None:
            value = top_state()
        if domain == None:
            domain = im.module
        self.in_scope = {}        # symbols in scope in this state TODO: obsolete
        self.domain = domain      # interpreter it belongs to (now this is the module)
        self.moded, self.clauses, self.precond = value if isinstance(value,tuple) else (None,value,false_clauses())
        self.expr = expr
        self.label = label
        self.cached_update = None
        self.cached_pred = None

    @property
    def value(self):
        return (self.moded,self.clauses,self.precond)
    @value.setter
    def value(self,value):
        self.moded, self.clauses, self.precond = value

    # conjectures are currently global for the
    # interpeter, but eventually it should be possible to have different underapprox
    # for each location.

    @property
    def conjs(self):
        if not hasattr(self.domain,'conjs'):
            self.domain.conjs = []
        return self.domain.conjs

    @conjs.setter
    def conjs(self,value):
        self.domain.conjs = value

    # underapproximations (known reachable states) are currently global for the
    # interpeter, but eventually it should be possible to have different underapprox
    # for each location.

    @property
    def unders(self):
        return self.domain.unders

    @unders.setter
    def unders(self,value):
        self.domain.unders = value

    def __repr__(self):
        return repr(clauses_to_formula(self.clauses)) if isinstance(self.clauses,list) else repr(self.clauses)

    __str__ = __repr__

    @property
    def update(self):
        if self.cached_update == None and self.expr != None and is_action_app(self.expr):
            self.cached_update = eval_action(self.expr.rep).update(self.domain,self.in_scope)
        return self.cached_update

    @update.setter
    def update(self,value):
        self.cached_update = value
            
    @property
    def pred(self):
        if self.cached_pred == None and self.expr != None and is_action_app(self.expr):
            self.cached_pred = self.expr.args[0]
        return self.cached_pred

    @pred.setter
    def pred(self,value):
        self.cached_pred = value

    def is_bottom(self):
        return (self.clauses.is_false())

    def to_formula(self):
        return self.clauses.to_formula()

class EvalContext(object):
    """ Context Manager for evaluating states and actions. """
    def __init__(self,check=True):
        self.check = check
    def __enter__(self):
        global context
        self.old_context = context
        context = self
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global context
        context = self.old_context
        return False # don't block any exceptions

context = EvalContext()

def get_core(state,clause):
        """ Check whether a clause is implied by a state. If so,
        return a core (a subset of clauses in the state that implies
        clause) else return None. Clause is assumed to be ground.
        """
        state_clauses = state.clauses
        clauses1 = and_clauses(state_clauses,state.domain.background_theory(state.in_scope))
        clauses2 = [[~lit] for lit in clause]
        return unsat_core(clauses1,clauses2)    

def new_state(value, exact = False, domain = None, expr = None):
#    print "new_state: {}".format(value)
    return ivy_actions.context.new_state(value,exact,domain,expr)

def bottom_state(domain = None):
    return new_state(tr.bottom_state(),exact=True,domain=domain,expr=state_join())

def concrete_post(update, state, expr = None):
    """ Apply an update concretely (compute concrete post). ".
    """
    
    # TODO: axioms could change as scope changes
    axioms = state.domain.background_theory(state.in_scope)
#    print "concrete post: axioms = {}".format(axioms)
    cons = compose_state_action(state.value,axioms,update,check=context.check)
    res = new_state(cons,domain = state.domain,expr=expr)
    # record the pre-state and update for future analysis
    res.pred = state
    res.update = update
    return res

def concrete_join(state1,state2):
    """ Apply an update concretely (compute concrete post). This leaves free symbols
    that are implicitly existentially quantified and are prefixed with "__old".
    """
 
    relations = state1.domain.relations
    value = join_state(state1.value,state2.value,relations)
    res = new_state(value,domain = state1.domain,expr=state_join(state1,state2))
    res.join_of = [state1,state2]
    return res

class UnsatCoreWithInterpolant(Exception):
    def __init__(self,core,interp):
        self.core = core
        self.interp = interp

def reverse_update_concrete_clauses(state,clauses=None):
    """ Reverse an update concretely (compute concrete pre). If unsat,
    throw UnsatCoreWithInterpolant.
    
    """

    assert(state.pred != None and state.update != None) # can't reverse if no predecessor
    if clauses == None:
        clauses = state.clauses
    axioms = state.domain.background_theory(state.in_scope)
    fi = forward_interpolant(state.pred.clauses,state.update,clauses,axioms,state.domain.functions)
    if fi:
        raise UnsatCoreWithInterpolant(*fi)
    return and_clauses(reverse_image(clauses,axioms,state.update), axioms)

def reverse(state,clauses=None):
    """ Reverse an update concretely (compute concrete pre). If unsat,
    throw UnsatCoreWithInterpolant.
    
    """

    assert(state.pred != None and state.update != None) # can't reverse if no predecessor
    if clauses == None:
        clauses = state.clauses
    axioms = state.domain.background_theory(state.in_scope)
    return and_clauses(reverse_image(clauses,axioms,state.update), axioms)

def reverse_join_concrete_clauses(state,join_of,clauses=None):
    if clauses == None:
        clauses = state.clauses
    axioms = state.domain.background_theory(state.in_scope)
    for s in join_of:
        if not clauses_imply(and_clauses(s.clauses,clauses),false_clauses()):
            return (and_clauses(s.clauses,clauses),s)
    pre = or_clauses(*[s.clauses for s in join_of])
    itp = interpolant(pre,clauses,axioms,state.domain.functions)
    if itp:
        raise UnsatCoreWithInterpolant(*itp)
    raise IvyError(None,"decision procedure incompleteness")


def join_unders(state):
    if not hasattr(state,'unders'):
        state.unders = []  # make sure we have this field
    pre = tagged_or_clauses('__pre',*[s.clauses for s in state.unders])  # join the underapproximations
    return pre

def add_under(state,clauses,pred = None, universe=None):
    if not hasattr(state,'unders'):
        state.unders = []  # make sure we have this field
    s = state.domain.new_state(clauses)
    if pred != None:
        s.pred = pred
    if universe != None:
        s.universe = universe
    state.unders.append(s)
    return s

def reach_state(state,clauses=None):
    """ Try to reach a state in one step from it's predecessor's
    underapproximation. If reachable, update the state's
    underapproximation with some known reachable state.  Return the
    reachable state. Else return None.
    """
    if not(state.pred != None and state.update != None):
        return None
    pre = join_unders(state.pred)
    if clauses == None:
        clauses = state.clauses
    print "reach_state: clauses = {}".format(clauses)
    axioms = state.domain.background_theory(state.in_scope)
    img = and_clauses(forward_image(pre,axioms,state.update),axioms,clauses)
    m = get_model_clauses(img)
    ignore = lambda s,d=state.domain: s not in d.relations and s not in d.functions
    if m:
#        print "reach_state model = {}".format(m.model)
        idx = find_true_disjunct(pre,m.eval)
        post = clauses_model_to_clauses(img,ignore,model=m)
        return add_under(state,post,state.unders[idx],dict((s,[c.skolem() for c in m.sort_universe(s)]) for s in m.sorts()))
    return None

def reach_state_from_pred(state,clauses=None):
    """ If state is reachable from its predecessor's
    underapproximation, update its underapproximation with some
    reachable set of states. If not reachable, throw
    UnsatCoreWithInterpolant. In this case, the interpolant is implied
    by the predecessor's underapproximation but cannot reach the
    current state, hence it is a reasonable abductive inference.
    """
    post = reach_state(state,clauses)
    if post != None:
        return post
    ri = reverse_interpolant_case(clauses,state.update,pre,axioms,state.domain.functions)
    if ri:
        raise UnsatCoreWithInterpolant(*ri)
    return None

reach_state_from_pred_no_abduction = reach_state

def case_conjecture(state,clauses):
    """ Conjecture a separator between state underapprox and clauses.
    The separator must be true of all models of the underapprox and
    false in at least one model of clauses.
    """
    pre = join_unders(state)
    axioms = state.domain.background_theory(state.in_scope)
    ri = interpolant_case(pre,clauses,axioms,state.domain.functions)
    if ri != None:
        core,interp = ri
#        print "case_conjecture conj = {}".format(interp)
        state.conjs.append(interp)
    return ri

def diagram(state,clauses,implied=false_clauses(),extra_axioms=None,weaken=True):
    """ Return the diagram of a single model of clauses in state or
    None if clauses are unsat.
    """
    axioms = state.domain.background_theory(state.in_scope)
    if extra_axioms:
        axioms = and_clauses(axioms,extra_axioms)
    under = clauses_model_to_diagram(clauses,is_skolem,implied,axioms=axioms,weaken=weaken)
    return under

def underapproximate_state(state,implied=[[]]):
    if not hasattr(state,'unders'):
        state.unders = []  # make sure we have this field
    axioms = state.domain.background_theory(state.in_scope)
    under = clauses_model_to_clauses(and_clauses(state.clauses,axioms),is_skolem,implied)
    if under != None:
        state.unders.append(self.new_state(under))


def apply_action(ast,action_name,action,state):
    upd = action.update(state.domain,state.in_scope)
    try:
        res = concrete_post(upd,state,action_app(action_name,state))
    except ActionFailed as af:
        raise IvyActionFailedError(ast,action_name,action,state,af.clauses,af.trans)
    res.action = action
    res.action_name = action_name
    return res

def is_action_app(expr):
    return isinstance(expr,ia.Atom) and len(expr.args) == 1

def is_state_join(expr):
    return isinstance(expr,ia.Or)

def action_app(action,arg):
    return ia.Atom(action,[arg])

class fail_action(Action):
    def __init__(self,action):
        self.action = eval_action(action)
        if hasattr(self.action,'lineno'):
            self.lineno = self.action.lineno
    def __str__(self):
        return "fail " + (self.action.label if hasattr(self.action,'label') else str(self.action))
    def update(self,domain,in_scope):
#        print "action_failure action: {}".format(pretty(str(self.action)))
        return action_failure(self.action.update(domain,in_scope))
    def int_update(self,domain,in_scope):
#        print "action_failure action: {}".format(pretty(str(self.action)))
        return action_failure(self.action.int_update(domain,in_scope))
    def decompose(self,pre,post):
        cases = self.action.decompose(pre,post,fail=True)
        res = []
        for pre,acts,post in cases:
            for i in range(len(acts)):
                pref = acts[0:i+1]
                pref[-1] = fail_action(pref[-1])
                res.append((pre,pref,post))
        return res
    def failed_action(self):
        return self.action

def fail_expr(expr):
    return action_app(fail_action(expr.rep),expr.args[0])

def state_join(*args):
    return ia.Or(*args)

def is_state_symbol(expr):
    return isinstance(expr,ia.Atom) and len(expr.args) == 0

def state_equation(lhs,rhs):
    return ia.Definition(lhs,rhs)

def states_state_expr(expr):
    if isinstance(expr,State):
        yield expr
    else:
        for a in expr.args:
            for b in states_state_expr(a):
                yield b

class IvyActionFailedError(IvyError):
    def __init__(self,ast,action_name,action,state,clauses,trans):
        super(IvyActionFailedError,self).__init__(ast,'precondition of "{}" failed'.format(action_name))
        err_state = state.domain.new_state(clauses)
        err_state.pred = state
        err_state.action = action
        err_state.action_name = action_name
        err_state.update = null_update()
#        print "err_state.clauses: {}".format(err_state.clauses)
        self.error_state = err_state
        self.conc = (trans[0],action_name,action,trans[1])

def eval_action(expr):
    if isinstance(expr,Action):
        return expr
    if isinstance(expr,fail_action):
        return fail_action(eval_action(expr.action))
    res = im.module.actions.get(expr,None)
    if res is None:
        raise IvyError(expr,'{} has no value'.format(expr))
    if not isinstance(res,Action):
        raise IvyError(expr,'{} is not an action'.format(expr.rep))
    return res

def eval_state_atom(expr):
    if isinstance(expr,State):
        return expr
    if ia.is_true(expr):
        return ivy_actions.context.new_state(true_clauses(),exact=True)
    if ia.is_true(expr):
        return ivy_actions.context.new_state(false_clauses(),exact=True)
    if is_state_symbol(expr):
        res = ivy_actions.context.get(expr.rep)
        if res is None:
            raise IvyError(expr,'{} has no value'.format(expr))
        if not isinstance(res,State):
            raise IvyError(expr,'{} is not a state'.format(expr.rep))
        return res
    if isinstance(expr,RME):
        req,mod,ens = expr.args
        # for now, ignore arguments and just keep track of symbols
        mod_syms = [a.rep for a in mod] if mod != None else None
        ens_clauses = ens
        req_clauses = Not(req)
        return ivy_actions.context.new_state((mod_syms,ens_clauses,req_clauses),exact=True)        
    assert False

def eval_state(expr):
    if is_state_join(expr):
        return reduce(concrete_join,[eval_state(e) for e in expr.args])
    if is_action_app(expr):
        v = eval_action(expr.rep)
        s = eval_state(expr.args[0])
        return apply_action(expr,expr.rep,v,s)
    return eval_state_atom(expr)

def decompose_action_app(state2,expr):
    assert is_action_app(expr)
    action = eval_action(expr.rep)
    state1 = eval_state(expr.args[0])
    comps = action.decompose(state1.value,state2.value)
#    print "comps:"
#    for comp in comps:
#        for a in comp[1]:
#            print a
#        print ""
    bg = state1.domain.background_theory(state1.in_scope)
    for pre,acts,post in comps:
#        print "pre core: {} ".format(unsat_core(and_clauses(pre[1],bg),true_clauses()))
#        print "post core: {} ".format(unsat_core(and_clauses(post[1],bg),true_clauses()))
        upds = [act.int_update(state1.domain,state1.in_scope) for act in acts]
        h = History(pre)
#        print "h.post: {}".format(h.post)
        for upd in upds:
#            print "upd: {}".format(upd)
            h = h.forward_step(bg,upd)
#            print "h.post: {}".format(h.post)
        h = h.assume(post)
#        print "h.post: {}".format(h.post)
        bmc_res = h.satisfy(bg)
        if bmc_res == None:
            continue
        universe,path = bmc_res
        states = []
        for i,value in enumerate(path):
#            print "core: {} ".format(unsat_core(and_clauses(value[1],bg),true_clauses()))
            state = new_state(value)
            if i != 0:
                state.expr = action_app(acts[i-1],states[-1])
                state.update = upds[i-1]
                state.pred = states[-1]
            state.label = None
            state.universe = universe
            states.append(state)
        return state
    return None


def eval_state_facts(expr):
    if is_state_join(expr):
        args = [eval_state_facts(e) for e in expr.args]
        args = [e for e in args if e is not None]
        return reduce(concrete_join, args) if args else None
    if is_action_app(expr):
        v = eval_action(expr.rep)
        s = eval_state_facts(expr.args[0])
        return apply_action(expr,expr.rep,v,s) if s is not None else None
    if is_state_symbol(expr):
        return None
    return eval_state_atom(expr)

def eval_state_actions(expr,pre):
    if is_state_join(expr):
        args = [eval_state_actions(e,pre) for e in expr.args]
        return [e for es in args for e in es]
    if is_action_app(expr):
        if is_state_symbol(expr.args[0]) and expr.args[0].rep == pre.label:
            return [action_app(expr.rep,pre)]
    return []

# TODO: this should be replaced by "order", but for now a state
# cannot contain a formula.

def state_implies_formula(state1, fmla2):
    clauses1 = and_clauses(state1.clauses + state1.domain.background_theory(state1.in_scope))
    return clauses_imply_formula(clauses1,fmla2)

def undecided_conjectures(state1):
    clauses1 = and_clauses(state1.clauses,state1.domain.background_theory(state1.in_scope))
    truths = clauses_imply_list(clauses1,state1.conjs)
    return [c for c,t in zip(state1.conjs,truths) if not t]
#    return [c for c in state1.conjs if not clauses_imply(clauses1,c)]

def false_properties(reporter= None):
    axioms = im.background_theory()
    props = [x for x in im.module.labeled_props if not x.temporal]
    subgoalmap = dict((x.id,y) for x,y in im.module.subgoals)
    aas = ([islvr.Assume(axioms)]
           + [(islvr.Assume if prop.id in subgoalmap else islvr.Assert)
              (formula_to_clauses(prop.formula),prop) for prop in props])
    truths = islvr.check_sequence(aas,reporter)
    return [c for c,t in zip(props,truths[1:]) if not t]
#    return [c for c in state1.conjs if not clauses_imply(clauses1,c)]

def get_property_context(prop):
    res = true_clauses()
    subgoalmap = dict((x.id,y) for x,y in im.module.subgoals)
    for x in im.module.labeled_props:
        if x.id == prop.id:
            break
        if x.id in subgoalmap:
            res = and_clauses(res,formula_to_clauses(x.formula))
    return res

def filter_conjectures(state1,model):
    keep = []
    lose = []
    for c in state1.conjs:
        if clauses_imply(model,c):
            keep.append(c)
        else:
            lose.append(c)
    state1.conjs = keep
    return lose

def new_history(state):
    return History(state.value)

def history_forward_step(history,state):
    action = state.expr.rep if state.expr != None and is_action_app(state.expr) else None
    return history.forward_step(state.pred.domain.background_theory(state.pred.in_scope),state.update,action)

def history_satisfy(history,state,_get_model_clauses=None,final_cond=None):
    return history.satisfy(
        state.domain.background_theory(state.in_scope),
        _get_model_clauses,
        final_cond
    )
    
def eval_assert_rhs(rhs,domain):
    if not isinstance(rhs,ivy_actions.RME):
        rhs = ivy_actions.RME(And(),None,rhs)
    # create the state in a temporary action context
    with ivy_actions.ActionContext(domain):
        return eval_state(rhs)

def eval_state_order(lhs,rhs):
#    print "lhs = {}".format(lhs)
#    print "rhs = {}".format(rhs)
    state = eval_state(lhs)
    if is_state_join(rhs):
        return any(state.domain.order(state,eval_state(r)) for r in rhs.args)
    return state.domain.order(state,eval_state(rhs))

def check_state_assertion(state,assertion):
    if not hasattr(state,'label'): return True
    if state.label != assertion.args[0].rep: return True
    rhs = assertion.args[1]
    rhs_state = eval_assert_rhs(rhs,state.domain)
#    print "state: %s" %  state.clauses
#    print "rhs_fmla: {}".format(rhs_state.value)
    return state.domain.order(state,rhs_state)

def get_state_assertions(state):
    res = true_clauses()
    if not hasattr(state,'label'): return res
    for assertion in im.module.assertions:
        if state.label == assertion.args[0].rep:
            rhs = assertion.args[1]
            rhs_state = eval_assert_rhs(rhs,state.domain)
            res = and_clauses(res,rhs_state[1])
#    print "state: %s" %  state.clauses
#    print "rhs_fmla: {}".format(rhs_state.value)
    return None if res.is_true() else res

def top_alpha(state):
    state.clauses = true_clauses()

def universe_constraint(state):
    if hasattr(state,'universe'):
        return Clauses([Or(*[Equals(Variable('X',s),v) for v in state.universe[s]]) for s in state.universe])
    return true_clauses()

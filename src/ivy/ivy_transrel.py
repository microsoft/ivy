#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
""" Functions for manipluating transition relations as two-vocabulary formulas

Updates represent the semantics of actions and states.  Both kinds of
updates have a set of modified symbols. The difference is that action
style uses "new" versions of the symbols to represent the post-state,
while state style uses "old" version to represent the pre-state. In a
"pure" state, the modifies set is "all" and the "old" symbols are not
referred to. That is, a pure state says nothing about the initial
condition. On the other hand, the state of a procedure is
"impure". The initial state of a procedure has an empty modifies set,
meaning mean the current values are all equal to the initial values.

An update is represented as a triple (mod,tr,pre) where mod is a list
of modified symbols (or "all") and tr is a two-vocabulary transition
relation, and pre is a one-vocabulary precondition. The precondition
is stated in the negative, so that an action *fails* in a state s if
st /\ axioms /\ pre is satisfiable. The tr and pre are both implicitly
existentially quantified over the skolem symbols.

Because pre is negative, we say that an action a = (mod_a,tr_a,pre_a)
*refines* (is a safe replacement for) an action b = (mod_b,tr_b,pre_b)
when pre_a => pre_b and frame(mod_a) /\ tr_a => frame(mod_b) /\
tr_b. Here, frame(S), where S is a set of symbols, is the condition
that all symbols *not* in S are preserved.

"""

from ivy_utils import UniqueRenamer, union_to_list, list_union, list_diff, IvyError, inverse_map, compose_maps, pretty
from ivy_logic import Variable, Constant, Literal, Atom, Not, And, Or,App, RelationSort, Definition, is_prenex_universal
from ivy_logic_utils import used_symbols_clauses, rename_clauses, clauses_using_symbols, simplify_clauses,\
    used_variables_clauses, used_constants_clauses, substitute_constants_clause, substitute_constants_clauses, constants_clauses,\
    relations_clauses, eq_lit, condition_clauses, or_clauses, and_clauses, false_clauses, true_clauses,\
    formula_to_clauses, clauses_to_formula, formula_to_clauses_tseitin, is_ground_clause, \
    relations_clause, Clauses, sym_inst, negate_clauses, negate
from ivy_solver import unsat_core, clauses_imply, clauses_imply_formula, clauses_sat, clauses_case, get_model_clauses, clauses_model_to_clauses, get_small_model
import ivy_logic
import ivy_logic_utils as lu
import ivy_utils as iu
from logic_util import is_tautology_equality


def new(sym):
    """ Return the "new" version of symbol "sym", that is, the one
    representing "sym" in the post_state.
    """
    return sym.prefix('new_')

def is_new(sym):
    return sym.startswith('new_')

def new_of(sym):
    return sym.drop_prefix('new_')

def old(sym):
    """ Return the "old" version of symbol "sym", that is, the one
    representing "sym" in the pre_state.
    """
    return sym.prefix('old_')

def is_old(sym):
    return sym.startswith('old_')

def old_of(sym):
    return sym.drop_prefix('old_')

def rename(sym,rn):
    return sym.rename(rn)

def is_skolem(sym):
    """
    Symbols with __ in them in the TR are considerd to be implicitly existentially quantified.
    """
    return sym.contains('__')

def null_update():
    return ([],true_clauses(),false_clauses())

def pure_state(clauses):
    return (None,clauses,false_clauses())

def is_pure_state(state):
    return state[0] == None

def top_state():
    return pure_state(true_clauses())

def bottom_state():
    return pure_state(false_clauses())

def state_postcond(state):
    return state[1]

def state_precond(state):
    return state[2]

def state_to_action(update):
    """ convert from the "state" style to the "action" style """
    updated,postcond,pre = update
    postcond,pre = clausify(postcond), clausify(pre)
    renaming = dict()
    for s in updated:
        renaming[s] = new(s)
    for s in used_symbols_clauses(postcond):
        if is_old(s):
            renaming[s] = old_of(s)
    return (updated,rename_clauses(postcond,renaming),pre)

def action_to_state(update):
    """ convert from the "action" style to the "state" style """
    updated,tr,pre = update
    renaming = dict()
    for s in updated:
        renaming[s] = old(s)
    for s in used_symbols_clauses(tr):
        if is_new(s):
            renaming[s] = new_of(s)
    return (updated,rename_clauses(tr,renaming),pre)

def update_frame_constraint(update,relations):
    """ Return a clause list constraining all updated symbols
    to keep their previous values """
    clauses = []
    for sym in update[0]:
        if sym in relations:
            arity = relations[sym]
            vs = [Variable("V{}".format(i)) for i in range(0,arity)]
            lit1 = Literal(1,Atom(sym,vs))
            lit2 = Literal(1,Atom(new(sym),vs))
            clauses += [[~lit1,lit2],[lit1,~lit2]]
        else:
            clauses.append([eq_lit(Constant(sym),Constant(new(sym)))])
    return Clauses(clauses)


def frame_def(sym,op):
    """ Add the condition that sym remains unchanged to a
    transition relation (using op = {new,old})"""
    lhs = sym_inst(op(sym) if op is new else sym)
    rhs = sym_inst(sym if op is new else op(sym))
    dfn = Definition(lhs,rhs)
    return dfn

def frame(updated,relations,op):
    """ Return a clause list constraining all updated symbols
    to keep their op values, for op = new,old """
    return Clauses([],[frame_def(sym,op) for sym in updated])

def symbol_frame_cond(sym,sig):
    """ Return transition relation implying that sym remains unchanged """
    return Clauses([],[frame_def(sym,new)])

def frame_update(update,in_scope,sig):
    """ Modify an update so all symbols in "in_scope" are on the
    update list, preserving semantics.
    """
    updated,clauses,pre = update
    moded = set(updated)
    dfns = []
    for sym in in_scope:
        if sym not in moded:
            updated.append(sym)
            dfns.append(frame_def(sym,new))
    return (updated,and_clauses(clauses,Clauses([],dfns)),pre)

def diff_frame(updated1,updated2,relations,op):
    if updated1 == None or updated2 == None: return Clauses([])
    updated = list_diff(updated2,updated1)
    return frame(updated,relations,op)

def updated_join(updated1,updated2):
    if updated1 == None or updated1 == None: return None
    return list_union(updated1,updated2)

def join(s1,s2,relations,op):
    u1,c1,p1 = s1
    u2,c2,p2 = s2
    df12 = diff_frame(u1,u2,relations,op)
    df21 = diff_frame(u2,u1,relations,op)
    c1 = and_clauses(c1,df12)
    c2 = and_clauses(c2,df21)
    p1 = and_clauses(p1,df12)
    p2 = and_clauses(p2,df21)
    u = updated_join(u1,u2)
    c = or_clauses(c1,c2)
    p = or_clauses(p1,p2)
    return (u,c,p)

class CounterExample(object):
    def __init__(self,clauses):
        self.clauses = clauses
    def __nonzero__(self):
        return False

def clauses_imply_formula_cex(clauses,fmla):
    if clauses_imply_formula(clauses,fmla):
        return True
    return CounterExample(conjoin(clauses,negate_clauses(formula_to_clauses(fmla))))

def implies(s1,s2,axioms,relations,op):
    u1,c1,p1 = s1
    u2,c2,p2 = s2
    if u1 == None and u2 != None:
        return False
#    print "c1: {}".format(c1)
#    print "axioms: {}".format(axioms)
#    print "df: {}".format(diff_frame(u1,u2,relations,op))
    c1 = and_clauses(c1,axioms,diff_frame(u1,u2,relations,op))
    if isinstance(c2,Clauses):
        if not c2.is_universal_first_order() or not p2.is_universal_first_order():
            return False
        c2 = and_clauses(c2,diff_frame(u2,u1,relations,op))
        return clauses_imply(p1,p2) and clauses_imply(c1,c2)
    else:
        if not is_prenex_universal(c2) or not is_prenex_universal(p2):
            return False
        c2 = And(c2,clauses_to_formula(diff_frame(u2,u1,relations,op)))
        return clauses_imply_formula_cex(p1,p2) and clauses_imply_formula_cex(c1,c2)

def implies_state(s1,s2,axioms,relations):
    return implies(s1,s2,axioms,relations,old)

def implies_action(s1,s2,axioms,relations):
    return implies(s1,s2,axioms,relations,new)

def join_state(s1,s2,relations):
    return join(clausify_state(s1),clausify_state(s2),relations,old)

def join_action(s1,s2,relations):
    return join(s1,s2,relations,new)

def condition_update_on_fmla(update,fmla,relations):
    """Given an update, return an update conditioned on fmla. Maybe an "else" would
    be useful too :-).
    """
    updated,if_clauses,if_pre = update
    else_clauses = update_frame_constraint(update,relations)
    if_clauses = condition_clauses(if_clauses,fmla)
    else_clauses = condition_clauses(else_clauses,Not(fmla))
##    print "if_clauses: %s" % if_clauses
##    print "else_clauses: %s" % else_clauses
    return updated,(and_clauses(if_clauses,else_clauses)),if_pre

def rename_distinct(clauses1,clauses2):
    """ rename skolems in clauses1 so they don't occur in clauses2.
    """
#    print "rename_distinct clauses1 = {}".format(clauses1)
#    print "rename_distinct clauses2 = {!r}".format(clauses2)
    used1 = used_symbols_clauses(clauses1)
    used2 = used_symbols_clauses(clauses2)
    rn = UniqueRenamer('',used2)
    map1 = dict()
    for s in used1:
        if is_skolem(s):
            map1[s] = rename(s,rn)
    return rename_clauses(clauses1,map1)

# TODO: this will be quadratic for chains of updates

def compose_updates(update1,axioms,update2):
    updated1, clauses1, pre1 = update1
    updated2, clauses2, pre2 = update2
    clauses2 = rename_distinct(clauses2,clauses1)
    pre2 = rename_distinct(pre2,clauses1)
#    print "clauses2 = {}".format(clauses2)
    us1 = set(updated1)
    us2 = set(updated2)
    mid = us1.intersection(us2)
    mid_ax = clauses_using_symbols(mid,axioms)
    used = used_symbols_clauses(and_clauses(clauses1,clauses2))
    rn = UniqueRenamer('__m_',used)
    map1 = dict()
    map2 = dict()
    for v in updated1:
        map2[v] = new(v)
    for mv in mid:
        mvf = rename(mv,rn)
        map1[new(mv)] = mvf
        map2[mv] = mvf
    clauses1 = rename_clauses(clauses1,map1)
    new_clauses = and_clauses(clauses1, rename_clauses(and_clauses(clauses2,mid_ax),map2))
    new_updated = list(us1.union(us2))
#    print "pre1 before = {}".format(pre1)
    pre1 = and_clauses(pre1,diff_frame(updated1,updated2,None,new))  # keep track of post-state of assertion failure
#    print "pre1 = {}".format(pre1)
    new_pre = or_clauses(pre1,and_clauses(clauses1,rename_clauses(and_clauses(pre2,mid_ax),map2)))
#    print "new_pre = {}".format(new_pre)
    return (new_updated,new_clauses,new_pre)

def exist_quant_map(syms,clauses):
    used = used_symbols_clauses(clauses)
    rn = UniqueRenamer('__',used)
    map1 = dict()
    for s in syms:
        map1[s] = rename(s,rn)
    return map1,rename_clauses(clauses,map1)

def exist_quant(syms,clauses):
    map1,res = exist_quant_map(syms,clauses)
    return res

def conjoin(clauses1,clauses2):
    """ Conjoin clause sets, taking into account skolems """
    return and_clauses(clauses1,rename_distinct(clauses2,clauses1))

def constrain_state(upd,fmla):
    return (upd[0],and_clauses(upd[1],formula_to_clauses(fmla)),upd[2])

def hide(syms,update):
    syms = set(syms)
    syms.update(new(s) for s in update[0] if s in syms)
    new_updated = [s for s in update[0] if s not in syms]
    new_tr = exist_quant(syms,update[1])
    new_pre = exist_quant(syms,update[2])
    return (new_updated,new_tr,new_pre)

def hide_state(syms,update):
    syms = set(syms)
    if update[0] != None:
        syms.update(old(s) for s in update[0] if s in syms)
        new_updated = [s for s in update[0] if s not in syms]
    else:
        new_updated = None
    new_tr = exist_quant(syms,update[1])
    new_pre = exist_quant(syms,update[2])
    return (new_updated,new_tr,new_pre)

def hide_state_map(syms,update):
    syms = set(syms)
    if update[0] != None:
        syms.update(old(s) for s in update[0] if s in syms)
        new_updated = [s for s in update[0] if s not in syms]
    else:
        new_updated = None
    trmap,new_tr = exist_quant_map(syms,update[1])
    new_pre = exist_quant(syms,update[2])
    return trmap, (new_updated,new_tr,new_pre)

def subst_action(update,subst):
    print subst
    syms = dict(subst.iteritems())
    syms.update((new(s),new(syms[s])) for s in update[0] if s in syms)
    print syms
    new_updated = [subst.get(s,s) for s in update[0]]
    new_tr = rename_clauses(update[1],syms)
    new_pre = rename_clauses(update[2],syms)
    return (new_updated,new_tr,new_pre)

def forward_image_map(pre_state,axioms,update):
    updated, clauses, _precond = update
#    print "transition_relation: {}".format(clauses)
    pre_ax = clauses_using_symbols(updated,axioms)
    pre = conjoin(pre_state,pre_ax)
    map1,res = exist_quant_map(updated,conjoin(pre,clauses))
    res = rename_clauses(res, dict((new(x),x) for x in updated))
##    print "before simp: %s" % res
    # res = simplify_clauses(res)
    return map1,res

def forward_image(pre_state,axioms,update):
    map1,res = forward_image_map(pre_state,axioms,update)
    return res

def action_failure(action):
    upd,tr,pre = action
    return upd,pre,true_clauses()

class ActionFailed(Exception):
    def __init__(self,clauses,trans):
        self.clauses = clauses
        self.trans = trans

def clausify(f):
    return f if isinstance(f,Clauses) else formula_to_clauses(f)

def clausify_state(s):
    upd,tr,pre = s
    return (upd,clausify(tr),clausify(pre))


def remove_taut_eqs_clauses(clauses):
   return Clauses(
                [f for f in clauses.fmlas if not is_tautology_equality(f)],
                clauses.defs
            )

def extract_pre_post_model(clauses,model,updated):
    renaming = dict((v,new(v)) for v in updated)
    ignore = lambda s: s.is_skolem() or is_new(s)
    pre_clauses = clauses_model_to_clauses(clauses,ignore = ignore,model = model,numerals=use_numerals())
    ignore = lambda s: s.is_skolem() or (not is_new(s) and s in renaming)
    post_clauses = clauses_model_to_clauses(clauses,ignore = ignore,model = model,numerals=use_numerals())
    post_clauses = rename_clauses(post_clauses,inverse_map(renaming))
    return map(remove_taut_eqs_clauses,(pre_clauses,post_clauses))

def compose_state_action(state,axioms,action, check=True):
    """ Compose a state and an action, returning a state """
#    print "state: {}".format(state)
#    print "action: {}".format(action)
    su,sc,sp = state
    au,ac,ap = action
    sc,sp = clausify(sc),clausify(sp)
    if check:
        pre_test = and_clauses(and_clauses(sc,ap),axioms)
        model = small_model_clauses(pre_test)
        if model != None:
            trans = extract_pre_post_model(pre_test,model,au)
            post_updated = [new(s) for s in au]
            pre_test = exist_quant(post_updated,pre_test)
            raise ActionFailed(pre_test,trans)
    if su != None:      # none means all moded
        ssu = set(su) # symbols already modified in state
        rn = dict((x,old(x)) for x in au if x not in ssu)
        sc = rename_clauses(sc,rn)
        ac = rename_clauses(ac,rn)
        su = list(su)
        union_to_list(su,au)
    img = forward_image(sc,axioms,action)
##    print "compose: {}".format((su,img,sp))
    return (su,img,sp)


def reverse_image(post_state,axioms,update):
    updated, clauses, _precond = update
    post_ax = clauses_using_symbols(updated,axioms)
    post_clauses = conjoin(post_state,post_ax)
    post_clauses = rename_clauses(post_clauses, dict((x,new(x)) for x in updated))
    post_updated = [new(s) for s in updated]
    res = exist_quant(post_updated,conjoin(clauses,post_clauses))
#    res = simplify_clauses(res)
    return res

def interpolant(clauses1,clauses2,axioms,interpreted):
#    print "interpolant clauses1={} clauses2={}".format(clauses1,clauses2)
#    print "axioms = {}".format(axioms)
    foo = and_clauses(clauses1,axioms)
    clauses2 = simplify_clauses(clauses2)
    core = unsat_core(clauses2,foo)
    if core == None:
        return None
#    print "core: %s" % core
    return core, interp_from_unsat_core(clauses2,foo,core,interpreted)

def forward_interpolant(pre_state,update,post_state,axioms,interpreted):
    return interpolant(forward_image(pre_state,axioms,update),post_state,axioms,interpreted)

def reverse_interpolant_case(post_state,update,pre_state,axioms,interpreted):
    pre = reverse_image(post_state,axioms,update)
    pre_case = clauses_case(pre)
##    print "pre_case1: {}".format(pre_case)
    pre_case = [cl for cl in pre_case if len(cl) <= 1
                                         and is_ground_clause(cl)
                                         and not any(is_skolem(r) for r,n in relations_clause(cl))]
##    print "pre_case2: {}".format(pre_case)
    return interpolant(pre_state,pre_case,axioms,interpreted)

def interpolant_case(pre_state,post,axioms,interpreted):
#    print "interpolant_case: before clauses_case"
#    print "interpolant_case post: {}".format(post)
    post_case = clauses_case(post)
#    print "interpolant_case: after clauses_case"
##    print "post_case1: {}".format(post_case)
    post_case = Clauses([cl for cl in post_case.clauses
                         if len(cl) <= 1
                         and is_ground_clause(cl)
                         and not any(is_skolem(r) for r,n in relations_clause(cl))])
#    print "interpolant_case: after filtering"
#    print "post_case2: {}".format(post_case)
    return interpolant(pre_state,post_case,axioms,interpreted)

def interp_from_unsat_core(clauses1,clauses2,core,interpreted):
    used_syms = used_symbols_clauses(core)
    vars = used_variables_clauses(core)
    if vars:
#        print "interpolant would require skolem constants"
        return None
    core_consts = used_constants_clauses(core)
    clauses2_consts = used_constants_clauses(clauses2)
#    print "interp_from_unsat_core core_consts = {}".format(map(str,core_consts))
#    print "interp_from_unsat_core clauses2_consts = {}".format(map(str,clauses2_consts))
    renaming = dict()
    i = 0
    for v in core_consts:
        if v not in clauses2_consts or v.is_skolem(): # and v not in interpreted:
            renaming[v] = Variable('V' + str(i),Constant(v).get_sort())
            i += 1
#    print "interp_from_unsat_core core = {}".format(core)
#    print "interp_from_unsat_core renaming = {}".format(renaming)
    renamed_core = substitute_constants_clauses(core,renaming)
#    print "interp_from_unsat_core renamed_core = {}".format(renamed_core)
    res = simplify_clauses(Clauses([Or(*[negate(c) for c in renamed_core.fmlas])]))
#    print "interp_from_unsat_core res = {}".format(res)
    return res

def small_model_clauses(cls):
    # Don't try to shrink the integers!
    return get_small_model(cls,ivy_logic.uninterpreted_sorts(),[])

class History(object):
    """ A history is a symbolically represented sequence of states. """
    def __init__(self,state,maps = []):
        """ state is the initial state of the history """
#        print "init: {}".format(state)
        update,clauses,pre = state
        assert update == None and pre.is_false()
        self.maps = maps     # sequence of symbol renamings resulting from forward images
        self.post = clauses  # characteristic formula of the history


    def forward_step(self,axioms,update):
        """ This is like forward_image on states, but records the
        symbol renaming used in the forward image. The list of
        renamings is used to reconstruct the state symbols at previous
        times in the history. A new history after forward step is
        returned. """
#        print "step: pre = {}, axioms = {}, update = {}".format(self.post,axioms,update)
        map1,res = forward_image_map(self.post,axioms,update)
        return History(pure_state(res),self.maps + [map1])

    def assume(self,clauses):
        """ Returns a new history in which the final state is constrainted to
        satisfy "clauses"."""
#        print "assume post: {}".format(self.post)
#        print "assume: {}".format(clauses)
        if isinstance(clauses,tuple):  # a pure state
            assert is_pure_state(clauses)
            clauses = clauses[1]
        clauses = rename_distinct(clauses,self.post) # TODO: shouldn't be needed
        return History(pure_state(and_clauses(self.post,clauses)),self.maps)

    def ignore(self,s,img,renaming):
        res = not(s in img or not s.is_skolem() and s not in renaming)
#        print "ignore: {} = {}".format(s,res)
        return res

    def satisfy(self, axioms, _get_model_clauses=None):
        """ Produce a state sequence if the symbolic history contains
        one. Returns the sort universes and a sequence of states, or
        None if the history is vacuous. """

        if _get_model_clauses is None:
            _get_model_clauses = small_model_clauses

#        print "axioms: {}".format(axioms)

        # A model of the post-state embeds a valuation for each time
        # in the history.
        post = and_clauses(self.post,axioms)
#        print "post: {}".format(post)
        print "bounded check {"
        model = _get_model_clauses(post)
        print "} bounded check"
        if model == None:
#            print "core = {}".format(unsat_core(post,true_clauses()))
            return None

        # we reconstruct the sub-model for each state composing the
        # recorded renamings in reverse order. Here "renaming" maps
        # symbols representing a past time onto current time skolems
        renaming,states,maps = {},[],reversed(self.maps)
        while True:
            # ignore all symbols except those representing the given past time
            img = set(renaming[s] for s in renaming if not s.is_skolem())
            ignore = lambda s: self.ignore(s,img,renaming)
            # get the sub-mode for the given past time as a formula
            clauses = clauses_model_to_clauses(post,ignore = ignore, model = model, numerals=use_numerals())
            # map this formula into the past using inverse map
            clauses = rename_clauses(clauses,inverse_map(renaming))
            # remove tautology equalities, TODO: not sure if this is correct here
            clauses = Clauses(
                [f for f in clauses.fmlas if not is_tautology_equality(f)],
                clauses.defs
            )
            states.append(clauses)
            try:
                # update the inverse map by composing it with inverse
                # of the next renaming (in reverse order)
                renaming = compose_maps(next(maps),renaming)
            except StopIteration:
                break
        uvs = model.universes(numerals=use_numerals())
#        print "uvs: {}".format(uvs)
        return uvs, [pure_state(clauses) for clauses in reversed(states)]


def use_numerals():
    return iu.use_numerals.get()

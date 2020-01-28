#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This module contains a liveness to safety reduction that allows
proving temporal properties.


TODO's and open issues:

* automatically add conjectures of original system to the saved state

* automatically add basic conjectures about the monitor (e.g. states
  are mutually exclusive)

* handle multiple temporal properties

* temporal axioms?

* support nesting structure?

* review the correctness

* figure out the public_actions issue

* decide abotu normalizing the Boolean structure of temporal formulas,
  properties, waited formulas, and named binders (e.g. normalize ~~phi
  to phi?)

* a syntax for accessing Skolem constants and functions from the
  negation of temporal properties.


Useful definitions from ivy_module:
self.definitions = []  # TODO: these are actually "derived" relations
self.labeled_axioms = []
self.labeled_props = []
self.labeled_inits = []
self.labeled_conjs = []  # conjectures
self.actions = {}
self.public_actions = set()
self.initializers = [] # list of name,action pairs
self.sig
"""

from collections import defaultdict
from itertools import chain

from ivy_printer import print_module
from ivy_actions import (AssignAction, Sequence, ChoiceAction,
                         AssumeAction, AssertAction, HavocAction,
                         concat_actions, Action, CallAction)
import ivy_actions as iact
import logic as lg
import ivy_logic as ilg
import ivy_logic_utils as ilu
import ivy_utils as iu
import ivy_temporal as itm
import ivy_proof as ipr
import ivy_module as im

debug = iu.BooleanParameter("l2s_debug",False)

def forall(vs, body):
    return lg.ForAll(vs, body) if len(vs) > 0 else body


def l2s_tactic(prover,goals,proof):
    mod = im.module
    goal = goals[0]                  # pick up the first proof goal
    lineno = goal.lineno
    conc = ipr.goal_conc(goal)       # get its conclusion
    if not isinstance(conc,itm.TemporalModels):
        raise iu.IvyError(proof,'proof goal is not temporal')
    model = conc.model.clone([])
    fmla = conc.fmla

    # Get all the temporal properties from the prover environment as assumptions
    
    # Add all the assumed invariants to the model

    assumed_gprops = [x for x in prover.axioms if not x.explicit and x.temporal]
    model.asms.extend([p.clone([p.label,p.formula.args[0]]) for p in assumed_gprops])

    # TRICKY: We postpone compiling formulas in the tactic until now, so
    # that tactics can introduce their own symbols. But, this means that the
    # tactic has to be given an appropriate environment label for any temporal
    # operators. Here, we compile the invariants in the tactic, using the given
    # label.

    assert hasattr(proof,'labels') and len(proof.labels) == 1
    proof_label = proof.labels[0]
#    print 'proof label: {}'.format(proof_label)
    invars = [ilg.label_temporal(inv.compile(),proof_label) for inv in proof.tactic_decls]

    l2s_waiting = lg.Const('l2s_waiting', lg.Boolean)
    l2s_frozen = lg.Const('l2s_frozen', lg.Boolean)
    l2s_saved = lg.Const('l2s_saved', lg.Boolean)
    l2s_d = lambda sort: lg.Const('l2s_d',lg.FunctionSort(sort,lg.Boolean))
    l2s_a = lambda sort: lg.Const('l2s_a',lg.FunctionSort(sort,lg.Boolean))
    l2s_w = lambda vs, t: lg.NamedBinder('l2s_w', vs, proof_label, t)
    l2s_s = lambda vs, t: lg.NamedBinder('l2s_s', vs, proof_label, t)
    l2s_g = lambda vs, t, environ: lg.NamedBinder('l2s_g', vs, environ, t)
    old_l2s_g = lambda vs, t, environ: lg.NamedBinder('_old_l2s_g', vs, environ, t)

    # Desugar the invariants.
    #
    # $was. phi(V)  -->   l2s_saved & ($l2s_s V.phi(V))(V)
    # $happened. phi --> l2s_saved & ~($l2s_w V.phi(V))(V)
    #
    # We push $l2s_s inside propositional connectives, so that the saved
    # values correspond to atoms. Otherwise, we would have redundant
    # saved values, for example p(X) and ~p(X).

    def desugar(expr):
        def apply_was(expr):
            if isinstance(expr,(lg.And,lg.Or,lg.Not,lg.Implies,lg.Iff)):
                return expr.clone([apply_was(a) for a in expr.args])
            vs = list(iu.unique(ilu.variables_ast(expr)))
            return l2s_s(vs,expr)(*vs)
        def apply_happened(expr):
            vs = list(iu.unique(ilu.variables_ast(expr)))
            return lg.Not(l2s_w(vs,expr)(*vs))
        if ilg.is_named_binder(expr):
            if expr.name == 'was':
                if len(expr.variables) > 0:
                    raise iu.IvyError(expr,"operator 'was' does not take parameters")
                return lg.And(l2s_saved,apply_was(expr.body))
            elif expr.name == 'happened':
                if len(expr.variables) > 0:
                    raise iu.IvyError(expr,"operator 'happened' does not take parameters")
                return lg.And(l2s_saved,apply_happened(expr.body))
        return expr.clone([desugar(a) for a in expr.args])
    
    invars = map(desugar,invars)
                          
    # Add the invariant phi to the list. TODO: maybe, if it is a G prop
    # invars.append(ipr.clone_goal(goal,[],invar))

    # Add the invariant list to the model
    model.invars = model.invars + invars
    
    # for inv in invars:
    #     print inv
    #     for b in ilu.named_binders_ast(inv):
    #         print 'orig binder: {} {} {}'.format(b.name,b.environ,b.body)

    # model pass helper funciton
    def mod_pass(transform):
        model.invars = [transform(x) for x in model.invars]
        model.asms = [transform(x) for x in model.asms]
        # TODO: what about axioms and properties?
        newb = []
        model.bindings = [b.clone([transform(b.action)]) for b in model.bindings]
        model.init = transform(model.init)

    # We first convert all temporal operators to named binders, so
    # it's possible to normalize them. Otherwise we won't have the
    # connection betweel (globally p(X)) and (globally p(Y)). Note
    # that we replace them even inside named binders.
    l2s_gs = set()
    def _l2s_g(vs, t, env):
        vs = tuple(vs)
        res = l2s_g(vs, t,env)
#        print 'l2s_gs: {} {} {}'.format(vs,t,env)
        l2s_gs.add((vs,t,env))
        return res
    replace_temporals_by_l2s_g = lambda ast: ilu.replace_temporals_by_named_binder_g_ast(ast, _l2s_g)
    mod_pass(replace_temporals_by_l2s_g)

    not_lf = replace_temporals_by_l2s_g(lg.Not(fmla))
    if debug.get():
        print "=" * 80 +"\nafter replace_temporals_by_named_binder_g_ast"+ "\n"*3
        print "=" * 80 + "\nl2s_gs:"
        for vs, t, env in sorted(l2s_gs):
            print vs, t, env
        print "=" * 80 + "\n"*3
        print model
        print "=" * 80 + "\n"*3

    # now we normalize all named binders
    mod_pass(ilu.normalize_named_binders)
    if debug.get():
        print "=" * 80 +"\nafter normalize_named_binders"+ "\n"*3
        print model
        print "=" * 80 + "\n"*3

    # construct the monitor related building blocks

    uninterpreted_sorts = [s for s in ilg.sig.sorts.values() if type(s) is lg.UninterpretedSort and s.name not in mod.finite_sorts]
    reset_a = [
        AssignAction(l2s_a(s)(v), l2s_d(s)(v)).set_lineno(lineno)
        for s in uninterpreted_sorts
        for v in [lg.Var('X',s)]
    ]
    add_consts_to_d = [
        AssignAction(l2s_d(s)(c), lg.true).set_lineno(lineno)
        for s in uninterpreted_sorts
        for c in ilg.sig.symbols.values() if c.sort == s
    ]
    # TODO: maybe add all ground terms, not just consts (if stratified)
    # TODO: add conjectures that constants are in d and a

    # figure out which l2s_w and l2s_s are used in conjectures
    named_binders_conjs = defaultdict(list) # dict mapping names to lists of (vars, body)
    for b in ilu.named_binders_asts(model.invars):
#        print 'binder: {} {} {}'.format(b.name,b.environ,b.body)
        named_binders_conjs[b.name].append((b.variables, b.body))
    named_binders_conjs = defaultdict(list,((k,list(set(v))) for k,v in named_binders_conjs.iteritems()))
    to_wait = [] # list of (variables, term) corresponding to l2s_w in conjectures
    to_wait += named_binders_conjs['l2s_w']
    to_save = [] # list of (variables, term) corresponding to l2s_s in conjectures
    to_save += named_binders_conjs['l2s_s']

    if debug.get():
        print "=" * 40 + "\nto_wait:\n"
        for vs, t in to_wait:
            print vs, t
            print list(ilu.variables_ast(t)) == list(vs)
            print
        print "=" * 40

    save_state = [
        AssignAction(l2s_s(vs,t)(*vs), t).set_lineno(lineno)
        for vs, t in to_save
    ]
    done_waiting = [
        forall(vs, lg.Not(l2s_w(vs,t)(*vs)))
        for vs, t in to_wait
    ]
    reset_w = [
        AssignAction(
            l2s_w(vs,t)(*vs),
            lg.And(*([l2s_d(v.sort)(v) for v in vs if v.sort.name not in mod.finite_sorts]
                     + [lg.Not(t),
                        replace_temporals_by_l2s_g(lg.Not(lg.Globally(proof_label,ilu.negate(t))))]))
        ).set_lineno(lineno)
        for vs, t in to_wait
    ]

    fair_cycle = [l2s_saved]
    fair_cycle += done_waiting
    # projection of relations
    fair_cycle += [
        lg.ForAll(vs, lg.Implies(
            lg.And(*(l2s_a(v.sort)(v) for v in vs if v.sort.name not in mod.finite_sorts)),
            lg.Iff(l2s_s(vs, t)(*vs), t)
        ))
        if len(vs) > 0 else
        lg.Iff(l2s_s(vs, t), t)
        for vs, t in to_save
        if (t.sort == lg.Boolean or
            isinstance(t.sort, lg.FunctionSort) and t.sort.range == lg.Boolean
        )
    ]
    # projection of functions and constants
    fair_cycle += [
        forall(vs, lg.Implies(
            lg.And(*(
                [l2s_a(v.sort)(v) for v in vs if v.sort.name not in mod.finite_sorts] +
                ([lg.Or(l2s_a(t.sort)(l2s_s(vs, t)(*vs)),
                       l2s_a(t.sort)(t))] if t.sort.name not in mod.finite_sorts else [])
            )),
            lg.Eq(l2s_s(vs, t)(*vs), t)
        ))
        for vs, t in to_save
        if (isinstance(t.sort, lg.UninterpretedSort) or
            isinstance(t.sort, lg.FunctionSort) and isinstance(t.sort.range, lg.UninterpretedSort)
        )
    ]
    assert_no_fair_cycle = AssertAction(lg.Not(lg.And(*fair_cycle))).set_lineno(lineno)
    assert_no_fair_cycle.lineno = goal.lineno

    monitor_edge = lambda s1, s2: [
        AssumeAction(s1).set_lineno(lineno),
        AssignAction(s1, lg.false).set_lineno(lineno),
        AssignAction(s2, lg.true).set_lineno(lineno),
    ]
    change_monitor_state = [ChoiceAction(
        # waiting -> frozen
        Sequence(*(
            monitor_edge(l2s_waiting, l2s_frozen) +
            [AssumeAction(x).set_lineno(lineno) for x in done_waiting] +
            reset_a
        )).set_lineno(lineno),
        # frozen -> saved
        Sequence(*(
            monitor_edge(l2s_frozen, l2s_saved) +
            save_state +
            reset_w
        )),
        # stay in same state (self edge)
        Sequence().set_lineno(lineno),
    ).set_lineno(lineno)]

    # tableau construction (sort of)

    # Note that we first transformed globally and eventually to named
    # binders, in order to normalize. Without this, we would get
    # multiple redundant axioms like:
    # forall X. (globally phi(X)) -> phi(X)
    # forall Y. (globally phi(Y)) -> phi(Y)
    # and the same redundancy will happen for transition updates.

    # temporals = []
    # temporals += list(ilu.temporals_asts(
    #     # TODO: these should be handled by mod_pass instead (and come via l2s_gs):
    #     # mod.labeled_axioms +
    #     # mod.labeled_props +
    #     [lf]
    # ))
    # temporals += [lg.Globally(lg.Not(t)) for vs, t in to_wait]
    # temporals += [lg.Globally(t) for vs, t in l2s_gs]
    # # TODO get from temporal axioms and temporal properties as well
    # print '='*40 + "\ntemporals:"
    # for t in temporals:
    #     print t, '\n'
    # print '='*40
    # to_g = [ # list of (variables, formula)
    #     (tuple(sorted(ilu.variables_ast(tt))), tt) # TODO what about variable normalization??
    #     for t in temporals
    #     for tt in [t.body if type(t) is lg.Globally else
    #                lg.Not(t.body) if type(t) is lg.Eventually else 1/0]
    # ]
    # TODO: get rid of the above, after properly combining it
    to_g = [] # list of (variables, formula)
    to_g += list(l2s_gs)
    to_g = list(set(to_g))
    if debug.get():
        print '='*40 + "\nto_g:\n"
        for vs, t, env in sorted(to_g):
            print vs, t, '\n'
        print '='*40

    assume_g_axioms = [
        AssumeAction(forall(vs, lg.Implies(l2s_g(vs, t, env)(*vs), t))).set_lineno(lineno)
        for vs, t, env in to_g
    ]


    # now patch the module actions with monitor and tableau


    if debug.get():
        print "public_actions:", model.calls

    # Tableau construction
    #
    # Each temporal operator has an 'environment'. The operator
    # applies to states *not* in actions labeled with this
    # environment. This has several consequences:
    #
    # 1) The operator's semantic constraint is an assumed invariant (i.e.,
    # it holds outside of any action)
    #
    # 2) An 'event' for the temporal operator occurs when (a) we return
    # from an execution context inside its environment to one outside,
    # or (b) we are outside the environment of the operator and some symbol
    # occurring in it's body is mutated.
    #
    # 3) At any event for the operator, we update its truth value and
    # and re-establish its semantic constraint.
    #

    # This procedure generates code for an event corresponding to a
    # list of operators. The tableau state is updated and the
    # semantics applied.
    
    def prop_events(gprops):
        res = []
        for gprop in gprops:
            vs,t,env = gprop.variables, gprop.body, gprop.environ
            res.append(AssignAction(old_l2s_g(vs, t, env)(*vs),l2s_g(vs, t, env)(*vs)).set_lineno(lineno))
            res.append(HavocAction(l2s_g(vs, t, env)(*vs)).set_lineno(lineno))
        for gprop in gprops:
            vs,t,env = gprop.variables, gprop.body, gprop.environ
            res.append(AssumeAction(forall(vs, lg.Implies(old_l2s_g(vs, t, env)(*vs),
                                                          l2s_g(vs, t, env)(*vs)))).set_lineno(lineno))
            res.append(AssumeAction(forall(vs, lg.Implies(lg.And(lg.Not(old_l2s_g(vs, t, env)(*vs)), t),
                                                          lg.Not(l2s_g(vs, t, env)(*vs))))).set_lineno(lineno))
            res.append(AssumeAction(forall(vs, lg.Implies(l2s_g(vs, t, env)(*vs), t))).set_lineno(lineno))
            
        return res
            

    # This procedure generates code for an event corresponding to a
    # list of eventualites to be waited on. The tableau state is updated and the
    # semantics applied.

    def wait_events(waits):
        res = []
        for wait in waits:
            vs = wait.variables
            t = wait.body

        # (l2s_w V. phi)(V) := (l2s_w V. phi)(V) & ~phi & ~(l2s_g V. ~phi)(V)

            res.append(
                AssignAction(
                    wait(*vs),
                    lg.And(wait(*vs),
                           lg.Not(t),
                           replace_temporals_by_l2s_g(lg.Not(lg.Globally(proof_label,ilu.negate(t)))))
                    # TODO check this and make sure its correct
                    # note this adds to l2s_gs
                ).set_lineno(lineno))
        return res

    # The following procedure instruments a statement with operator
    # events for all of the temporal operators.  This depends on the
    # statement's environment, that is, current set of environment
    # labels.
    #
    # Currently, the environment labels of a statement have to be
    # statically determined, but this could change, i.e., the labels
    # could be represented by boolean variables. 
    #
    
    # First, make some memo tables

    envprops = defaultdict(list)
    symprops = defaultdict(list)
    symwaits = defaultdict(list)
    for vs, t, env in l2s_gs:
        prop = l2s_g(vs,t,env)
        envprops[env].append(prop)
        for sym in ilu.symbols_ast(t):
            symprops[sym].append(prop)
    for vs, t in to_wait:
        wait = l2s_w(vs,t)
        for sym in ilu.symbols_ast(t):
            symwaits[sym].append(wait)
    actions = dict((b.name,b.action) for b in model.bindings)
    # lines = dict(zip(gprops,gproplines))
            
    def instr_stmt(stmt,labels):

        # first, recur on the sub-statements
        args = [instr_stmt(a,labels) if isinstance(a,Action) else a for a in stmt.args]
        res = stmt.clone(args)

        # now add any needed temporal events after this statement
        event_props = set()
        event_waits = set()

        # first, if it is a call, we must consider any events associated with
        # the return
        
        # if isinstance(stmt,CallAction):
        #     callee = actions[stmt.callee()]  # get the called action
        #     exiting = [l for l in callee.labels if l not in labels] # environments we exit on return
        #     for label in exiting:
        #         for prop in envprops[label]:
        #             event_props.add(prop)

        # Second, if a symbol is modified, we must add events for every property that
        # depends on the symbol, but only if we are not in the environment of that property. 
                    
        for sym in stmt.modifies():
            for prop in symprops[sym]:
#                if prop.environ not in labels:
                event_props.add(prop)
            for wait in symwaits[sym]:
                event_waits.add(wait)

                    
        # Now, for every property event, we update the property state (none in this case)
        # and also assert the property semantic constraint. 

        events = prop_events(event_props)
        events += wait_events(event_waits)
        res =  iact.postfix_action(res,events)
        stmt.copy_formals(res) # HACK: This shouldn't be needed
        return res

    # Instrument all the actions

    model.bindings = [b.clone([b.action.clone([instr_stmt(b.action.stmt,b.action.labels)])])
                      for b in model.bindings]
    
    # Now, for every exported action, we add the l2s construction. On
    # exit of each external procedure, we add a tableau event for all
    # the operators whose scope is being exited.
    #
    # TODO: This is wrong in the case of an exported procedure that is
    # also internally called.  We do *not* want to update the tableau
    # in the case of an internal call, since the scope of the
    # operators os not exited. One solution to this is to create to
    # duplicate the actions so there is one version for internal
    # callers and one for external callers. It is possible that this
    # is already done by ivy_isolate, but this needs to be verified.
    
    calls = set(model.calls) # the exports
    for b in model.bindings:
        if b.name in calls:
            add_params_to_d = [
                AssignAction(l2s_d(p.sort)(p), lg.true)
                for p in b.action.inputs
                if p.sort.name not in mod.finite_sorts
            ]
            # tableau updates for exit to environment
            # event_props = set()
            # for label in b.action.labels:
            #     for prop in envprops[label]:
            #         event_props.add(prop)
            # events = prop_events(event_props)
            stmt = concat_actions(*(
                add_params_to_d +
                assume_g_axioms +  # could be added to model.asms
                [b.action.stmt] +
                add_consts_to_d
            )).set_lineno(lineno)
            b.action.stmt.copy_formals(stmt) # HACK: This shouldn't be needed
            b.action = b.action.clone([stmt])

    # The idle action handles automaton state update and cycle checking

    idle_action = concat_actions(*(
        change_monitor_state +
        assume_g_axioms +  # could be added to model.asms
        add_consts_to_d +
        [assert_no_fair_cycle]
    )).set_lineno(lineno)
    idle_action.formal_params = []
    idle_action.formal_returns = []
    model.bindings.append(itm.ActionTermBinding('idle',itm.ActionTerm([],[],[],idle_action)))
    model.calls.append('idle')
    
    l2s_init = [
        AssignAction(l2s_waiting, lg.true).set_lineno(lineno),
        AssignAction(l2s_frozen, lg.false).set_lineno(lineno),
        AssignAction(l2s_saved, lg.false).set_lineno(lineno),
    ]
    l2s_init += add_consts_to_d
    l2s_init += reset_w
    l2s_init += assume_g_axioms
    l2s_init += [AssumeAction(not_lf).set_lineno(lineno)]
    if not hasattr(model.init,'lineno'):
        model.init.lineno = None  # Hack: fix this
    model.init =  iact.postfix_action(model.init,l2s_init)

    if debug.get():
        print "=" * 80 + "\nafter patching actions" + "\n"*3
        print model
        print "=" * 80 + "\n"*3

    # now replace all named binders by fresh relations

    named_binders = defaultdict(list) # dict mapping names to lists of (vars, body)
    for b in ilu.named_binders_asts(chain(
            model.invars,
            model.asms,
            [model.init],
            [b.action for b in model.bindings],
    )):
        named_binders[b.name].append(b)
    named_binders = defaultdict(list, ((k,list(sorted(set(v)))) for k,v in named_binders.iteritems()))
    # make sure old_l2s_g is consistent with l2s_g
    assert len(named_binders['l2s_g']) == len(named_binders['_old_l2s_g'])
    assert named_binders['_old_l2s_g'] == [
         lg.NamedBinder('_old_l2s_g', b.variables, b.environ, b.body)
         for b in named_binders['l2s_g']
    ]
    subs = dict(
        (b, lg.Const('{}_{}'.format(k, i), b.sort))
        for k, v in named_binders.iteritems()
        for i, b in enumerate(v)
    )
    if debug.get():
        print "=" * 80 + "\nsubs:" + "\n"*3
        for k, v in subs.items():
            print k, ' : ', v, '\n'
        print "=" * 80 + "\n"*3
    mod_pass(lambda ast: ilu.replace_named_binders_ast(ast, subs))

    if debug.get():
        print "=" * 80 + "\nafter replace_named_binders" + "\n"*3
        print model
        print "=" * 80 + "\n"*3

    # if len(gprops) > 0:
    #     assumes = [gprop_to_assume(x) for x in gprops]
    #     model.bindings = [b.clone([prefix_action(b.action,assumes)]) for b in model.bindings]

    # HACK: reestablish invariant that shouldn't be needed

    for b in model.bindings:
        b.action.stmt.formal_params = b.action.inputs
        b.action.stmt.formal_returns = b.action.outputs

    # Change the conclusion formula to M |= true
    conc = itm.TemporalModels(model,lg.And())

    # Build the new goal
    goal = ipr.clone_goal(goal,ipr.goal_prems(goal),conc)

    # Return the new goal stack

    goals = [goal] + goals[1:]
    return goals

# Register the l2s tactic

ipr.register_tactic('l2s',l2s_tactic)



def l2s(mod, lf):

    # modify mod in place

    # module pass helper funciton
    def mod_pass(transform):
        mod.labeled_conjs = [transform(x) for x in mod.labeled_conjs]
        # TODO: what about axioms and properties?
        for a in mod.public_actions:
            action = mod.actions[a]
            new_action = transform(action)
            new_action.lineno = action.lineno
            new_action.formal_params = action.formal_params
            new_action.formal_returns = action.formal_returns
            mod.actions[a] = new_action
        mod.initializers = [(x, transform(y)) for x, y in mod.initializers]

    l2s_waiting = lg.Const('l2s_waiting', lg.Boolean)
    l2s_frozen = lg.Const('l2s_frozen', lg.Boolean)
    l2s_saved = lg.Const('l2s_saved', lg.Boolean)
    l2s_d = lambda sort: lg.Const('l2s_d',lg.FunctionSort(sort,lg.Boolean))
    l2s_a = lambda sort: lg.Const('l2s_a',lg.FunctionSort(sort,lg.Boolean))
    l2s_w = lambda vs, t: lg.NamedBinder('l2s_w', vs, None, t)
    l2s_s = lambda vs, t: lg.NamedBinder('l2s_s', vs, None, t)
    l2s_g = lambda vs, t: lg.NamedBinder('l2s_g', vs, None, t)
#    old_l2s_g = lambda vs, t: lg.NamedBinder('old_l2s_g', vs, t)

    #print ilu.used_symbols_asts(mod.labeled_conjs)
    #print '='*40
    #print list(ilu.named_binders_asts(mod.labeled_conjs))

    # some normalization

    # We first convert all temporal operators to named binders, so
    # it's possible to normalize them. Otherwise we won't have the
    # connection betweel (globally p(X)) and (globally p(Y)). Note
    # that we replace them even inside named binders.
    l2s_gs = set()
    def _l2s_g(vs, t):
        vs = tuple(vs)
        res = l2s_g(vs, t)
        l2s_gs.add((vs,t))
        return res
    replace_temporals_by_l2s_g = lambda ast: ilu.replace_temporals_by_named_binder_g_ast(ast, _l2s_g)
    mod_pass(replace_temporals_by_l2s_g)
    not_lf = replace_temporals_by_l2s_g(lg.Not(lf.formula))
    if debug.get():
        print "=" * 80 +"\nafter replace_temporals_by_named_binder_g_ast"+ "\n"*3
        print "=" * 80 + "\nl2s_gs:"
        for vs, t in sorted(l2s_gs):
            print vs, t
        print "=" * 80 + "\n"*3
        print model
        print "=" * 80 + "\n"*3

    # now we normalize all named binders
    mod_pass(ilu.normalize_named_binders)
    if debug.get():
        print "=" * 80 +"\nafter normalize_named_binders"+ "\n"*3
        print model
        print "=" * 80 + "\n"*3

    # TODO: what about normalizing lf?

    # construct the monitor related building blocks

    uninterpreted_sorts = [s for s in mod.sig.sorts.values() if type(s) is lg.UninterpretedSort and s.name not in mod.finite_sorts]
    reset_a = [
        AssignAction(l2s_a(s)(v), l2s_d(s)(v))
        for s in uninterpreted_sorts
        for v in [lg.Var('X',s)]
    ]
    add_consts_to_d = [
        AssignAction(l2s_d(s)(c), lg.true)
        for s in uninterpreted_sorts
        for c in mod.sig.symbols.values() if c.sort == s
    ]
    # TODO: maybe add all ground terms, not just consts (if stratified)
    # TODO: add conjectures that constants are in d and a

    # figure out which l2s_w and l2s_s are used in conjectures
    named_binders_conjs = defaultdict(list) # dict mapping names to lists of (vars, body)
    for b in ilu.named_binders_asts(mod.labeled_conjs):
        named_binders_conjs[b.name].append((b.variables, b.body))
    named_binders_conjs = defaultdict(list,((k,list(set(v))) for k,v in named_binders_conjs.iteritems()))
    to_wait = [] # list of (variables, term) corresponding to l2s_w in conjectures
    to_wait += named_binders_conjs['l2s_w']
    to_save = [] # list of (variables, term) corresponding to l2s_s in conjectures
    to_save += named_binders_conjs['l2s_s']

    if debug.get():
        print "=" * 40 + "\nto_wait:\n"
        for vs, t in to_wait:
            print vs, t
            print list(ilu.variables_ast(t)) == list(vs)
            print
        print "=" * 40

    save_state = [
        AssignAction(l2s_s(vs,t)(*vs), t)
        for vs, t in to_save
    ]
    done_waiting = [
        forall(vs, lg.Not(l2s_w(vs,t)(*vs)))
        for vs, t in to_wait
    ]
    reset_w = [
        AssignAction(
            l2s_w(vs,t)(*vs),
            lg.And(*(l2s_d(v.sort)(v) for v in vs if v.sort not in mod.finite_sorts))
        )
        for vs, t in to_wait
    ]
    update_w = [
        AssignAction(
            l2s_w(vs,t)(*vs),
            lg.And(l2s_w(vs,t)(*vs), lg.Not(t), replace_temporals_by_l2s_g(lg.Not(lg.Globally(ilu.negate(t)))))
            # TODO check this and make sure its correct
            # note this adds to l2s_gs
        )
        for vs, t in to_wait
    ]
    if debug.get():
        print "=" * 40 + "\nupdate_w:\n"
        for x in update_w:
            print x
            print
        print "=" * 40

    fair_cycle = [l2s_saved]
    fair_cycle += done_waiting
    # projection of relations
    fair_cycle += [
        lg.ForAll(vs, lg.Implies(
            lg.And(*(l2s_a(v.sort)(v) for v in vs if v.sort not in mod.finite_sorts)),
            lg.Iff(l2s_s(vs, t)(*vs), t)
        ))
        if len(vs) > 0 else
        lg.Iff(l2s_s(vs, t), t)
        for vs, t in to_save
        if (t.sort == lg.Boolean or
            isinstance(t.sort, lg.FunctionSort) and t.sort.range == lg.Boolean
        )
    ]
    # projection of functions and constants
    fair_cycle += [
        forall(vs, lg.Implies(
            lg.And(*(
                [l2s_a(v.sort)(v) for v in vs if v.sort not in mod.finite_sorts] +
                ([lg.Or(l2s_a(t.sort)(l2s_s(vs, t)(*vs)),
                       l2s_a(t.sort)(t))] if t.sort not in mod.finite_sorts else [])
            )),
            lg.Eq(l2s_s(vs, t)(*vs), t)
        ))
        for vs, t in to_save
        if (isinstance(t.sort, lg.UninterpretedSort) or
            isinstance(t.sort, lg.FunctionSort) and isinstance(t.sort.range, lg.UninterpretedSort)
        )
    ]
    assert_no_fair_cycle = AssertAction(lg.Not(lg.And(*fair_cycle)))
    assert_no_fair_cycle.lineno = lf.lineno

    monitor_edge = lambda s1, s2: [
        AssumeAction(s1),
        AssignAction(s1, lg.false),
        AssignAction(s2, lg.true),
    ]
    change_monitor_state = [ChoiceAction(
        # waiting -> frozen
        Sequence(*(
            monitor_edge(l2s_waiting, l2s_frozen) +
            [AssumeAction(x) for x in done_waiting] +
            reset_a
        ).set_lineno(lineno)),
        # # frozen -> saved
        # Sequence(*(
        #     monitor_edge(l2s_frozen, l2s_saved) +
        #     save_state +
        #     reset_w
        # )),
        # stay in same state (self edge)
        Sequence().set_lineno(lineno),
    )]

    # tableau construction (sort of)

    # Note that we first transformed globally and eventually to named
    # binders, in order to normalize. Without this, we would get
    # multiple redundant axioms like:
    # forall X. (globally phi(X)) -> phi(X)
    # forall Y. (globally phi(Y)) -> phi(Y)
    # and the same redundancy will happen for transition updates.

    # temporals = []
    # temporals += list(ilu.temporals_asts(
    #     # TODO: these should be handled by mod_pass instead (and come via l2s_gs):
    #     # mod.labeled_axioms +
    #     # mod.labeled_props +
    #     [lf]
    # ))
    # temporals += [lg.Globally(lg.Not(t)) for vs, t in to_wait]
    # temporals += [lg.Globally(t) for vs, t in l2s_gs]
    # # TODO get from temporal axioms and temporal properties as well
    # print '='*40 + "\ntemporals:"
    # for t in temporals:
    #     print t, '\n'
    # print '='*40
    # to_g = [ # list of (variables, formula)
    #     (tuple(sorted(ilu.variables_ast(tt))), tt) # TODO what about variable normalization??
    #     for t in temporals
    #     for tt in [t.body if type(t) is lg.Globally else
    #                lg.Not(t.body) if type(t) is lg.Eventually else 1/0]
    # ]
    # TODO: get rid of the above, after properly combining it
    to_g = [] # list of (variables, formula)
    to_g += list(l2s_gs)
    to_g = list(set(to_g))
    if debug.get():
        print '='*40 + "\nto_g:\n"
        for vs, t in sorted(to_g):
            print vs, t, '\n'
        print '='*40

    assume_g_axioms = [
        AssumeAction(forall(vs, lg.Implies(l2s_g(vs, t)(*vs), t)))
        for vs, t in to_g
    ]
    update_g = [a for vs, t in to_g for a in [
        HavocAction(l2s_g(vs, t)(*vs)),
        AssumeAction(forall(vs, lg.Implies(old_l2s_g(vs, t)(*vs), l2s_g(vs, t)(*vs)))),
        AssumeAction(forall(vs, lg.Implies(lg.And(lg.Not(old_l2s_g(vs, t)(*vs)), t), lg.Not(l2s_g(vs, t)(*vs))))),
    ]]

    # now patch the module actions with monitor and tableau


    if debug.get():
        print "public_actions:", mod.public_actions
    # TODO: this includes the succ action (for the ticket example of
    # test/test_liveness.ivy). seems to be a bug, and this causes
    # wrong behavior for the monitor, since a call to succ from within
    # another action lets it take a step

    for a in mod.public_actions:
        action = mod.actions[a]
        add_params_to_d = [
            AssignAction(l2s_d(p.sort)(p), lg.true)
            for p in action.formal_params
            if p.sort not in mod.finite_sorts
        ]
        new_action = concat_actions(*(
            change_monitor_state +
            add_params_to_d +
            update_g +
            [action] +
            assume_g_axioms +
            add_consts_to_d +
            update_w +
            [assert_no_fair_cycle]
        ))
        new_action.lineno = action.lineno
        new_action.formal_params = action.formal_params
        new_action.formal_returns = action.formal_returns
        mod.actions[a] = new_action

    l2s_init = [
        AssignAction(l2s_waiting, lg.true),
        AssignAction(l2s_frozen, lg.false),
        AssignAction(l2s_saved, lg.false),
    ]
    l2s_init += add_consts_to_d
    l2s_init += reset_w
    l2s_init += assume_g_axioms
    l2s_init += [AssumeAction(not_lf)]
    mod.initializers.append(('l2s_init', Sequence(*l2s_init).set_lineno(lineno)))

    if debug.get():
        print "=" * 80 + "\nafter patching actions" + "\n"*3
        print model
        print "=" * 80 + "\n"*3

    # now replace all named binders by fresh relations

    named_binders = defaultdict(list) # dict mapping names to lists of (vars, body)
    for b in ilu.named_binders_asts(chain(
            mod.labeled_conjs,
            mod.actions.values(),
            (y for x,y in mod.initializers),
    )):
        named_binders[b.name].append(b)
    named_binders = defaultdict(list, ((k,list(sorted(set(v)))) for k,v in named_binders.iteritems()))
    # make sure old_l2s_g is consistent with l2s_g
    assert len(named_binders['l2s_g']) == len(named_binders['old_l2s_g'])
    assert named_binders['old_l2s_g'] == [
         lg.NamedBinder('old_l2s_g', b.variables, None, b.body)
         for b in named_binders['l2s_g']
    ]
    subs = dict(
        (b, lg.Const('{}_{}'.format(k, i), b.sort))
        for k, v in named_binders.iteritems()
        for i, b in enumerate(v)
    )
    if debug.get():
        print "=" * 80 + "\nsubs:" + "\n"*3
        for k, v in subs.items():
            print k, ' : ', v, '\n'
        print "=" * 80 + "\n"*3
    mod_pass(lambda ast: ilu.replace_named_binders_ast(ast, subs))

    if debug.get():
        print "=" * 80 + "\nafter replace_named_binders" + "\n"*3
        print model
        print "=" * 80 + "\n"*3

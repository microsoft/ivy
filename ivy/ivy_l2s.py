#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This module contains a liveness to safety reduction that allows
proving temporal properties.


TODO's and open issues:

* allow exporting and using of temporal properties

* support for ivy1.7 syntax

* add support for enumerated types

* add support for adding all elements smaller than a constant (downward finite total order)

* automatically add conjectures of original system to the saved state

* handle multiple temporal properties

* temporal axioms?

* review the correctness

* decide abotu normalizing the Boolean structure of temporal formulas,
  properties, waited formulas, and named binders (e.g. normalize ~~phi
  to phi?)

* syntax for accessing Skolem constants and functions from the
  negation of temporal properties.

* syntax for fair scheduling of actions (e.g., eliminate scheduled
  from ticket)

* use assetions instead of l2s_error
"""

"""
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
                         concat_actions)
import ivy_ast as ast
import logic as lg
import ivy_logic_utils as ilu
import ivy_utils as iu


debug = iu.BooleanParameter("l2s_debug",False)


def forall(vs, body):
    return lg.ForAll(vs, body) if len(vs) > 0 else body


def l2s(mod, temporal_goal):
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
    l2s_error = lg.Const('l2s_error', lg.Boolean)
    l2s_d = lambda sort: lg.Const('l2s_d',lg.FunctionSort(sort,lg.Boolean))
    l2s_a = lambda sort: lg.Const('l2s_a',lg.FunctionSort(sort,lg.Boolean))
    l2s_w = lambda vs, t: lg.NamedBinder('l2s_w', vs, t)
    l2s_s = lambda vs, t: lg.NamedBinder('l2s_s', vs, t)
    l2s_g = lambda vs, t: lg.NamedBinder('l2s_g', vs, t)
    old_l2s_g = lambda vs, t: lg.NamedBinder('old_l2s_g', vs, t)

    # add conjectures about monitor state
    conjs = [
        lg.Or(l2s_waiting, l2s_frozen, l2s_saved),
        lg.Or(lg.Not(l2s_waiting), lg.Not(l2s_frozen)),
        lg.Or(lg.Not(l2s_waiting), lg.Not(l2s_saved)),
        lg.Or(lg.Not(l2s_frozen), lg.Not(l2s_saved)),
    ]
    for f in conjs:
        c = ast.LabeledFormula(ast.Atom('l2s_internal'), f)
        c.lineno = temporal_goal.lineno
        mod.labeled_conjs.append(c)

    # add conjecture that we are not in the error state (this is
    # instead of using an assertion. see below)
    c = ast.LabeledFormula(ast.Atom('not_l2s_error'), lg.Not(l2s_error))
    c.lineno = temporal_goal.lineno
    mod.labeled_conjs.append(c)

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
    not_temporal_goal = replace_temporals_by_l2s_g(lg.Not(temporal_goal.formula))
    if debug.get():
        print "=" * 80 +"\nafter replace_temporals_by_named_binder_g_ast"+ "\n"*3
        print "=" * 80 + "\nl2s_gs:"
        for vs, t in sorted(l2s_gs):
            print vs, t
        print "=" * 80 + "\n"*3
        print_module(mod)
        print "=" * 80 + "\n"*3

    # now we normalize all named binders
    mod_pass(ilu.normalize_named_binders)
    if debug.get():
        print "=" * 80 +"\nafter normalize_named_binders"+ "\n"*3
        print_module(mod)
        print "=" * 80 + "\n"*3

    # TODO: what about normalizing temporal_goal? - temporal_goal
    # should not contain any named binders except for temporal
    # properties, so it is normalized by construction

    # construct the monitor related building blocks

    uninterpreted_sorts = [s for s in mod.sig.sorts.values() if type(s) is lg.UninterpretedSort]
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
    named_binders_conjs = defaultdict(list,((k,sorted(list(set(v)))) for k,v in named_binders_conjs.iteritems()))
    to_wait = [] # list of (variables, term) corresponding to l2s_w in conjectures
    to_wait += named_binders_conjs['l2s_w']
    to_save = [] # list of (variables, term) corresponding to l2s_s in conjectures
    to_save += named_binders_conjs['l2s_s']

    if debug.get():
        print "=" * 40 + "\nto_wait:\n"
        for vs, t in to_wait:
            print vs, t
            # print list(ilu.variables_ast(t)) == list(vs)
            # print
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
            lg.And(*(l2s_d(v.sort)(v) for v in vs))
        )
        for vs, t in to_wait
    ]
    update_w = [
        AssignAction(
            l2s_w(vs,t)(*vs),
            lg.And(l2s_w(vs,t)(*vs), lg.Not(t), replace_temporals_by_l2s_g(lg.Not(lg.Globally(ilu.negate(t)))))
            # ($l2s_w.  phi) waits until ( phi | globally ~phi), but
            # ($l2s_w. ~phi) waits until (~phi | globally  phi) (i.e., we avoid "globally ~~phi" here)
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
            lg.And(*(l2s_a(v.sort)(v) for v in vs)),
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
                [l2s_a(v.sort)(v) for v in vs] +
                [lg.Or(l2s_a(t.sort)(l2s_s(vs, t)(*vs)),
                       l2s_a(t.sort)(t))]
            )),
            lg.Eq(l2s_s(vs, t)(*vs), t)
        ))
        for vs, t in to_save
        if (isinstance(t.sort, lg.UninterpretedSort) or
            isinstance(t.sort, lg.FunctionSort) and isinstance(t.sort.range, lg.UninterpretedSort)
        )
    ]
    if debug.get():
        print "=" * 40 + "\nfair_cycle:\n"
        for x in fair_cycle:
            print x
            print
        print "=" * 40
    # TODO: figure out why AssertAction doesn't work properly
    def assert_no_fair_cycle(a):
        # comment and uncomment the following lines to debug:
        # res = AssertAction(lg.Not(lg.And(*fair_cycle)))
        # res = AssertAction(lg.false)
        # res.lineno = temporal_goal.lineno
        # res.lineno = a.lineno
        res = AssignAction(l2s_error, lg.And(*fair_cycle))
        return res

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
        )),
        # frozen -> saved
        Sequence(*(
            monitor_edge(l2s_frozen, l2s_saved) +
            save_state +
            reset_w
        )),
        # stay in same state (self edge)
        Sequence(),
    )]

    # tableau construction
    to_g = [] # list of (variables, formula)
    to_g += sorted(list(l2s_gs))
    if debug.get():
        print '='*40 + "\nto_g:\n"
        for vs, t in to_g:
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
    for a in mod.public_actions:
        action = mod.actions[a]
        add_params_to_d = [
            AssignAction(l2s_d(p.sort)(p), lg.true)
            for p in action.formal_params
        ]
        new_action = concat_actions(*(
            # TODO: check this with Sharon
            assume_g_axioms +
            change_monitor_state +
            add_params_to_d +
            update_g +
            [action] +
            assume_g_axioms +
            add_consts_to_d +
            update_w +
            [assert_no_fair_cycle(action)]
        ))
        new_action.lineno = action.lineno
        new_action.formal_params = action.formal_params
        new_action.formal_returns = action.formal_returns
        mod.actions[a] = new_action

    l2s_init = [
        AssignAction(l2s_waiting, lg.true),
        AssignAction(l2s_frozen, lg.false),
        AssignAction(l2s_saved, lg.false),
        AssignAction(l2s_error, lg.false),
    ]
    l2s_init += add_consts_to_d
    l2s_init += reset_w
    l2s_init += assume_g_axioms
    l2s_init += [AssumeAction(not_temporal_goal)]
    mod.initializers.append(('l2s_init', Sequence(*l2s_init)))

    if debug.get():
        print "=" * 80 + "\nafter patching actions" + "\n"*3
        print_module(mod)
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
         lg.NamedBinder('old_l2s_g', b.variables, b.body)
         for b in named_binders['l2s_g']
    ]
    subs = dict(
        (b, lg.Const('{}_{}'.format(k, i), b.sort))
        for k, v in named_binders.iteritems()
        for i, b in enumerate(v)
    )
    if debug.get():
        print "=" * 80 + "\nsubs:" + "\n"*3
        for k in sorted(named_binders.keys()):
            v = named_binders[k]
            for i, b in enumerate(v):
                print '{}_{}'.format(k, i), ' : ', b
        print "=" * 80 + "\n"*3
    mod_pass(lambda ast: ilu.replace_named_binders_ast(ast, subs))

    if debug.get():
        print "=" * 80 + "\nafter replace_named_binders" + "\n"*3
        print_module(mod)
        print "=" * 80 + "\n"*3

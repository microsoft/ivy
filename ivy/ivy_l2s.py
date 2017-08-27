        # self.definitions = []  # TODO: these are actually "derived" relations
        # self.labeled_axioms = []
        # self.labeled_props = []
        # self.labeled_inits = []
        # self.labeled_conjs = []  # conjectures
        # self.actions = {}
        # self.public_actions = set()

        # self.initializers = [] # list of name,action pairs

        # self.sig

from collections import defaultdict
from itertools import chain

from ivy_printer import print_module
from ivy_actions import (AssignAction, Sequence, ChoiceAction,
                         AssumeAction, AssertAction, HavocAction,
                         concat_actions)
import logic as lg
import ivy_logic_utils as ilu

def forall(vs, body):
    return lg.ForAll(vs, body) if len(vs) > 0 else body


def l2s(mod, lf):

    #print ilu.used_symbols_asts(mod.labeled_conjs)
    #print '='*40
    #print list(ilu.named_binders_asts(mod.labeled_conjs))
    # modify mod in place

    l2s_waiting = lg.Const('l2s_waiting', lg.Boolean)
    l2s_frozen = lg.Const('l2s_frozen', lg.Boolean)
    l2s_saved = lg.Const('l2s_saved', lg.Boolean)
    l2s_d = lambda sort: lg.Const('l2s_d',lg.FunctionSort(sort,lg.Boolean))
    l2s_a = lambda sort: lg.Const('l2s_a',lg.FunctionSort(sort,lg.Boolean))
    l2s_w = lambda vs, t: lg.NamedBinder('l2s_w', vs, t)
    l2s_s = lambda vs, t: lg.NamedBinder('l2s_s', vs, t)
    l2s_g = lambda vs, t: lg.NamedBinder('l2s_g', vs, t)
    old_l2s_g = lambda vs, t: lg.NamedBinder('old_l2s_g', vs, t)

    uninterpreted_sorts = [s for s in mod.sig.sorts.values() if type(s) is lg.UninterpretedSort]

    #for k, v in mod.sig.sorts.items() + mod.sig.symbols.items():
    #    print repr(k), ':', repr(v)
    #    print
    #print

    reset_a = [
        AssignAction(l2s_a(s)(v), l2s_d(s)(v))
        for s in uninterpreted_sorts
        for v in [lg.Var('X',s)]
    ]

    named_binders = defaultdict(list) # dict mapping names to lists of (vars, body)
    for b in ilu.named_binders_asts(mod.labeled_conjs):
        named_binders[b.name].append((b.variables, b.body))
    named_binders = defaultdict(list,((k,list(set(v))) for k,v in named_binders.iteritems()))
    # TODO: the above appears twice in this file, why? fix it!
    # TODO: normalize named binders, so variable names won't be significant

    # DONE?: change to_wait to be from the tableau or conjectures, this is a mock
    to_wait = [] # list of (variables, term)
    # to_wait += [((), c) for c in mod.sig.symbols.values() if c.sort == lg.Boolean]
    # to_wait += [
    #     (vs, f(*vs))
    #     for f in mod.sig.symbols.values()
    #     if isinstance(f.sort, lg.FunctionSort) and f.sort.range == lg.Boolean
    #     for vs in [tuple(lg.Var('X{}'.format(i), s) for i,s in enumerate(f.sort.domain))]
    # ]
    to_wait = named_binders['l2s_w']
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
            lg.And(l2s_w(vs,t)(*vs), lg.Not(t), lg.Not(lg.Globally(lg.Not(t))))
        )
        for vs, t in to_wait
    ]

    # tableau construction (sort of)
    temporals = [] # TODO get from temporal axioms and temporal properties
    temporals += list(ilu.temporals_asts(
        mod.labeled_conjs +
        mod.labeled_axioms +
        mod.labeled_props +
        [lf]
    ))
    temporals += [lg.Globally(lg.Not(t)) for vs, t in to_wait]
    print '='*40
    for t in temporals:
        print t, '\n'
    print '='*40
    to_g = [ # list of (variables, formula)
        (tuple(sorted(ilu.variables_ast(tt))), tt)
        for t in temporals
        for tt in [t.body if type(t) is lg.Globally else
                   lg.Not(t.body) if type(t) is lg.Eventually else 1/0]
    ]
    to_g = list(set(to_g))
    print '='*40
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
# lg.Or(
#             l2s_g(vs, t)(*vs),
#             lg.And(lg.Not(t), l2s_ga(vs, t)(*vs))
#         )),
    ]]

    # DONE?: change to_save to be taken from the conjectures
    to_save = [] # list of (variables, term) corresponding to l2s_s
    # for f in mod.sig.symbols.values():
    #     if isinstance(f.sort, lg.FunctionSort):
    #         vs = tuple(lg.Var('X{}'.format(i), s) for i,s in enumerate(f.sort.domain))
    #         to_save.append((vs, f(*vs)))
    #     else:
    #         to_save.append(((), f))
    to_save = named_binders['l2s_s']
    save_state = [
        AssignAction(l2s_s(vs,t)(*vs), t)
        for vs, t in to_save
    ]

    fair_cycle = [l2s_saved]
    fair_cycle += done_waiting
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
    assert_no_fair_cycle = AssertAction(lg.true) #AssertAction(lg.Not(lg.And(*fair_cycle)))
    assert_no_fair_cycle.lineno = lf.lineno

    edge = lambda s1, s2: [
        AssumeAction(s1),
        AssignAction(s1, lg.false),
        AssignAction(s2, lg.true),
    ]
    change_monitor_state = [ChoiceAction(
        # waiting -> frozen
        Sequence(*(
            edge(l2s_waiting, l2s_frozen) +
            [AssumeAction(x) for x in done_waiting] +
            reset_a
        )),
        # frozen -> saved
        Sequence(*(
            edge(l2s_frozen, l2s_saved) +
            save_state +
            reset_w
        )),
        # stay in same state (self edge)
        Sequence(),
    )]

    add_consts_to_d = [
        AssignAction(l2s_d(s)(c), lg.true)
        for s in uninterpreted_sorts
        for c in mod.sig.symbols.values() if c.sort == s
    ]
    # TODO add all ground terms, not just consts (if stratified)

    # TODO: add conjectures that constants are in d and a

    for a in mod.public_actions:
        action = mod.actions[a]
        add_params_to_d = [
            AssignAction(l2s_d(p.sort)(p), lg.true)
            for p in action.formal_params
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
    l2s_init += [AssumeAction(lg.Not(lf.formula))]
    # TODO: check assume [~property]
    mod.initializers.append(('l2s_init', Sequence(*l2s_init)))

    print "=" * 80 + "\n"*3
    print_module(mod)
    print "=" * 80 + "\n"*3

    # module pass helper funciton
    def mod_pass(transform):
        mod.labeled_conjs = [transform(x) for x in mod.labeled_conjs]
        for a in mod.public_actions:
            action = mod.actions[a]
            new_action = transform(action)
            new_action.lineno = action.lineno
            new_action.formal_params = action.formal_params
            new_action.formal_returns = action.formal_returns
            mod.actions[a] = new_action
        mod.initializers = [(x, transform(y)) for x, y in mod.initializers]

    # now replace all temporal operators by l2s_g
    l2s_gs = set()
    def _l2s_g(vs, t):
        vs = tuple(vs)
        res = l2s_g(vs, t)
        l2s_gs.add((vs,t))
        return res
    mod_pass(lambda ast: ilu.replace_temporals_by_named_binder_g_ast(ast, _l2s_g))

    #print "=" * 80 + "\n"*3
    #print_module(mod)
    #print "=" * 80 + "\n"*3

    # now replace the named binders by fresh relations

    named_binders = defaultdict(list) # dict mapping names to lists of (vars, body)
    for b in ilu.named_binders_asts(chain(
            mod.labeled_conjs,
            mod.actions.values(),
            (y for x,y in mod.initializers),
    )):
        named_binders[b.name].append(b)
    named_binders = defaultdict(list, ((k,list(sorted(set(v)))) for k,v in named_binders.iteritems()))
    # make sure old_l2s_g is consistent with l2s_g
    # assert len(named_binders['l2s_g']) == len(named_binders['old_l2s_g'])
    named_binders['old_l2s_g'] = [
        lg.NamedBinder('old_l2s_g', b.variables, b.body)
        for b in named_binders['l2s_g']
    ]
    subs = dict(
        (b, lg.Const('{}_{}'.format(k, i), b.sort))
        for k, v in named_binders.iteritems()
        for i, b in enumerate(v)
    )
    #for k, v in subs.items():
    #    print k, ' : ', v, '\n'
    mod_pass(lambda ast: ilu.replace_named_binders_ast(ast, subs))

    print "=" * 80 + "\n"*3
    print_module(mod)
    print "=" * 80 + "\n"*3

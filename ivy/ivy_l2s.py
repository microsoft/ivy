        # self.definitions = []  # TODO: these are actually "derived" relations
        # self.labeled_axioms = []
        # self.labeled_props = []
        # self.labeled_inits = []
        # self.labeled_conjs = []  # conjectures
        # self.actions = {}
        # self.public_actions = set()

        # self.initializers = [] # list of name,action pairs

        # self.sig

from ivy_printer import print_module
from ivy_actions import (AssignAction, Sequence, ChoiceAction,
                         AssumeAction, AssertAction, concat_actions)
import logic as lg
import ivy_logic_utils as ilu

def forall(vs, body):
    return lg.ForAll(vs, body) if len(vs) > 0 else body


def l2s(mod, lf):

    print ilu.used_symbols_asts(mod.labeled_conjs)
    print '='*40
    print list(ilu.named_binders_asts(mod.labeled_conjs))
    # modify mod in place

    l2s_waiting = lg.Const('l2s_waiting', lg.Boolean)
    l2s_frozen = lg.Const('l2s_frozen', lg.Boolean)
    l2s_saved = lg.Const('l2s_saved', lg.Boolean)
    l2s_d = lambda sort: lg.Const('l2s_d',lg.FunctionSort(sort,lg.Boolean))
    l2s_a = lambda sort: lg.Const('l2s_a',lg.FunctionSort(sort,lg.Boolean))
    l2s_w = lambda vs, t: lg.NamedBinder('l2s_w', vs, t)
    l2s_s = lambda vs, t: lg.NamedBinder('l2s_s', vs, t)

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

    # TODO: change wait_for to be from the tableau or conjectures, this is a mock
    wait_for = [] # list of (variables, term)
    wait_for += [((), c) for c in mod.sig.symbols.values() if c.sort == lg.Boolean]
    wait_for += [
        (vs, f(*vs))
        for f in mod.sig.symbols.values()
        if isinstance(f.sort, lg.FunctionSort) and f.sort.range == lg.Boolean
        for vs in [tuple(lg.Var('X{}'.format(i), s) for i,s in enumerate(f.sort.domain))]
    ]
    done_waiting = [
        forall(vs, lg.Not(l2s_w(vs,t)(*vs)))
        for vs, t in wait_for
    ]
    reset_w = [
        AssignAction(
            l2s_w(vs,t)(*vs),
            lg.And(*(l2s_d(v.sort)(v) for v in vs))
        )
        for vs, t in wait_for
    ]
    update_w = [
        AssignAction(
            l2s_w(vs,t)(*vs),
            lg.And(l2s_w(vs,t)(*vs), lg.Not(t), lg.Not(lg.Globally(lg.Not(t))))
        )
        for vs, t in wait_for
    ]

    # TODO: change to_save to be taken from the conjectures
    to_save = [] # list of (variables, term) corresponding to l2s_s
    for f in mod.sig.symbols.values():
        if isinstance(f.sort, lg.FunctionSort):
            vs = tuple(lg.Var('X{}'.format(i), s) for i,s in enumerate(f.sort.domain))
            to_save.append((vs, f(*vs)))
        else:
            to_save.append(((), f))
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
            [action] +
            add_consts_to_d +
            update_w +
            [AssertAction(lg.Not(lg.And(*fair_cycle)))]
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
    # TODO: assume [~property]
    mod.initializers.append(('l2s_init', Sequence(*l2s_init)))

    print "=" * 80 + "\n"*3
    print_module(mod)

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
                         AssumeAction, concat_actions)
import logic as lg
import ivy_logic_utils as ilu

def l2s(mod, lf):
    # modify mod in place

    l2s_waiting = lg.Const('l2s_waiting', lg.Boolean)
    l2s_frozen = lg.Const('l2s_frozen', lg.Boolean)
    l2s_saved = lg.Const('l2s_saved', lg.Boolean)
    l2s_d = lambda sort: lg.Const('l2s_d',lg.FunctionSort(sort,lg.Boolean))
    l2s_a = lambda sort: lg.Const('l2s_a',lg.FunctionSort(sort,lg.Boolean))
    l2s_w = lambda x: lg.Binder('l2s_w', [], x)
    l2s_s = lambda vs, t: lg.Binder('l2s_s', vs, t)

    uninterpreted_sorts = [s for s in mod.sig.sorts.values() if type(s) is lg.UninterpretedSort]

    #for k, v in mod.sig.sorts.items() + mod.sig.symbols.items():
    #    print repr(k), ':', repr(v)
    #    print
    #print

    # TODO: change wait_for to be from the tableau, this is a mock
    wait_for = [c for c in mod.sig.symbols.values() if c.sort == lg.Boolean]
    wait_for += [
        f(*[lg.Var('X{}'.format(i), s) for i,s in enumerate(f.sort.domain)])
        for f in mod.sig.symbols.values()
        if isinstance(f.sort, lg.FunctionSort) and f.sort.range == lg.Boolean]
    done_waiting = [ilu.close_epr(lg.Not(l2s_w(w))) for w in wait_for]

    # TODO: change to_save to be taken from the conjectures
    to_save = [] # list of (variables, term) corresponding to l2s_s
    for f in mod.sig.symbols.values():
        if isinstance(f.sort, lg.FunctionSort):
            vs = tuple(lg.Var('X{}'.format(i), s) for i,s in enumerate(f.sort.domain))
            to_save.append((vs, f(*vs)))
        else:
            to_save.append(((), f))

    prelude = ChoiceAction(
        # waiting -> frozen
        Sequence(*([
            AssumeAction(l2s_waiting)
        ] +[
            AssumeAction(x) for x in done_waiting
        ] + [
            AssignAction(l2s_waiting, lg.false),
            AssignAction(l2s_frozen, lg.true),
        ] + [
            AssignAction(l2s_a(s)(v), l2s_d(s)(v))
            for s in uninterpreted_sorts
            for v in [lg.Var('X',s)]
        ])),
        # frozen -> saved
        Sequence(*([
            AssumeAction(l2s_frozen),
            AssignAction(l2s_frozen, lg.false),
            AssignAction(l2s_saved, lg.true),
        ] + [
            AssignAction(l2s_s(vs,t)(*vs) if len(vs) > 0 else l2s_s(vs,t), t)
            for vs, t in to_save
            # TODO copy relations and functions
            # TODO reset l2s_w from l2s_d
        ])),
        # stay
        Sequence(),
    )

    add_consts_to_d = [
        AssignAction(l2s_d(s)(c), lg.true)
        for s in uninterpreted_sorts
        for c in mod.sig.symbols.values() if c.sort == s
    ]

    # TODO: add conjectures that constants are in d and a

    for a in mod.public_actions:
        action = mod.actions[a]
        add_params_to_d = [
            AssignAction(l2s_d(p.sort)(p), lg.true)
            for p in action.formal_params
        ]
        new_action = concat_actions(*(
            [prelude] +
            add_params_to_d +
            [action] +
            add_consts_to_d
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
    # TODO: initialize w
    # TODO: assume [~property]
    mod.initializers.append(('l2s_init', Sequence(*l2s_init)))

    print "=" * 80 + "\n"*3
    print_module(mod)

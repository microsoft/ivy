#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy_module as im
import ivy_actions as ia
import logic as lg
import ivy_logic as il
import ivy_transrel as tr
import ivy_logic_utils as ilu
import ivy_utils as iu
import ivy_art as art
import ivy_interp as itp
import ivy_theory as thy
import ivy_ast
import ivy_proof
import ivy_trace

def check_isolate(n_steps):
    
    step_action = ia.env_action(None)

    conjectures = im.module.conjs
    conj = ilu.and_clauses(*conjectures)

    used_names = frozenset(x.name for x in il.sig.symbols.values())
    def witness(v):
        c = lg.Const('@' + v.name, v.sort)
        assert c.name not in used_names
        return c
    clauses = ilu.dual_clauses(conj, witness)

    ag = art.AnalysisGraph()
    with ag.context as ac:
#                post = ac.new_state(ag.init_cond)
        ag.add_initial_state(ag.init_cond)
        post = ag.states[0]
    if 'initialize' in im.module.actions:
        init_action = im.module.actions['initialize']
        post = ag.execute(init_action, None, None, 'initialize')

    for n in range(n_steps + 1):
        print 'Checking invariants at depth {}...'.format(n)
        res = ivy_trace.check_final_cond(ag,post,clauses,[],True)
        if res is not None:
            print 'BMC with bound {} found a counter-example...'.format(n)
            print
            print res
            exit(0)
        post = ag.execute(step_action)
            

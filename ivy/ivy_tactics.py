#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy_proof as pf
import ivy_actions as ia
import ivy_temporal as tm
import ivy_logic as lg
import ivy_utils as iu
import ivy_trace as tr
import ivy_logic_utils as lu
import ivy_proof as pr

# This tactic reduces a safety property to initiatation and consecution
# subgoals. TODO: we lose the annotation here, so we can't extract a
# trace. Need to add the annotation to the subgoals.

def vcgen(self,decls,proof):
    goal = decls[0]
    conc = pr.goal_conc(goal)
    decls = decls[1:]
    if not isinstance(conc,tm.TemporalModels) or not lg.is_true(conc.fmla):
        raise iu.IvyError(self,'vcgen tactic applies only to safety properties')
    model = conc.model
    initiation = tr.make_vc(model.init,postcond=model.invars)
    env = tm.env_action(model.bindings)
    consecution = tr.make_vc(env,precond=model.invars+model.asms,postcond=model.invars)
    goal1 = pr.make_goal(proof.lineno,'initiation',[],lg.Not(lu.clauses_to_formula(initiation)))
    goal2 = pr.make_goal(proof.lineno,'consecution',[],lg.Not(lu.clauses_to_formula(consecution)))
    return [goal1,goal2] + decls[1:]

pf.register_tactic('vcgen',vcgen)
    

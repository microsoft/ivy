#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy_proof as pf
import ivy_actions as ia
import ivy_temporal as tm
import ivy_logic as lg
import ivy_utils as iu
import ivy_trace as tr
import ivy_transrel as itr
import ivy_logic_utils as lu
import ivy_proof as pr
import ivy_ast as ias

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
    goal1 = triple_to_goal(proof.lineno,'initiation',model.init,postcond=model.invars)
    goal2 = triple_to_goal(proof.lineno,'consecution',tm.env_action(model.bindings),
                           precond=model.invars+model.asms,postcond=model.invars)
    return [goal1,goal2] + decls[1:]

def vc_to_goal(lineno,name,vc,action):
    sks = list(iu.unique(s for s in lu.symbols_clauses(vc) if itr.is_skolem(s)))
    prems = [ias.ConstantDecl(s) for s in sks]
    return pr.make_goal(lineno,name,prems,lg.Not(lu.clauses_to_formula(vc)),
                        annot=(action,vc.annot))

def triple_to_goal(lineno,name,action,precond=[],postcond=[]):
    vc = tr.make_vc(action,precond,postcond)
    return vc_to_goal(lineno,name,vc,action)

pf.register_tactic('vcgen',vcgen)
    
def skolemize(self,decls,proof):
    goal = decls[0]
    goal = pr.skolemize_goal(goal)
    return [goal] + decls[1:]

pf.register_tactic('skolemize',skolemize)

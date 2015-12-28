#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy
import ivy_interp as itp
import ivy_actions as act
import ivy_utils as utl
import ivy_logic_utils as lut
import ivy_ui as ui
import ivy_logic as lg

class AC(act.ActionContext):
    def __init__(self,assertions,actions,domain):
        self.assertions = {}
        self.assertions.update(actions)
        for x in assertions:
            rhs = eval_assert_rhs(x.args[1],domain)
            self.assertions[x.args[0].rep] = rhs
        self.domain = domain
    def get(self,sym):
        return self.assertions.get(sym,None)

def analyze_state_rec(ag,state):
    if hasattr(state,'id'):
        return # state already visited
    if hasattr(state,'pred') and state.pred:
        analyze_state_rec(ag,state.pred)
        ag.add(state)
        ag.transitions.append((state.pred,state.action,state.action_name,state))
    elif hasattr(state,'join_of'):
        for x in state.join_of: analyze_state_rec(ag,x)
        ag.add(state)
        for x in state.join_of:
            ag.transitions.append((x,None,'join',state))
    else:
        if not isinstance(state.clauses,list):
            state.clauses = lut.formula_to_clauses(state.clauses)
        ag.add(state)

def analyze_state(ag,state,clauses):
#    print "cex: {}".format(clauses)
    ag.states = []
    analyze_state_rec(ag,state)
    state.clauses.extend(clauses)
    ui.ui_main_loop(ag)
    
def eval_assert_rhs(rhs,domain):
    if not isinstance(rhs,act.RME):
        rhs = act.RME(log.And(),[],rhs)
    return itp.eval_state(rhs,act.ActionContext(domain))

if __name__ == "__main__":
    ag = ivy.ivy_init()
    ac = AC(ag.assertions,ag.actions,ag.domain)
    with utl.ErrorPrinter():
        for ass in ag.assertions:
            lhs = ass.args[0].rep
            rhs = ass.args[1]
            rhs_state = eval_assert_rhs(rhs,ag.domain)
            try:
                if lhs in ag.predicates:
                    with ac:
                        lhs_state = itp.eval_state(ag.predicates[lhs],ac)
                elif lhs in ag.actions:
                    with ac:
                        lhs_state = itp.eval_state(act.entry(lg.Not(rhs_state.precond)),ac)
                        lhs_state = itp.apply_action(ass,lhs,ag.actions[lhs],lhs_state)
                else:
                    raise utl.IvyError(ass,"{} undefined".format(lhs))
                print "lhs_state: %s" %  lhs_state.clauses
                print "rhs_fmla: %s" %  rhs_state.clauses
                cex = ag.domain.order(lhs_state,rhs_state)
                if not cex:
                    print repr(utl.IvyError(ass,"assertion does not hold"))
                    analyze_state(ag,lhs_state,cex.clauses)
            except itp.IvyActionFailedError as err:
                print repr(err)
                print err.error_state.clauses
                analyze_state(ag,err.error_state,[])
                

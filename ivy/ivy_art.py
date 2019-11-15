#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy_actions
from ivy_interp import *
import ivy_utils as iu
import ivy_module as im
from cy_elements import CyElements
from string import *
import copy
import functools
import pickle
import ivy_actions


################################################################################
#
#  Class of Abstract Reachability Graphs
#
#
# An ARG is a set of nodes, which may be derived from other nodes by
# node expressions. Each node has an associated value, which may be
# concrete or abstract state. In addition, there is a covering
# relation between nodes.
#
################################################################################


########################################
#
# The context object AC sets an ARG as the context for evaluating node
# expressions

class AC(ivy_actions.ActionContext):
    def __init__(self,ag,no_add=False):
        self.assertions = {}
        self.actions,self.domain,self.add = ag.actions,ag.domain,ag.add
        self.no_add = no_add
    def get(self,sym):
        return self.actions.get(sym,None)
    def new_state(self,clauses, exact = False, domain = None, expr = None):
        res = self.domain.new_state(clauses)
        if not self.no_add:
            self.add(res,expr)
        if exact:
            res.unders = [self.domain.new_state(clauses)]
        return res

########################################
#
# A counterexample is a thing that evaluates to false and contains
# information on why a property is false.

class Counterexample(object):
    def __init__(self,clauses,state,conc,msg):
        self.clauses, self.state, self.msg, self.conc = clauses, state, msg, conc
    def __nonzero__(self):
        return False

########################################
#
# option to abstract the initial state

option_abs_init = iu.BooleanParameter("abs_init",False)


########################################
#
# The class of ARG's

class AnalysisGraph(object):
    def __init__(self,module = None, pvars = [], initializer=None):
        if module == None:
            module = im.module  # use the current module if not specified
        self.domain = module
        self.states = []
        self.transitions = [] # TODO: redundant, remove
        self.covering = []
        self.pvars = pvars  # TODO: remove this field
        self.state_graphs = []

        # delegate some former fields to Module for compat

        self.actions = module.actions
        self.predicates = module.predicates
        self.assertions = module.assertions
        self.mixins = module.mixins
        self.isolates = module.isolates
        self.exports = module.exports
        self.delegates = module.delegates
        self.public_actions = module.public_actions
        self.init_cond = module.init_cond
        
        # TODO: may not really want this
        if initializer is not None:
            self.initialize(initializer)

    @property
    def context(self):
        return AC(self)

    def add_initial_state(self, ic = None, abstractor = None):
        if ic == None:
            ic = im.init_cond
        s = self.domain.new_state(ic)
        if self.domain.initializers:
            action = ivy_actions.Sequence(*[a for n,a in self.domain.initializers])
            action = ivy_actions.env_action(action,'init')
            s = action_app(action,s)
            with AC(self,no_add=True):
                with EvalContext(check=False):
                    s2 = eval_state(s)
            s2.expr = s
            self.add(s2)
        else:
            s2 = self.domain.new_state(ic)
            self.add(s2,s)
        if abstractor:
            abstractor(s2)

    def initialize(self, abstractor):
        ac = self.context
        with ac:
            if self.predicates:
                if not im.module.init_cond.is_true():
                    raise IvyError(None,"init and state declarations are not compatible");
                for n,p in self.predicates.iteritems():
                    s = eval_state_facts(p)
                    if s is not None:
                        s.label = n
            else:
                self.add_initial_state(self.domain.init_cond,abstractor)


    def state_actions(self,state):
        if hasattr(state,'label') and state.label != None:
            return [state_equation(post,expr) for post,e in self.predicates.iteritems() for expr in eval_state_actions(e,state)]
        return [state_equation(None,action_app(a,state)) for a in self.actions if a in self.public_actions]

    def do_state_action(self,equation,abstractor):
        with self.context:
            s = eval_state(equation.args[1])
            s.label = equation.args[0]
        if abstractor:
            abstractor(s)
        return s

    def recalculate(self,transition,abstractor = None):
        prestate,op,label,poststate = transition
        if not op and label == 'join':
            ps = self.join_states(poststate.join_of[0],poststate.join_of[1],abstractor)
        else:
            if label in self.actions:
                op = self.actions[label]
            ps = self.post_state(op,prestate,abstractor)
        self.replace_state(poststate,ps)
        return poststate

    def post_state(self,op,pre_state,abstractor):
        s = concrete_post(op.update(pre_state.domain,pre_state.in_scope),pre_state)
        s.action = op
        if abstractor:
            abstractor(s)
        return s

    def replace_state(self,poststate,ps):
        ps.id = poststate.id
        ps.label = poststate.label
        poststate.__dict__ = ps.__dict__.copy()    # yikes!
        for c in list(self.covering):
            covered,covering = c
            if covered.id == poststate.id:
                self.covering.remove(c)
                self.cover(poststate,covering)
        print "recalculated state %s: %s" % (poststate.id,poststate.clauses)

    def recalculate_state(self,state,abstractor=None):
        if hasattr(state,'pred') and state.pred:
            ps = concrete_post(state.update,state.pred)
            if abstractor:
                abstractor(ps)
            self.replace_state(state,ps)
        elif hasattr(state,'join_of') and state.join_of:
            ps = self.join_states(state.join_of[0],state.join_of[1],abstractor)
            self.replace_state(state,ps)

    def execute(self,op,prestate = None, abstractor = None, label=None):
#        print "exec: %s" % op
        if prestate == None:
            prestate = self.states[len(self.states)-1]
        poststate = self.post_state(op,prestate,abstractor)
        expr = action_app(op if label is None else label,prestate) 
#        label = label if label else repr(op)
        self.add(poststate,expr)
#        print "post state %s: %s" % (poststate.id,poststate.clauses)
        return poststate

    def execute_action(self,name,prestate = None, abstractor = None):
        return self.execute(self.actions[name],prestate, abstractor, name)

    def join_states(self,state1,state2,abstractor = None):
#        if state1.label != state2.label:
#            raise IvyError(None,"Cannot join instances of different states")
        joined_state = concrete_join(state1,state2)
        if abstractor:
            abstractor(joined_state)
        joined_state.label = state1.label
        return joined_state

    def join(self,state1,state2 = None, abstractor = None):
        if state2 == None:
            state2 = self.states[len(self.states)-1]
        joined_state = self.join_states(state1,state2,abstractor)
        self.add(joined_state,state_join(state1,state2))
        print "joined state: %s" % joined_state.clauses
        return joined_state

    def cover(self,covered_node,covering_node):
        if covered_node.domain.order(covered_node,covering_node):
            print "Covering succeeded: %s %s" % (covered_node.id, covering_node.id)
            self.covering.append((covered_node,covering_node))
            return True
        else:
            print "Covering failed"
            return False

    def is_covered(self,node):
        return any(x.id == node.id for x,y in self.covering)

    def unreachable(self,covered_node):
        covering_node = State(covered_node.domain,[[]])
        if covered_node.domain.order(covered_node,covering_node):
            print "Unreachable: %s" % covered_node.id
            covered_node.clauses = [[]]
            return True
        else:
            print "Unreachability check failed"
            return False

    def show_core(self,clause_str,state = None):
        clause = to_clause(clause_str)
        if state == None:
            state = self.states[len(self.states)-1]
        print state.domain.get_core(state,clause)

    def add(self,state,expr=None):
        state.id = len(self.states)
        self.states.append(state)
        if expr is not None:
            state.expr = expr
            if is_action_app(expr):
                assert len(expr.args) == 1
                assert isinstance(expr.args[0],State)
                if not isinstance(expr.rep,str):
                    action = expr.rep
                    label = label_from_action(action)
                else:
                    assert expr.rep in self.actions, expr.rep
                    action = self.actions[expr.rep]
                    label = expr.rep
                self.transitions.append((expr.args[0],action,label,state))
            elif is_state_join(expr):
                for js in expr.args:
                    assert isinstance(js,State)
                    self.transitions.append((js,None,"join",state))

    # execute action in a sub-graph

    def call_action(self,name,op,prestate):
        ag = AnalysisGraph(self.domain,self.pvars)
        ag.apply_update = self.apply_update
        ag.add(copy.copy(prestate))
        op(ag)
        op = AnalysisSubgraph(name,ag)
        poststate = ag.states[len(ag.states)-1]
        poststate = copy.copy(poststate)
        return poststate

    def call(self,name,op,prestate = None):
        if prestate == None:
            prestate = self.states[len(self.states)-1]
        op,poststate = self.call_action(name,prestate)
        self.add(poststate)
        self.transitions.append((prestate,op,name,poststate))
        return poststate

    def dependencies(self,s):
        if hasattr(s,'pred'): return [s.pred]
        elif hasattr(s,'join_of'): return s.join_of
        return []

    def delete(self,state):
        id = state.id
        state.id = -1
        for i in range(id+1,len(self.states)):
            s = self.states[i]
            if any(t.id == -1 for s in self.dependencies(s)):
                s.id = -1
        self.remove_marked_states()

    def remove_marked_states(self):
        self.states = [s for s in self.states if s.id != -1]
        for i,s in enumerate(self.states):
            s.id = i
        self.transitions = [t for t in self.transitions if t[0].id != -1 and t[-1].id != -1]
        self.covering = [t for t in self.covering if t[0].id != -1 and t[-1].id != -1]

    def concept_graph(self,state,standard_graph,clauses=None):
        if clauses == None:
            clauses = state.clauses
        bg = self.domain.background_theory(state.in_scope)
#        print "bg: {}".format(bg)
        sg = standard_graph(state)
        # TODO: following shouldn't be needed.
        sg.current.set_state(and_clauses(clauses,bg))
        sg.current.set_concrete([])  # TODO: get rid of this
        return sg

    def transition_to(self,state):
        for t in self.transitions:
            if t[-1] is state:
                return t
        return None

    def get_history(self,state,bound=None):
        if hasattr(state,'pred') and state.pred != None and bound != 0:
            next_bound = None if bound is None else bound - 1
            return history_forward_step(self.get_history(state.pred, next_bound), state)
        else:
            return new_history(state)

    def bmc(self,state,error_cond,other_art=None,bound=None,_get_model_clauses=None):
        history = self.get_history(state, bound)
#        history = history.assume(error_cond)
        bmc_res = history_satisfy(history,state,_get_model_clauses,final_cond=error_cond)
        if bmc_res == None:
            return None
        universe,path = bmc_res
        if other_art is None:
            other_art = AnalysisGraph(self.domain,self.pvars)
            other_art.actions = self.actions
        self.copy_path(state,other_art,bound)
        for state,value in zip(other_art.states[-len(path):],path):
            state.value = value
            state.universe = universe
        return other_art

    def check_bounded_safety(self,state,_get_model_clauses=None,bound=None):
        postcond = get_state_assertions(state)
        if postcond != None:
            res = self.bmc(state,postcond,_get_model_clauses=_get_model_clauses,bound=bound)
            if res != None:
                return res
        # currently checks failure only in last action
        if state.expr != None:
            fail = State(expr = fail_expr(state.expr))
            res = self.bmc(fail,true_clauses(),_get_model_clauses=_get_model_clauses,bound=bound)
            return res
        return True

    def copy_path(self,state,other,bound=None):
        other_state = State(other.domain)
        other_state.arg_node = state
        if hasattr(state,'pred') and state.pred != None and bound != 0:
            next_bound = None if bound is None else bound - 1
            pred = self.copy_path(state.pred,other,next_bound)
            expr = state.expr
            other.add(other_state,action_app(expr.rep,pred))
        else:
            other.add(other_state)
        return other_state

    def check_safety(self,state):
        for asn in self.assertions:
            cex = check_state_assertion(state,asn)
            if not cex:
                return Counterexample(cex.clauses,state,None,"assertion failure") # safety property failed
        if hasattr(state,'expr') and state.expr != None:
            with AC(self,no_add=True):
                try:
                    eval_state(state.expr)
                except IvyActionFailedError as err:
                    return Counterexample(err.error_state.clauses,err.error_state.pred,err.conc,repr(err))
        return True

    def construct_transitions_from_expressions(self):
        for state in self.states:
            if hasattr(state,'expr') and is_action_app(state.expr):
                expr = state.expr
                prestate,op,label,poststate = expr.args[0],expr.rep,label_from_action(expr.rep),state
                self.transitions.append((prestate,op,label,poststate))

    def decompose_state(self,state):
        if hasattr(state,'expr') and state.expr != None:
            if hasattr(state.expr,'subgraph'):
                return state.expr.subgraph
            other_art = AnalysisGraph(self.domain)
            with AC(other_art):
                res = decompose_action_app(state,state.expr)
                if res != None:
                    other_art.construct_transitions_from_expressions()
                    return other_art
        return None

    def make_concrete_trace(self,state,conc):
        # TODO
        return
        
    def decompose_edge(self,transition):
        prestate,op,label,poststate = transition
        return self.decompose_state(poststate)

    @property
    def uncovered_states(self):
        covered = set(x for x,y in self.covering)
        joined = set()
        for state in self.states:
            if hasattr(state,'expr') and state.expr is not None:
                if any(s.id in covered
                       for s in states_state_expr(state.expr)):
                    covered.add(state)
                if is_state_join(state.expr):
                    for s in state.expr.args:
                        joined.add(s)
        return [s for s in self.states if s not in covered and s not in joined]

    def fixedpoint_candidate(self, join = state_join):
        fpc = defaultdict(lambda:[])
        for state in self.uncovered_states:
            if hasattr(state,'label'):
                fpc[state.label].append(state)
        print "fpc = {}".format(fpc)
        return defaultdict(bottom_state,((x,join(*y)) for x,y in fpc.iteritems()))

    def state_extensions(self,state, join = state_join):
        sas = self.state_actions(state)
        fpc = self.fixedpoint_candidate(join)
        for equation in sas:
            with AC(self,no_add=True):
                if not eval_state_order(equation.args[1],fpc[equation.args[0]]):
                    yield equation

    def as_cy_elements(self,dot_layout):
        return dot_layout(render_rg(self),edge_labels=True)

def label_from_action(action):
    if hasattr(action,'label'):
        return action.label
    return iu.pretty(str(action),max_lines=4)

class AnalysisSubgraph(object):
    def __init__(self,op,graph):
        self.op = op
        self.graph = graph
    def __str__(self):
        return self.op
    __repr__ = __str__


def render_rg(rg):
    """
    Render an ivy_arg.AnalysisGraph object

    """
    g = CyElements()

    # add nodes for states
    for s in rg.states:
        if s.is_bottom():
            classes = ['bottom_state']
        else:
            classes = ['state']
        g.add_node(
            obj=s,
            label=str(s.id),
            classes=classes,
            short_info=str(s.id),
            long_info=[str(x) for x in s.clauses.to_open_formula()],
            locked=True,
        )

    # add edges for transitions
    for source, op, label, target in rg.transitions:
        if label == 'join':
            classes = ['transition_join']
            label = 'join'
            info = 'join'
        else:
            classes = ['transition_action']

            # Curly braces don't survive dot (even if they balance). We work around this by replacing them with digraphs
            # and then fixing it later by modding the text of the canvas items. Also, we want our code labels to be left 
            # justified, so we end the lines with \l, which dot recognizes. Note the backslashes are escaped, since this
            # is *not* a special character, it is a two-character sequence.

            label = label.replace('}',']-').replace('{','-[')
            label = label.replace('\n','\\l')+'\\l'
            info = str(op)
        g.add_edge(
            op,
            source,
            target,
            label=label,
            classes=classes,
            short_info=info,
            long_info=info,
        )

    # add edges for covering
    for covered, by in rg.covering:
        g.add_edge(
            'cover',
            covered,
            by,
            label='',
            classes=['cover'],
            short_info='',
            long_info='',
            events=[],
            actions=[],
        )

    return g


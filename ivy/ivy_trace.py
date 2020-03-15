#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
#
#  Construct counterexample traces suitable for viewing with the GUI
#

import ivy_solver as islv
import ivy_art as art
import ivy_interp as itp
import ivy_actions as act
import ivy_logic as lg
import ivy_transrel as itr
import ivy_logic_utils as lut
import ivy_utils as iu
import ivy_module as im
import ivy_solver as slv
from collections import defaultdict

################################################################################
#
# Class of traces
#
# A trace is an ARG representing a counterexample
#
# The trace object acts as a handler for match_action (see ivy_actions.py)
# allowing a trace to be constructed from a counterexample.
#
################################################################################

class TraceBase(art.AnalysisGraph):
    def __init__(self):
        art.AnalysisGraph.__init__(self)
        self.last_action = None
        self.sub = None
        self.returned = None

    def is_skolem(self,sym):
        res = itr.is_skolem(sym) and not (sym.name.startswith('__') and sym.name[2:3].isupper())
        # if not res and self.top_level:
        #     name = sym.name
        #     res = name.startswith('loc:') or name.startswith('fml:')
        return res


    def add_state(self,eqns):
        clauses = lut.Clauses(eqns)
        state = self.domain.new_state(clauses)
        univs = self.get_universes()
        if univs is not None:
            state.universe = univs
        if self.last_action is not None:
            expr = itp.action_app(self.last_action,self.states[-1])
            if self.returned is not None:
                expr.subgraph = self.returned
                self.returned = None
            self.last_action = None
            self.add(state,expr)
        else:
            self.add(state)


    def label_from_action(self,action):
        if hasattr(action,'label'):
            return action.label + '\n'
        lineno = str(action.lineno) if hasattr(action,'lineno') else ''
        return lineno + iu.pretty(str(action),max_lines=4)

    def to_lines(self,lines,hash,indent):
        for state in self.states:
            if hasattr(state,'expr') and state.expr is not None:
                expr = state.expr
                newlines = [indent * '    ' + x + '\n' for x in self.label_from_action(expr.rep).split('\n')]
                lines.extend(newlines)
                if hasattr(expr,'subgraph'):
                    lines.append(indent * '    ' + '{\n')
                    expr.subgraph.to_lines(lines,hash,indent+1)
                    lines.append(indent * '    ' + '}\n')
                lines.append('\n')
            foo = False
            for c in state.clauses.fmlas:
                s1,s2 = map(str,c.args)
                if not(s1 in hash and hash[s1] == s2):
                    hash[s1] = s2
                    if not foo:
                        lines.append(indent * '    ' + '[\n')
                        foo = True
                    lines.append((indent+1) * '    ' + str(c) + '\n')
            if foo:
                lines.append(indent * '    ' + ']\n')
        
    def __str__(self):
        lines = []
        hash = dict()
        self.to_lines(lines,hash,0)
        return ''.join(lines)

                

    def handle(self,action,env):
#        iu.dbg('env')
        if self.sub is not None:
            self.sub.handle(action,env)
        elif isinstance(self.last_action,(act.CallAction,act.EnvAction)) and self.returned is None:
            self.sub = self.clone()
            self.sub.handle(action,env)
        else:
            self.new_state(env)
            self.last_action = action

    def do_return(self,action,env):
        if self.sub is not None:
            if self.sub.sub is not None:
                self.sub.do_return(action,env)
            else:
                self.returned = self.sub
                self.sub = None
                self.returned.new_state(env)
            
    def fail(self):
        self.last_action = itp.fail_action(self.last_action)
    def end(self):
        if self.sub is not None: # return from any unfinished calls, due to assertion failure
            self.sub.end()
            self.returned = self.sub
            self.sub = None
        self.final_state()

class Trace(TraceBase):
    def __init__(self,clauses,model,vocab,top_level=True):
        TraceBase.__init__(self)
        self.clauses = clauses
        self.model = model
        self.vocab = vocab
        self.top_level = top_level
        if clauses is not None:
            ignore = lambda s: islv.solver_name(s) == None
            mod_clauses = islv.clauses_model_to_clauses(clauses,model=model,numerals=True,ignore=ignore)
            self.eqs = defaultdict(list)
            for fmla in mod_clauses.fmlas:
                if lg.is_eq(fmla):
                    lhs,rhs = fmla.args
                    if lg.is_app(lhs):
                        self.eqs[lhs.rep].append(fmla)
                elif isinstance(fmla,lg.Not):
                    app = fmla.args[0]
                    if lg.is_app(app):
                        self.eqs[app.rep].append(lg.Equals(app,lg.Or()))
                else:
                    if lg.is_app(fmla):
                        self.eqs[fmla.rep].append(lg.Equals(fmla,lg.And()))

    def clone(self):
        return Trace(self.clauses,self.model,self.vocab,False)

    def get_universes(self):
        return self.model.universes(numerals=True)
        
    def eval(self,cond):
        truth = self.model.eval_to_constant(cond)
        if lg.is_false(truth):
            return False
        elif lg.is_true(truth):
            return True
        assert False,truth
        
    def get_sym_eqs(self,sym):
        return self.eqs[sym]

    def new_state(self,env):
        sym_pairs = []
        for sym in self.vocab:
            if sym not in env and not itr.is_new(sym) and not self.is_skolem(sym):
                sym_pairs.append((sym,sym))
        for sym,renamed_sym in env.iteritems():
            if not itr.is_new(sym) and not self.is_skolem(sym):
                sym_pairs.append((sym,renamed_sym))
        self.new_state_pairs(sym_pairs,env)

    def new_state_pairs(self,sym_pairs,env):
        eqns = []
        for sym,renamed_sym in sym_pairs:
            rmap = {renamed_sym:sym}
            # TODO: what if the renamed symbol is not in the model?
            for fmla in self.get_sym_eqs(renamed_sym):
                rfmla = lut.rename_ast(fmla,rmap)
                eqns.append(rfmla)
        self.add_state(eqns)
                        
    def final_state(self):
        sym_pairs = []
        for sym in self.vocab:
            if not itr.is_new(sym) and not self.is_skolem(sym):
                sym_pairs.append((sym,sym))
        self.new_state_pairs(sym_pairs,{})


def make_check_art(act_name=None,precond=[]):
    action = act.env_action(act_name)

    ag = art.AnalysisGraph()
    
    pre = itp.State()
    pre.clauses = lut.and_clauses(*precond) if precond else lut.true_clauses()
    pre.clauses.annot = act.EmptyAnnotation()
    
    with itp.EvalContext(check=False): # don't check safety
        post = ag.execute(action, pre)
        post.clauses = lut.true_clauses()

    fail = itp.State(expr = itp.fail_expr(post.expr))

    return ag,post,fail

        
def check_final_cond(ag,post,final_cond,rels_to_min=[],shrink=False,handler_class=None):
    history = ag.get_history(post)
    axioms = im.module.background_theory()
    clauses = history.post
    clauses = lut.and_clauses(clauses,axioms)
    model = slv.get_small_model(clauses,lg.uninterpreted_sorts(),rels_to_min,final_cond=final_cond,shrink=shrink)
    if model is not None:
        failed = ([final_cond] if not isinstance(final_cond,list)
                  else [c.cond() for c in ffcs if c.failed])
        mclauses = lut.and_clauses(*([clauses] + failed))
        vocab = lut.used_symbols_clauses(mclauses)
        handler = (handler_class(mclauses,model,vocab) if handler_class is not None
                   else Trace(mclauses,model,vocab))
        assert all(x is not None for x in history.actions)
        # work around a bug in ivy_interp
        actions = [im.module.actions[a] if isinstance(a,str) else a for a in history.actions]
        action = act.Sequence(*actions)
        act.match_annotation(action,clauses.annot,handler)
        handler.end()
        return handler
    return None

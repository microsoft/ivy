#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy_init
import ivy_interp as itp
import ivy_actions as act
import ivy_utils as utl
import ivy_logic_utils as lut
import ivy_logic as lg
import ivy_utils as iu
import ivy_module as im
import ivy_alpha
import ivy_art
import ivy_interp
import ivy_compiler
import ivy_isolate
import ivy_ast
import ivy_theory as ith
import ivy_transrel as itr
import ivy_solver as islv
import ivy_fragment as ifc
import ivy_proof
import ivy_trace
import ivy_temporal as itmp
import ivy_printer
import ivy_l2s
import ivy_mc
import ivy_bmc

import sys
from collections import defaultdict

diagnose = iu.BooleanParameter("diagnose",False)
coverage = iu.BooleanParameter("coverage",True)
checked_action = iu.Parameter("action","")
opt_trusted = iu.BooleanParameter("trusted",False)
opt_mc = iu.BooleanParameter("mc",False)
opt_trace = iu.BooleanParameter("trace",False)
opt_separate = iu.BooleanParameter("separate",None)

def display_cex(msg,ag):
    if diagnose.get():
        import tk_ui as ui
        iu.set_parameters({'mode':'induction'})
        ui.ui_main_loop(ag)
        exit(1)
    raise iu.IvyError(None,msg)
    
def check_properties():
    if itp.false_properties():
        if diagnose.get():
            print "Some properties failed."
            import tk_ui as ui
            iu.set_parameters({'mode':'induction'})
            gui = ui.new_ui()
            gui.tk.update_idletasks() # so that dialog is on top of main window
            gui.try_property()
            gui.mainloop()
            exit(1)
        raise iu.IvyError(None,"Some properties failed.")
    im.module.labeled_axioms.extend(im.module.labeled_props)
    im.module.update_theory()

def show_counterexample(ag,state,bmc_res):
    universe,path = bmc_res
    other_art = ivy_art.AnalysisGraph()
    ag.copy_path(state,other_art,None)
    for state,value in zip(other_art.states[-len(path):],path):
        state.value = value
        state.universe = universe
    gui_art(other_art)

def gui_art(other_art):
    import tk_ui as ui
#    iu.set_parameters({'mode':'induction'})
    iu.set_parameters({'ui':'cti'})
    gui = ui.new_ui()
    agui = gui.add(other_art)
    gui.tk.update_idletasks() # so that dialog is on top of main window
    gui.tk.mainloop()
    exit(1)

    
def check_conjectures(kind,msg,ag,state):
    failed = itp.undecided_conjectures(state)
    if failed:
        if diagnose.get():
            print "{} failed.".format(kind)
            import tk_ui as ui
            iu.set_parameters({'mode':'induction'})
            gui = ui.new_ui()
            agui = gui.add(ag)
            gui.tk.update_idletasks() # so that dialog is on top of main window
            agui.try_conjecture(state,msg="{}\nChoose one to see counterexample.".format(msg),bound=1)
            gui.tk.mainloop()
            exit(1)
        raise iu.IvyError(None,"{} failed.".format(kind))

def has_temporal_stuff(f):
    return any(True for x in lut.temporals_ast(f)) or any(True for x in lut.named_binders_ast(f))

    
# This is a little tricky. We know that the current module is a valid abstraction of the
# program, thus module |= prop implies prop. We tell the prover to trust us and admit
# prop if module |= prop holds.

def check_temporals():
    mod = im.module
    props = mod.labeled_props
    pmap = dict((prop.id,p) for prop,p in mod.proofs)
    pc = ivy_proof.ProofChecker(mod.labeled_axioms+mod.assumed_invariants,mod.definitions,mod.schemata)
    for prop in props:
        print '\n    The following temporal property is being proved:\n'
        print pretty_lf(prop)
        if prop.temporal:
            proof = pmap.get(prop.id,None)
            model = itmp.normal_program_from_module(im.module)
            subgoal = prop.clone([prop.args[0],itmp.TemporalModels(model,prop.args[1])])
            subgoals = [subgoal]
            subgoals = pc.admit_proposition(prop,proof,subgoals)
            check_subgoals(subgoals)
            
        # else:
        #     # Non-temporal properties have already been proved, so just
        #     # admit them here without proof (in other words, ignore the
        #     # generated subgoals).

        #     pc.admit_proposition(prop,ivy_ast.ComposeTactics())


def usage():
    print "usage: \n  {} file.ivy".format(sys.argv[0])
    sys.exit(1)

def find_assertions(action_name=None):
    res = []
    actions = act.call_set(action_name,im.module.actions) if action_name else im.module.actions.keys()
    for actname in actions:
        action = im.module.actions[actname]
        for a in action.iter_subactions():
            if isinstance(a,act.AssertAction) or isinstance(a,act.Ranking):
                res.append(a)
    return res

def show_assertions():
    for a in find_assertions():
        print '{}: {}'.format(a.lineno,a)

checked_action_found = False

def get_checked_actions():
    cact = checked_action.get()
    if cact and 'ext:'+cact in im.module.public_actions:
        cact = 'ext:'+cact
    if not(cact and cact not in im.module.public_actions):
        global checked_action_found
        checked_action_found = True
        return [cact] if cact else sorted(im.module.public_actions)
    return []

failures = 0

def print_dots():
    print '...',
    sys.stdout.flush()
    

class Checker(object):
    def __init__(self,conj,report_pass=True,invert=True):
        self.fc = lut.formula_to_clauses(conj)
        if invert:
            def witness(v):
                return lg.Symbol('@' + v.name, v.sort)
            self.fc = lut.dual_clauses(self.fc,witness)
        self.report_pass = report_pass
        self.failed = False
    def cond(self):
        return self.fc
    def start(self):
        if self.report_pass:
            print_dots()
    def sat(self):
        print('FAIL')
        global failures
        failures += 1
        self.failed = True
        return not (diagnose.get() or opt_trace.get()) # ignore failures if not diagnosing
    def unsat(self):
        if self.report_pass:
            print('PASS')
    def assume(self):
        return False

def pretty_label(label):
    return "(no name)" if label is None else label

def pretty_lineno(ast):
    return str(ast.lineno) if hasattr(ast,'lineno') else '(internal) '

def pretty_lf(lf,indent=8):
    return indent*' ' + "{}{}".format(pretty_lineno(lf),pretty_label(lf.label))
    
class ConjChecker(Checker):
    def __init__(self,lf,indent=8):
        self.lf = lf
        self.indent = indent
        Checker.__init__(self,lf.formula)
    def start(self):
        print pretty_lf(self.lf,self.indent),
        print_dots()
    
class ConjAssumer(Checker):
    def __init__(self,lf):
        self.lf = lf
        Checker.__init__(self,lf.formula,invert=False)
    def start(self):
        print pretty_lf(self.lf) + "  [proved by tactic]"
    def assume(self):
        return True

class MatchHandler(object):
    def __init__(self,clauses,model,vocab):
#        iu.dbg('clauses')
        self.clauses = clauses
        self.model = model
        self.vocab = vocab
        self.current = dict()
        mod_clauses = islv.clauses_model_to_clauses(clauses,model=model,numerals=True)
#        iu.dbg('mod_clauses')
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
        # for sym in vocab:
        #     if not itr.is_new(sym) and not itr.is_skolem(sym):
        #         self.show_sym(sym,sym)
        self.started = False
        self.renaming = dict()
        print
        print 'Trace follows...'
        print 80 * '*'

    def show_sym(self,sym,renamed_sym):
        if sym in self.renaming and self.renaming[sym] == renamed_sym:
            return
        self.renaming[sym] = renamed_sym
        rmap = {renamed_sym:sym}
        # TODO: what if the renamed symbol is not in the model?
        for fmla in self.eqs[renamed_sym]:
            rfmla = lut.rename_ast(fmla,rmap)
            lhs,rhs = rfmla.args
            if lhs in self.current and self.current[lhs] == rhs:
                continue
            self.current[lhs] = rhs
            print '    {}'.format(rfmla)
        
    def eval(self,cond):
        truth = self.model.eval_to_constant(cond)
        if lg.is_false(truth):
            return False
        elif lg.is_true(truth):
            return True
        assert False,truth
        
    def is_skolem(self,sym):
        res = itr.is_skolem(sym) and not (sym.name.startswith('__') and sym.name[2:3].isupper())
        return res

    def handle(self,action,env):
        
#        iu.dbg('env')
        if hasattr(action,'lineno'):
#            print '        env: {}'.format('{'+','.join('{}:{}'.format(x,y) for x,y in env.iteritems())+'}')
#            inv_env = dict((y,x) for x,y in env.iteritems())
            if not self.started:
                for sym in self.vocab:
                    if sym not in env and not itr.is_new(sym) and not self.is_skolem(sym):
                        self.show_sym(sym,sym)
                self.started = True
            for sym,renamed_sym in env.iteritems():
                if not itr.is_new(sym) and not self.is_skolem(sym):
                    self.show_sym(sym,renamed_sym)

            print '{}{}'.format(action.lineno,action)

    def do_return(self,action,env):
        pass

    def end(self):
        for sym in self.vocab:
            if not itr.is_new(sym) and not self.is_skolem(sym):
                self.show_sym(sym,sym)
            
    def fail(self):
        pass

                
def filter_fcs(fcs):
    global check_lineno
    if check_lineno is None:
        return fcs
    return [fc for fc in fcs if (not isinstance(fc,ConjChecker) or fc.lf.lineno == check_lineno)]

def check_fcs_in_state(mod,ag,post,fcs):
#    iu.dbg('"foo"')
    history = ag.get_history(post)
#    iu.dbg('history.actions')
    gmc = lambda cls, final_cond: itr.small_model_clauses(cls,final_cond,shrink=diagnose.get())
    axioms = im.module.background_theory()
    if opt_trace.get() or diagnose.get():
        clauses = history.post
        clauses = lut.and_clauses(clauses,axioms)
        ffcs = filter_fcs(fcs)
        model = itr.small_model_clauses(clauses,ffcs,shrink=True)
        if model is not None:
#            iu.dbg('history.actions')
            failed = [c for c in ffcs if c.failed]
            mclauses = lut.and_clauses(*([clauses] + [c.cond() for c in failed]))
            vocab = lut.used_symbols_clauses(mclauses)
#            handler = MatchHandler(mclauses,model,vocab) if opt_trace.get() else ivy_trace.Trace(mclauses,model,vocab)
            handler = ivy_trace.Trace(mclauses,model,vocab)
            assert all(x is not None for x in history.actions)
            # work around a bug in ivy_interp
            actions = [im.module.actions[a] if isinstance(a,str) else a for a in history.actions]
            action = act.Sequence(*actions)
            act.match_annotation(action,clauses.annot,handler)
            handler.end()
            ff = failed[0]
            handler.is_cti = (lut.formula_to_clauses(ff.lf.formula) if isinstance(ff,ConjChecker)
                              else None)
            if not opt_trace.get():
                gui_art(handler)
            else:
                print str(handler)
            exit(0)
    else:
        res = history.satisfy(axioms,gmc,filter_fcs(fcs))
        if res is not None and diagnose.get():
            show_counterexample(ag,post,res)
    return not any(fc.failed for fc in fcs)

def check_conjs_in_state(mod,ag,post,indent=8):
    conjs = mod.conj_subgoals if mod.conj_subgoals is not None else mod.labeled_conjs
    check_lineno = act.checked_assert.get()
    if check_lineno == "":
        check_lineno = None
    if check_lineno is not None:
        lcs = [sub for sub in conjs if sub.lineno == check_lineno]
    else:
        lcs = conjs
    return check_fcs_in_state(mod,ag,post,[ConjChecker(c,indent) for c in lcs])

def check_safety_in_state(mod,ag,post,report_pass=True):
    return check_fcs_in_state(mod,ag,post,[Checker(lg.Or(),report_pass=report_pass)])

opt_summary = iu.BooleanParameter("summary",False)

# This gets the pre-state for inductive checks. Only implicit conjectures are used.

def get_conjs(mod):
    fmlas = [lf.formula for lf in mod.labeled_conjs + mod.assumed_invariants if not lf.explicit]
    return lut.Clauses(fmlas,annot=act.EmptyAnnotation())

def apply_conj_proofs(mod):
    # Apply any proof tactics to the conjs to get the conj_subgoals.

    pc = ivy_proof.ProofChecker(mod.labeled_axioms+mod.assumed_invariants,mod.definitions,mod.schemata)
    pmap = dict((lf.id,p) for lf,p in mod.proofs)
    conjs = []
    for lf in mod.labeled_conjs:
        if lf.id in pmap:
            proof = pmap[lf.id]
            subgoals = pc.admit_proposition(lf,proof)
            subgoals = map(ivy_compiler.theorem_to_property,subgoals)
            conjs.extend(subgoals)
        else:
            conjs.append(lf)
    mod.conj_subgoals = conjs


def summarize_isolate(mod):

    global check_lineno
    check_lineno = act.checked_assert.get()
    if check_lineno == "":
        check_lineno = None
#    print 'check_lineno: {}'.format(check_lineno)
    check = not opt_summary.get()
    subgoalmap = dict((x.id,y) for x,y in im.module.subgoals)
    axioms = [m for m in mod.labeled_axioms if m.id not in subgoalmap] 
    schema_instances = [m for m in mod.labeled_axioms if m.id in subgoalmap]
    if axioms:
        print "\n    The following properties are assumed as axioms:"
        for lf in axioms:
            print pretty_lf(lf)

    if mod.definitions:
        print "\n    The following definitions are used:"
        for lf in mod.definitions:
            print pretty_lf(lf)

    if (mod.labeled_props or schema_instances) and not checked_action.get():
        print "\n    The following properties are to be checked:"
        if check:
            for lf in schema_instances:
                print pretty_lf(lf) + " [proved by axiom schema]"
            ag = ivy_art.AnalysisGraph()
            clauses1 = lut.true_clauses(annot=act.EmptyAnnotation())
            pre = itp.State(value = clauses1)
            props = [x for x in im.module.labeled_props if not x.temporal]
            fcs = ([(ConjAssumer if prop.id in subgoalmap else ConjChecker)(prop) for prop in props])
            check_fcs_in_state(mod,ag,pre,fcs)
        else:
            for lf in schema_instances + mod.labeled_props:
                print pretty_lf(lf)

    # after checking properties, make them axioms, except temporals
    im.module.labeled_axioms.extend(p for p in im.module.labeled_props if not p.temporal)
    im.module.update_theory()


    if mod.labeled_inits:
        print "\n    The following properties are assumed initially:"
        for lf in mod.labeled_inits:
            print pretty_lf(lf)
    if mod.labeled_conjs:
        print "\n    The inductive invariant consists of the following conjectures:"
        for lf in mod.labeled_conjs:
            print pretty_lf(lf)

    apply_conj_proofs(mod)
    
    if mod.isolate_info.implementations:
        print "\n    The following action implementations are present:"
        for mixer,mixee,action in sorted(mod.isolate_info.implementations,key=lambda x: x[0]):
            print "        {}implementation of {}".format(pretty_lineno(action),mixee)

    if mod.isolate_info.monitors:
        print "\n    The following action monitors are present:"
        for mixer,mixee,action in sorted(mod.isolate_info.monitors,key=lambda x: x[0]):
            print "        {}monitor of {}".format(pretty_lineno(action),mixee)

    # if mod.actions:
    #     print "\n    The following actions are present:"
    #     for actname,action in sorted(mod.actions.iteritems()):
    #         print "        {}{}".format(pretty_lineno(action),actname)

    if mod.initializers:
        print "\n    The following initializers are present:"
        for actname,action in sorted(mod.initializers, key=lambda x: x[0]):
            print "        {}{}".format(pretty_lineno(action),actname)

    if mod.labeled_conjs and not checked_action.get():
        print "\n    Initialization must establish the invariant"
        if check:
            with itp.EvalContext(check=False):
                ag = ivy_art.AnalysisGraph(initializer=lambda x:None)
                check_conjs_in_state(mod,ag,ag.states[0])
        else:
            print ''

    if mod.initializers:
        print "\n    Any assertions in initializers must be checked",
        if check:
            ag = ivy_art.AnalysisGraph(initializer=lambda x:None)
            fail = itp.State(expr = itp.fail_expr(ag.states[0].expr))
            check_safety_in_state(mod,ag,fail)


    checked_actions = get_checked_actions()

    if checked_actions and mod.labeled_conjs:
        print "\n    The following set of external actions must preserve the invariant:"
        for actname in sorted(checked_actions):
            action = act.env_action(actname)
            print "        {}{}".format(pretty_lineno(action),actname)
            if check:
                ag = ivy_art.AnalysisGraph()
                pre = itp.State()
                pre.clauses = get_conjs(mod)
                with itp.EvalContext(check=False): # don't check safety
#                    post = ag.execute(action, pre, None, actname)
                    post = ag.execute(action, pre)
                check_conjs_in_state(mod,ag,post,indent=12)
            else:
                print ''
            


    callgraph = defaultdict(list)
    for actname,action in mod.actions.iteritems():
        for called_name in action.iter_calls():
            callgraph[called_name].append(actname)

    some_assumps = False
    for actname,action in mod.actions.iteritems():
        assumptions = [sub for sub in action.iter_subactions()
                           if isinstance(sub,act.AssumeAction)]
        if assumptions:
            if not some_assumps:
                print "\n    The following program assertions are treated as assumptions:"
                some_assumps = True
            callers = callgraph[actname]
            if actname in mod.public_actions:
                callers.append("the environment")
            prettyname = actname[4:] if actname.startswith('ext:') else actname
            prettycallers = [c[4:] if c.startswith('ext:') else c for c in callers]
            print "        in action {} when called from {}:".format(prettyname,','.join(prettycallers))
            for sub in assumptions:
                print "            {}assumption".format(pretty_lineno(sub))

    tried = set()
    some_guarants = False
    for actname,action in mod.actions.iteritems():
        guarantees = [sub for sub in action.iter_subactions()
                          if isinstance(sub,(act.AssertAction,act.Ranking))]
        if check_lineno is not None:
            guarantees = [sub for sub in guarantees if sub.lineno == check_lineno]
        if guarantees:
            if not some_guarants:
                print "\n    The following program assertions are treated as guarantees:"
                some_guarants = True
            callers = callgraph[actname]
            if actname in mod.public_actions:
                callers.append("the environment")
            prettyname = actname[4:] if actname.startswith('ext:') else actname
            prettycallers = [c[4:] if c.startswith('ext:') else c for c in callers]
            print "        in action {} when called from {}:".format(prettyname,','.join(prettycallers))
            roots = set(iu.reachable([actname],lambda x: callgraph[x]))
            for sub in guarantees:
                print "            {}guarantee".format(pretty_lineno(sub)),
                if check and any(r in roots and (r,sub.lineno) not in tried for r in checked_actions):
                    print_dots()
                    old_checked_assert = act.checked_assert.get()
                    act.checked_assert.value = sub.lineno
                    some_failed = False
                    for root in checked_actions:
                        if root in roots:
                           tried.add((root,sub.lineno))
                           action = act.env_action(root)
                           ag = ivy_art.AnalysisGraph()
                           pre = itp.State()
                           pre.clauses = get_conjs(mod)
                           with itp.EvalContext(check=False):
                               post = ag.execute(action,prestate=pre)
                           fail = itp.State(expr = itp.fail_expr(post.expr))
                           if not check_safety_in_state(mod,ag,fail,report_pass=False):
                               some_failed = True
                               break
                    if not some_failed:
                        print 'PASS'
                    act.checked_assert.value = old_checked_assert
                else:
                    print ""


def check_isolate():
    temporals = [p for p in im.module.labeled_props if p.temporal]
    mod = im.module
    # if temporals:
    #     if len(temporals) > 1:
    #         raise IvyError(None,'multiple temporal properties in an isolate not supported yet')
    #     from ivy_l2s import l2s
    #     l2s(mod, temporals[0])
    #     mod.concept_spaces = []
    #     mod.update_conjs()
    ifc.check_fragment()
    with im.module.theory_context():
        summarize_isolate(mod)
        check_temporals()
        return
        check_properties()
        some_temporals = any(p.temporal for p in im.module.labeled_props)
        check_temporals()
        ag = ivy_art.AnalysisGraph(initializer=ivy_alpha.alpha)
        if im.module.initializers:
            cex = ag.check_bounded_safety(ag.states[0])
            if cex is not None:
                display_cex("safety failed in initializer",cex)
        with ivy_interp.EvalContext(check=False):
            initiation_checked = False
            if not some_temporals:
                check_conjectures('Initiation','These conjectures are false initially.',ag,ag.states[0])
                initiation_checked = True
            for actname in get_checked_actions():
                old_checked_assert = act.checked_assert.get()
                assertions = find_assertions(actname)
                if assertions and not initiation_checked:
                    check_conjectures('Initiation','These conjectures are false initially.',ag,ag.states[0])
                    initiation_checked = True
                print "trying {}...".format(actname)
                if act.checked_assert.get():
                    assertions = [a for a in assertions if a.lineno == act.checked_assert.get()]
                tried = set()
                for asn in assertions:
                    if asn.lineno not in tried:
                        tried.add(asn.lineno)
                        act.checked_assert.value = asn.lineno
                        print '{}: {}'.format(asn.lineno,asn)
                        ag.execute_action(actname,prestate=ag.states[0])
                        cex = ag.check_bounded_safety(ag.states[-1],bound=1)
                        if cex is not None:
                            display_cex("safety failed",cex)
                if initiation_checked:
                    print "checking consecution..."
                    ag.execute_action(actname,prestate=ag.states[0],abstractor=ivy_alpha.alpha)
                    check_conjectures('Consecution','These conjectures are not inductive.',ag,ag.states[-1])
                act.checked_assert.value = old_checked_assert


# This is a little bit backward. When faced with a subgoal from the prover,
# we check it by constructing fake isolate.
                
def check_subgoals(goals):
    mod = im.module
    for goal in goals:
        # print 'goal: {}'.format(goal)
        conc = ivy_proof.goal_conc(goal)
        if isinstance(conc,itmp.TemporalModels):
            model = conc.model
            fmla = conc.fmla
            if not lg.is_true(fmla):
                raise IvyError(goal,
                  """The temporal subgoal {} has not been reduced to an invariance property. 
                     Try using a tactic such as l2s.""")
            mod = im.module.copy()
            # mod.labeled_axioms.extend(proved)
            mod.labeled_props = []
            mod.concept_spaces = []
            mod.labeled_conjs = model.invars
            mod.public_actions = set(model.calls)
            mod.actions = model.binding_map
            mod.initializers = [('init',model.init)]
            mod.labeled_axioms = list(mod.labeled_axioms)
            mod.assumed_invars = model.asms
            for prem in ivy_proof.goal_prems(goal):
                if prem.temporal:
                    mod.labeled_axioms.append(prem)
            # ivy_printer.print_module(mod)
        else:
            goal = ivy_compiler.theorem_to_property(goal)
            mod = im.module.copy()
            # mod.labeled_axioms.extend(proved)
            mod.labeled_props = [goal]
            mod.concept_spaces = []
            mod.conjs = []
            mod.public_actions = set()
            mod.actions = dict()
            mod.initializers = []
        with mod:
            check_isolate()
                

def all_assert_linenos():
    mod = im.module
    all = []
    for actname,action in mod.actions.iteritems():
        guarantees = [sub.lineno for sub in action.iter_subactions()
                      if isinstance(sub,(act.AssertAction,act.Ranking))]
        all.extend(guarantees)
    all.extend(lf.lineno for lf in mod.labeled_conjs)
    seen = set()
    res = []
    for lineno in all:
        if not lineno in seen:
            res.append(lineno)
            seen.add(lineno)
    check_lineno = act.checked_assert.get()
    if check_lineno:
        if check_lineno in seen:
            return [check_lineno]
        raise iu.IvyError(None,'There is no assertion at the specified line')
    return res

def get_isolate_attr(isolate,attr,default=None):
    if isolate is None:
        return default
    attr = iu.compose_names(isolate,attr)
    if attr not in im.module.attributes:
        return default
    return im.module.attributes[attr].rep

def check_separately(isolate):
    if opt_separate.get() is not None:
        return opt_separate.get()
    return get_isolate_attr(isolate,'separate','false') == 'true'

def mc_isolate(isolate,meth=ivy_mc.check_isolate):
    if im.module.labeled_props:
        raise IvyError(im.module.labeled_props[0],'model checking not supported for property yet')
    if not check_separately(isolate):
        with im.module.theory_context():
            meth()
        return
    for lineno in all_assert_linenos():
        with im.module.copy():
            old_checked_assert = act.checked_assert.get()
            act.checked_assert.value = lineno
            with im.module.theory_context():
                meth()
            act.checked_assert.value = old_checked_assert
    
def get_isolate_method(isolate):
    if opt_mc.get():
        return 'mc'
    return get_isolate_attr(isolate,'method','ic')


def check_module():
    # If user specifies an isolate, check it. Else, if any isolates
    # are specificied in the file, check all, else check globally.

    missing = []

    isolate = ivy_compiler.isolate.get()
    if isolate != None:
        isolates = [isolate]
    else:
        isolates = sorted(list(im.module.isolates))
        if len(isolates) == 0:
            isolates = [None]
        else:
            if coverage.get():
                missing = ivy_isolate.check_isolate_completeness()
            
    if missing:
        raise iu.IvyError(None,"Some assertions are not checked")

    for isolate in isolates:
        if isolate is not None and isolate in im.module.isolates:
            idef = im.module.isolates[isolate]
            if len(idef.verified()) == 0 or isinstance(idef,ivy_ast.TrustedIsolateDef):
                continue # skip if nothing to verify
        if isolate:
            print "\nIsolate {}:".format(isolate)
        if isolate is not None and iu.compose_names(isolate,'macro_finder') in im.module.attributes:
            save_macro_finder = islv.opt_macro_finder.get()
            if save_macro_finder:
                print "Turning off macro_finder"
                islv.set_macro_finder(False)
        with im.module.copy():
            ivy_isolate.create_isolate(isolate) # ,ext='ext'
            if opt_trusted.get():
                continue
            method_name = get_isolate_method(isolate)
            if method_name == 'mc':
                mc_isolate(isolate)
            elif method_name.startswith('bmc['):
                global some_bounded
                some_bounded = True
                _,prms = iu.parse_int_subscripts(method_name)
                if len(prms) != 1:
                    raise IvyError(None,'BMC method specifier should be bmc[<steps>]. Got "{}".'.format(method_name))
                mc_isolate(isolate,lambda : ivy_bmc.check_isolate(prms[0]))
            else:
                check_isolate()
        if isolate is not None and iu.compose_names(isolate,'macro_finder') in im.module.attributes:
            if save_macro_finder:
                print "Turning on macro_finder"
                islv.set_macro_finder(True)
    print ''
    if failures > 0:
        raise iu.IvyError(None,"failed checks: {}".format(failures))
    if checked_action.get() and not checked_action_found:
        raise iu.IvyError(None,"{} is not an exported action of any isolate".format(checked_action.get()))

    cact = checked_action.get()


def main():
    import signal
    signal.signal(signal.SIGINT,signal.SIG_DFL)
    import ivy_alpha
    ivy_alpha.test_bottom = False # this prevents a useless SAT check
    ivy_init.read_params()
    if len(sys.argv) != 2 or not sys.argv[1].endswith('ivy'):
        usage()
    global some_bounded
    some_bounded = False

    with im.Module():
        with utl.ErrorPrinter():
            ivy_init.source_file(sys.argv[1],ivy_init.open_read(sys.argv[1]),create_isolate=False)
            check_module()
    if some_bounded:
        print "BOUNDED"
    else:
        print "OK"


if __name__ == "__main__":
    main()


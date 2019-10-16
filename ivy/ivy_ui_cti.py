import ivy_ui
import ivy_logic as il
import logic as lg
from ivy_interp import State,EvalContext,reverse,decompose_action_app, universe_constraint
import ivy_module as im
import ivy_logic_utils as ilu
import logic_util as lu
import ivy_utils as iu
import ivy_graph_ui
import ivy_actions as ia
import ivy_trace

from concept import (get_initial_concept_domain,
                     get_diagram_concept_domain,
                     get_structure_concept_domain,
                     get_structure_concept_abstract_value,
                     get_structure_renaming,
                     get_standard_combinations)
from collections import defaultdict

class IvyUI(object):
    def AGUI(self):
        return AnalysisGraphUI

class Thing(object):
    def __init__(self,value):
        self.value = value

compile_kwargs = {'ext':'ext'}

class AnalysisGraphUI(ivy_ui.AnalysisGraphUI):

    # This defines the menus items we provide. The actual menus might be
    # tool buttons or other such things.

    def menus(self):
        return [("menu","File",
                 [
                  ("button","Remove tab",lambda self=self: self.ui_parent.remove(self)),
                  ("button","Save invariant",self.save_conjectures),
                  ("button","Exit", lambda self=self: self.ui_parent.exit()),]),
                ("menu","Invariant",
                 [("button","Check induction",self.check_inductiveness),
                  ("button","Bounded check",self.bmc_conjecture),
                  ("button","Diagram",self.diagram),
                  ("button","Weaken",self.weaken),
                  ])]

    def start(self):
        ivy_ui.AnalysisGraphUI.start(self)
#        self.node(0).clauses = ilu.false_clauses() # just to make CG empty initially
        self.transitive_relations = []
        self.transitive_relation_concepts = []
        self.relations_to_minimize = Thing('relations to minimize')
        self.conjectures = im.module.conjs
        self.view_state(self.node(0))
        with self.ui_parent.run_context():
            self.autodetect_transitive()
        self.have_cti = hasattr(self.g,'is_cti')
        if self.have_cti:
            self.current_conjecture = self.g.is_cti


    def CGUI(self):
        return ConceptGraphUI

    def new_ag(self):
        from ivy_art import AnalysisGraph
        ag = AnalysisGraph()
        return ag

    def autodetect_transitive(self):
        import logic as lg
        from ivy_logic_utils import Clauses
        from ivy_solver import clauses_imply
        from concept import Concept

#        self.edge_display_checkboxes['=']['transitive'].value = True
#        self.edge_display_checkboxes['=']['all_to_all'].value = True

        self.transitive_relations = []
        self.transitive_relation_concepts = []

                    
        axioms = im.module.background_theory()
        for c in il.all_symbols():
            if (type(c.sort) is lg.FunctionSort and
                c.sort.arity == 2 and
                c.sort.domain[0] == c.sort.domain[1] and
                c.sort.range == lg.Boolean):
                X = lg.Var('X', c.sort.domain[0])
                Y = lg.Var('Y', c.sort.domain[0])
                Z = lg.Var('Z', c.sort.domain[0])
                transitive = lg.ForAll([X, Y, Z], lg.Or(lg.Not(c(X,Y)), lg.Not(c(Y,Z)), c(X,Z)))
                defined_symmetry = lg.ForAll([X, Y], lg.Or(c(X,X), lg.Not(c(Y,Y))))
                t = Clauses([transitive, defined_symmetry])
                if clauses_imply(axioms, t):
                    self.transitive_relations.append(c.name)
                    concept = self.current_concept_graph.g.formula_to_concept(c(X,Y))
                    self.transitive_relation_concepts.append(concept)
                    self.current_concept_graph.show_relation(concept,'T')
        if self.transitive_relations:
            self.current_concept_graph.update()


    def check_inductiveness(self, button=None):
        import ivy_transrel
        from ivy_solver import get_small_model
        from proof import ProofGoal
        from ivy_logic_utils import Clauses, and_clauses, dual_clauses
        from random import randrange
        from ivy_art import AnalysisGraph
        
        with self.ui_parent.run_context():

            ag,succeed,fail = ivy_trace.make_check_art(precond=self.conjectures)

            to_test =  [None] + list(self.conjectures)  # None = check safety

            while len(to_test) > 0:
                # choose randomly, so the user can get another result by
                # clicking again
#                conj = to_test.pop(randrange(len(to_test)))
                conj = to_test.pop(0)
                assert conj == None or conj.is_universal_first_order()
                used_names = frozenset(x.name for x in il.sig.symbols.values())
                def witness(v):
                    c = lg.Const('@' + v.name, v.sort)
                    assert c.name not in used_names
                    return c

                # TODO: this is still a bit hacky, and without nice error reporting
                if self.relations_to_minimize.value == 'relations to minimize':
                    self.relations_to_minimize.value = ' '.join(sorted(
                        k for k, v in il.sig.symbols.iteritems()
                        if (type(v.sort) is lg.FunctionSort and
                            v.sort.range == lg.Boolean and
                            v.name not in self.transitive_relations 
#                            and '.' not in v.name
                        )
                    ))

                if conj == None: # check safety
                    clauses = ilu.true_clauses()
                    post = fail
                else:
                    clauses = dual_clauses(conj, witness)
                    post = succeed
                history = ag.get_history(post)
                rels_to_min = []
                for x in self.relations_to_minimize.value.split():
                    relation = il.sig.symbols[x]
                    relation = history.maps[0].get(relation, relation)
                    rels_to_min.append(relation)
                        
                clauses.annot = ia.EmptyAnnotation()
                res = ivy_trace.check_final_cond(ag,post,clauses,rels_to_min,True)
#                    res = ag.bmc(post, clauses, None, None, _get_model_clauses)

                if res is not None:
                    self.current_conjecture = conj
                    assert len(res.states) == 2
                    self.g = res
                    self.rebuild()
                    self.view_state(self.g.states[0], reset=True)
                    self.show_used_relations(clauses)
                    #self.post_graph.selected = self.get_relevant_elements(self.post_state[2], clauses)
                    if conj == None:
                        self.ui_parent.ok_dialog('An assertion failed. A failing state is displayed. You can step into\nthe failing action to observe the failing execution. ')
                    else:
                        self.ui_parent.text_dialog('The following conjecture is not relatively inductive:',
                                                   str(il.drop_universals(conj.to_formula())),on_cancel=None)
                    self.have_cti = True
                    return False

    #        self.set_states(False, False)
            self.ui_parent.text_dialog('Inductive invariant found:',
                                       '\n'.join(str(conj) for conj in self.conjectures))
            self.have_cti = False
            return True

    def show_used_relations(self,clauses,both=False):
        self.current_concept_graph.clear_edges()
        rels = self.current_concept_graph.g.relations
        used = set(il.normalize_symbol(s) for s in lu.used_constants(clauses.to_formula()))
        for rel in rels:
            fmla = rel.formula
            if any(c in used and not c.name.startswith('@')
                   for c in lu.used_constants(fmla)):
                self.current_concept_graph.show_relation(rel,'+',update=False)
                if both and not il.is_enumerated(fmla):
                    self.current_concept_graph.show_relation(rel,'-',update=False)
        need_update_relations = False
        for app in ilu.apps_clauses(clauses):
            if len(app.args) == 3 and il.is_numeral(app.args[0]):
                fmla = app.rep(app.args[0],il.Variable('X',app.args[1].sort),il.Variable('Y',app.args[2].sort))
                concept = self.current_concept_graph.g.formula_to_concept(fmla)
                self.current_concept_graph.g.new_relation(concept)
                need_update_relations = True
                self.current_concept_graph.show_relation(concept,'+',update=False)
                if both:
                    self.current_concept_graph.show_relation(concept,'-',update=False)
        if need_update_relations:
            self.current_concept_graph.update_relations()
        self.current_concept_graph.update()

    def diagram(self):
        from ivy_solver import clauses_model_to_diagram, get_model_clauses
        from ivy_transrel import is_skolem, reverse_image
        if not self.have_cti:
            if self.check_inductiveness() or len(self.g.states) != 2:
                return
        conj = self.current_conjecture
        post = ilu.dual_clauses(conj) if conj != None else ilu.true_clauses()
        pre = self.g.states[0].clauses
        axioms = im.module.background_theory()
        uc = universe_constraint(self.g.states[0])
        axioms_uc = ilu.and_clauses(axioms,uc)
#        rev = ilu.and_clauses(reverse_image(post,axioms,self.g.states[1].update), axioms)
        rev = reverse_image(post,axioms,self.g.states[1].update)
        clauses = ilu.and_clauses(ilu.and_clauses(pre,rev),axioms_uc)
        mod = get_model_clauses(clauses)
        assert mod != None
        diag = clauses_model_to_diagram(rev,is_skolem,model=mod,axioms=axioms)
        self.view_state(self.g.states[0], clauses=diag, reset=True)
        self.show_used_relations(diag,both=True)
        self.current_concept_graph.gather_facts()

    def set_states(self,s0,s1):
        self.cg = self.view_state(s0, reset=True)
        
    def show_result(self,res):
        print res

    def weaken(self, conjs = None, button=None):
        if conjs == None:
            udc = self.conjectures
            udc_text = [str(il.drop_universals(conj.to_formula())) for conj in udc]
            msg = "Select conjecture to remove:"
            cmd = lambda sel: self.weaken([udc[idx] for idx in sel])
            self.ui_parent.listbox_dialog(msg,udc_text,command=cmd,multiple=True)
        else:
            for conj in conjs:
                self.have_cti = False
                self.conjectures.remove(conj)
            self.ui_parent.text_dialog('Removed the following conjectures:',
                                       '\n'.join(str(conj) for conj in conjs))

    def save_conjectures(self):
        f = self.ui_parent.saveas_dialog('Save invariant as...',[('ivy files', '.ivy')])
        if f:

            old_conjs_set = set(str(c) for c in im.module.conjs)
            new_conjs_set = set(str(c) for c in self.conjectures)

            old_kept = [lc for lc in im.module.labeled_conjs if str(lc.formula) in new_conjs_set]
            old_dropped = [lc for lc in im.module.labeled_conjs if str(lc.formula) not in new_conjs_set]
            new = [conj for conj in self.conjectures if str(conj) not in old_conjs_set]

            f.write('# This file was generated by ivy.\n\n')

            if old_kept:
                f.write('\n# original conjectures kept\n\n')
                for lc in old_kept:
                    _write_conj(f,lc.label,lc.formula)

            if old_dropped:
                f.write('\n# original conjectures dropped\n\n')
                for lc in old_dropped:
                    f.write('# ')
                    _write_conj(f,lc.label,lc.formula)
                    
            if new:
                f.write('\n# new conjectures\n\n')
                for conj in new:
                    _write_conj(f,None,conj)

            f.close()

    def bmc_conjecture(self, button=None, bound = None, conjecture=None, verbose=False, tell_unsat=True):
        import ivy_transrel
        import ivy_solver
        from proof import ProofGoal
        from ivy_logic_utils import Clauses, and_clauses, dual_clauses

        # get the bound, if not specified

        if bound is None:
            iv = self.current_bound if hasattr(self,'current_bound') else None
            c = lambda b: self.bmc_conjecture(button=button, bound=b, conjecture=conjecture,
                                              verbose=verbose, tell_unsat=tell_unsat)
            self.ui_parent.int_dialog('Number of steps to check:',
                                        command = c, minval=0, initval=iv)
            return


        with self.ui_parent.run_context():

            step_action = ia.env_action(None)

            n_steps = bound
            self.current_bound = bound

            conj = conjecture
            if conj is None:
                conj = and_clauses(*self.conjectures)
            
            assert conj.is_universal_first_order()
            used_names = frozenset(x.name for x in il.sig.symbols.values())
            def witness(v):
                c = lg.Const('@' + v.name, v.sort)
                assert c.name not in used_names
                return c
            clauses = dual_clauses(conj, witness)

            ag = self.new_ag()
            with ag.context as ac:
#                post = ac.new_state(ag.init_cond)
                ag.add_initial_state(ag.init_cond)
                post = ag.states[0]
            if 'initialize' in im.module.actions:
                print "got here"
                init_action = im.module.actions['initialize']
                post = ag.execute(init_action, None, None, 'initialize')

            for n in range(n_steps + 1):
                res = ivy_trace.check_final_cond(ag,post,clauses,[],True)
#                res = ag.bmc(post, clauses)
                if verbose:
                    if res is None:
                        msg = 'BMC with bound {} did not find a counter-example to:\n{}'.format(
                            n,
                            str(conj.to_formula()),
                        )
                    else:
                        msg = 'BMC with bound {} found a counter-example to:\n{}'.format(
                            n,
                            str(conj.to_formula()),
                        )
                    print '\n' + msg + '\n'
                if res is not None:
    #                ta.step()
                    cmd = lambda: self.ui_parent.add(res,ui_class=ivy_ui.AnalysisGraphUI)
                    self.ui_parent.text_dialog('BMC with bound {} found a counter-example to:'.format(n),
                                               str(conj.to_formula()),
                                               command = cmd,
                                               command_label = 'View')
                    return True
                post = ag.execute(step_action)

            if tell_unsat:
                self.ui_parent.text_dialog('BMC with bound {} did not find a counter-example to:'.format(n_steps),
                                       str(conj.to_formula()),
                                       on_cancel = None)

            return False


def _write_conj(f,lab,fmla):
    fmla = il.drop_universals(fmla)
    if lab:
        f.write("invariant [{}] {}\n".format(lab,str(fmla)))
    else:
        f.write("invariant {}\n".format(str(fmla)))

class ConceptGraphUI(ivy_graph_ui.GraphWidget):
    def menus(self):
        return [("menu","Conjecture",
                 [("button","Undo",self.undo),
                  ("button","Redo",self.redo),
                  ("button","Gather",self.gather_facts),
                  ("button","Bounded check",self.bmc_conjecture),
                  ("button","Minimize",self.minimize_conjecture),
                  ("button","Check sufficient",self.is_sufficient),
                  ("button","Check relative induction",self.is_inductive),
                  ("button","Strengthen",self.strengthen),
                  ("button","Export",self.export),
                  ]),
                ("menu","View",
                 [("button","Add relation",self.add_concept_from_string),
                  ])]


    def get_node_actions(self,node,click='left'):
        if click == 'left':
            return [("<>",self.select_node)]
        else:
            return [
                ("Projections...",None),
                ("---",None),
                ] + self.get_node_projection_actions(node)

    def get_edge_actions(self,node,click='left'):
        if click == 'left':
            return [("<>",self.select_edge)]
        else:
            return [] # nothing on right click

    def get_selected_conjecture(self):
        """
        Return a positive universal conjecture based on the selected facts.

        The result is a Clauses object
        """
        from logic_util import used_constants, free_variables, substitute
        from ivy_logic_utils import negate, Clauses, simplify_clauses

        facts = self.get_active_facts()
        assert len(free_variables(*facts)) == 0, "conjecture would contain existential quantifiers..."
        sig_symbols = frozenset(il.sig.symbols.values())
        facts_consts = used_constants(*facts)
        subs = {}
        rn = iu.VariableGenerator()
        for c in sorted(facts_consts, key=lambda c: c.name):
            if c.is_numeral() and il.is_uninterpreted_sort(c.sort):
#                prefix = str(c.sort)[:2].upper() + c.name
                subs[c] = lg.Var(rn(c.sort.name), c.sort)

        literals = [negate(substitute(f, subs)) for f in facts]
        result = Clauses([lg.Or(*literals)])
        result = simplify_clauses(result)

        # now rename again to get a pretty clause, since some
        # variables have been eliminated by simplify_clauses
        # assert len(result.fmlas) == 1
        # clause = result.fmlas[0]
        # subs = {}
        # count = defaultdict(int)
        # for c in free_variables(clause):
        #     prefix = str(c.sort)[0].upper()
        #     count[prefix] += 1
        #     subs[c] = lg.Var(prefix + str(count[prefix]), c.sort)
        # result = Clauses([substitute(clause, subs)])

        # change to negation of conjunction rather than disjunction
        assert len(result.fmlas) == 1
        if type(result.fmlas[0]) is lg.Or:
            result = Clauses([lg.Not(lg.And(*(negate(lit) for lit in result.fmlas[0])))])

        return result


    def add_conjecture(self,conj):
        self.parent.have_cti = False
        self.parent.conjectures.append(conj)

    def strengthen(self, button=None):
        conj = self.get_selected_conjecture()
        f = il.drop_universals(conj.to_formula())
        self.ui_parent.text_dialog('Add the following conjecture:',str(f),
                                   command = lambda : self.add_conjecture(conj))



    def conjecture(self):
        print self.get_selected_conjecture()


    def bmc_conjecture(self, button=None, bound = None, conjecture=None, verbose=False, add_to_crg=True, tell_unsat=True):
        if conjecture is None:
            conj = self.get_selected_conjecture()
        else:
            conj = conjecture

        self.parent.bmc_conjecture(button=button, bound = bound, conjecture=conj, verbose=verbose, tell_unsat=tell_unsat)


    def minimize_conjecture(self, button=None, bound=None):
        import ivy_transrel
        import ivy_solver
        from proof import ProofGoal
        from ivy_logic_utils import Clauses, and_clauses, dual_clauses, used_symbols_clauses, negate
        from ivy_solver import unsat_core
        from logic_util import free_variables, substitute

        if self.bmc_conjecture(bound=bound,tell_unsat=False):
            # found a BMC counter-example
            return

        with self.ui_parent.run_context():
            step_action = ia.env_action(None)

            n_steps = self.parent.current_bound

            ag = self.parent.new_ag()
            with ag.context as ac:
                ag.add_initial_state(ag.init_cond)
                post = ag.states[0]
            for n in range(n_steps):
                post = ag.execute(step_action)
            axioms = im.module.background_theory()
            post_clauses = and_clauses(post.clauses, axioms)

            used_names = (
                frozenset(x.name for x in il.sig.symbols.values()) |
                frozenset(x.name for x in used_symbols_clauses(post_clauses))
            )
            facts = self.get_active_facts()
            assert not any(
                c.is_skolem() and c.name in used_names for c in lu.used_constants(*facts)
            )
            core = unsat_core(Clauses(facts), post_clauses)
            if core is None:
                core = Clauses([]) ## can happen if we are proving true
#            assert core is not None, "bmc_conjecture returned False but unsat core is None"
            core_formulas = frozenset(core.fmlas)
            self.set_facts([fact for fact in facts if fact in core_formulas])
            self.highlight_selected_facts()
            self.ui_parent.text_dialog("BMC found the following possible conjecture:",
                                       str(self.get_selected_conjecture()))


#    def highlight_selected_facts(self):
#            pass # TODO

    def is_sufficient(self, button=None):
        """
        Check if the active conjecture is sufficient to imply the current
        CTI conjecture at the next step

        TODO: this has a lot in common with check_inductiveness,
        should refactor common parts out
        """
        import ivy_transrel
        import ivy_solver
        from proof import ProofGoal
        from ivy_logic_utils import Clauses, and_clauses, dual_clauses
        from random import randrange

        with self.ui_parent.run_context():

            conj = self.get_selected_conjecture()
            target_conj = self.parent.current_conjecture

            ag = self.parent.new_ag()

            pre = State()
            pre.clauses = and_clauses(conj, *self.parent.conjectures)
            pre.clauses.annot = ia.EmptyAnnotation()

            action = ia.env_action(None)
            post = ag.execute(action, pre)
            post.clauses = ilu.true_clauses(annot=ia.EmptyAnnotation())

            assert target_conj.is_universal_first_order()
            used_names = frozenset(x.name for x in il.sig.symbols.values())
            def witness(v):
                c = lg.Const('@' + v.name, v.sort)
                assert c.name not in used_names
                return c
            clauses = dual_clauses(target_conj, witness)
            clauses.annot = ia.EmptyAnnotation()
            res = ivy_trace.check_final_cond(ag,post,clauses,[],True)

            text = '(1) ' + str(conj.to_formula()) + '\n(2) ' + str(target_conj.to_formula())
            if res is not None:
                self.ui_parent.text_dialog('(1) does not imply (2) at the next time. View counterexample?',
                                           text,command_label='View',command = lambda: self.ui_parent.add(res))
                return False
            else:
                self.ui_parent.text_dialog('(1) implies (2) at the next time:',text,on_cancel=None)
                return True


    def is_inductive(self, button=None):
        """
        Check if the active conjecture implies itself at the next step

        TODO: this has a lot in common with check_inductiveness and is_sufficient,
        should refactor common parts out
        """
        import ivy_transrel
        import ivy_solver
        from proof import ProofGoal
        from ivy_logic_utils import Clauses, and_clauses, dual_clauses
        from random import randrange

        with self.ui_parent.run_context():
            conj = self.get_selected_conjecture()
            target_conj = conj

            ag = self.parent.new_ag()

            pre = State()
            pre.clauses = and_clauses(conj, *self.parent.conjectures)
            pre.clauses.annot = ia.EmptyAnnotation()

            action = ia.env_action(None)
            post = ag.execute(action, pre)
            post.clauses = ilu.true_clauses(annot=ia.EmptyAnnotation())

            assert target_conj.is_universal_first_order()
            used_names = frozenset(x.name for x in il.sig.symbols.values())
            def witness(v):
                c = lg.Const('@' + v.name, v.sort)
                assert c.name not in used_names
                return c
            clauses = dual_clauses(target_conj, witness)
            clauses.annot = ia.EmptyAnnotation()
            res = ivy_trace.check_final_cond(ag,post,clauses,[],True)

            text = '(1) ' + str(conj.to_formula()) 
            if res is not None:
                self.ui_parent.text_dialog('(1) is not relatively inductive. View counterexample?',
                                           text,command_label='View',command = lambda: self.ui_parent.add(res))
                return False
            else:
                self.ui_parent.text_dialog('(1) is relatively inductive:',text,on_cancel=None)
                return True

    # TODO: this is not used yet

    def unused_highlight_selected_facts(self):
        """
        Add custom node labels and edges to reflect the selected
        conjecture in pre_graph
        """
        # first collect all atoms that appear in the facts
        atoms = []
        def collect_atoms(x):
            if type(x) in (lg.Apply, lg.Eq):
                atoms.append(x)
            else:
                for y in x:
                    collect_atoms(y)
        collect_atoms(self.get_active_facts())

        # now collect relevant edges and node labels elements
        self.g.concept_session.widget = None
        self.g.concept_session.domain.concepts['edges'] = []
        self.g.concept_session.domain.concepts['node_labels'] = []
        nodes = frozenset(self.g.concept_session.domain.concepts['nodes'])
        for atom in atoms:
            if type(atom) is lg.Eq:
                assert type(atom.t2) is lg.Const
                if type(atom.t1) is lg.Const:
                    n1 = atom.t1.name
                    n2 = atom.t2.name
                    if n1 in nodes and n2 in nodes:
                        self.g.concept_session.add_custom_edge('=', n1, n2)
                    elif n1 in nodes:
                        label_name = '={}'.format(n2)
                        assert label_name in self.g.concept_session.domain.concepts, atom
                        self.g.concept_session.add_custom_node_label(n1, label_name)
                    else:
                        # TODO
                        # assert False, atom
                        pass
                else:
                    assert type(atom.t1) is lg.Apply
                    if atom.t1.func.sort.arity == 1:
                        assert type(atom.t1.terms[0]) is lg.Const
                        self.g.concept_session.add_custom_edge(
                            atom.t1.func.name,
                            atom.t1.terms[0].name,
                            atom.t2.name,
                        )
                    else:
                        # TODO: support higher arity
                        pass
            elif type(atom) is lg.Apply:
                if atom.func.sort.arity == 1:
                    self.g.concept_session.add_custom_node_label(atom.terms[0].name, atom.func.name)
                elif atom.func.sort.arity == 2:
                    self.g.concept_session.add_custom_edge(*(c.name for c in atom))
                else:
                    # TODO: support higher arity
                    pass
            else:
                assert False, lit
        self.g.recompute()
#        self.g.pre_graph.selected = tuple(set(chain(*(elements for fact, elements in self.g.facts_list.value))))


    def gather_facts(self, button=None):
        """
        Gather only based on selected nodes, taking all visible edges.
        """
        g = self.g
        facts = [] # list of pairs (formula, graph_elements)
        selected_nodes = sorted(self.node_selection)
        # if nothing is selected, use all nodes
        if not selected_nodes:
            selected_nodes = [n.name for n in g.nodes]
        for node in selected_nodes:
            elements = ((node,),)
            facts += [(formula, elements) for formula in g.concept_session.get_node_facts(node)]
        selected_nodes = frozenset(selected_nodes)
        edges = set(
            tag[-3:]
            for tag, value in g.concept_session.abstract_value
            if tag[0] == 'edge_info' and
            tag[-2] in selected_nodes and
            tag[-1] in selected_nodes
        )
        for edge, source, target in sorted(edges):
            elements = ((source,), (target,), (edge,source,target))
            if (g.edge_display_checkboxes[edge]['all_to_all'].value):
                if g.edge_display_checkboxes[edge]['transitive'].value and source==target:
                    continue # don't use reflective edges for orders
                facts += [(formula, elements) for formula in
                          g.concept_session.get_edge_facts(edge, source, target, True)]
            if g.edge_display_checkboxes[edge]['none_to_none'].value or edge == '=':
                # get dis-equalities, don't get other negative
                # transitive facts unless checkboxed
                facts += [(formula, elements) for formula in
                          g.concept_session.get_edge_facts(edge, source, target, False)]
        # filter double equalities and self-edges of reflexive relations
        facts = [(f, elements) for f, elements in facts if not (
            #(type(f) is Eq and f.t1 >= f.t2) or
            (type(f) is lg.Not and type(f.body) is lg.Eq and f.body.t1 >= f.body.t2) #or
            # (
            #     type(f) is Apply and
            #     g.edge_display_checkboxes[f.func.name]['transitive'].value and
            #     f.terms[0] == f.terms[1]
            # )
        )]
        g.set_facts([x for x,y in facts])
        self.fact_elems = dict(facts)
        self.update()
        self.highlight_selected_facts()


import ivy_ui
import ivy_logic as il
import logic as lg
from ivy_interp import State
import ivy_module as im
import ivy_logic_utils as ilu
import logic_util as lu
import ivy_utils as iu
import ivy_graph_ui
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
                  ("button","Exit", lambda self=self: self.ui_parent.exit()),]),
                ("menu","Action",
                 [("button","Check induction",self.check_inductiveness),
                  ("button","Weaken",self.weaken),
                  ])]

    def start(self):
        ivy_ui.AnalysisGraphUI.start(self)
        self.transitive_relations = []
        self.relations_to_minimize = Thing('')
        self.conjectures = im.module.conjs
        self.view_state(self.node(0))


    def CGUI(self):
        return ConceptGraphUI

    def new_ag(self):
        from ivy_art import AnalysisGraph
        ag = AnalysisGraph()
        return ag

    def check_inductiveness(self, button=None):
        import ivy_transrel
        from ivy_solver import get_small_model
        import tactics_api as ta
        from proof import ProofGoal
        from ivy_logic_utils import Clauses, and_clauses, dual_clauses
        from random import randrange

        ag = self.new_ag()

        pre = State()
        pre.clauses = and_clauses(*self.conjectures)

        action = im.module.actions['ext']
        post = ag.execute(action, pre, None, 'ext')
        post.clauses = ilu.true_clauses()

        to_test = list(self.conjectures)
        while len(to_test) > 0:
            # choose randomly, so the user can get another result by
            # clicking again
            conj = to_test.pop(randrange(len(to_test)))
            assert conj.is_universal_first_order()
            used_names = frozenset(x.name for x in il.sig.symbols.values())
            def witness(v):
                c = lg.Const('@' + v.name, v.sort)
                assert c.name not in used_names
                return c
            clauses = dual_clauses(conj, witness)
            history = ag.get_history(post)

            # TODO: this is still a bit hacky, and without nice error reporting
            if self.relations_to_minimize.value == 'relations to minimize':
                self.relations_to_minimize.value = ' '.join(sorted(
                    k for k, v in il.sig.symbols.iteritems()
                    if (type(v.sort) is lg.FunctionSort and
                        v.sort.range == lg.Boolean and
                        v.name not in self.transitive_relations and
                        '.' not in v.name
                    )
                ))

            res = ag.bmc(post, clauses, None, None, lambda clauses: get_small_model(
                clauses,
                sorted(il.sig.sorts.values()),
                [
                    # TODO: this is still a bit hacky, and without nice error reporting
                    history.maps[0].get(relation, relation)
                    for x in self.relations_to_minimize.value.split()
                    for relation in [il.sig.symbols[x]]
                ],
            ))
            if res is not None:
                self.current_conjecture = conj
                assert len(res.states) == 2
                rels = self.current_concept_graph.g.relations
                used = lu.used_constants(clauses.to_formula())
                for rel in rels:
                    if any(c in used for c in lu.used_constants(rel.formula)):
                        self.current_concept_graph.show_relation(rel,'+')
                self.set_states(res.states[0], res.states[1])
                #self.post_graph.selected = self.get_relevant_elements(self.post_state[2], clauses)
                self.show_result('The following conjecture is not inductive:\n{}'.format(
                    str(conj.to_formula()),
                ))
                return False

#        self.set_states(False, False)
        self.ui_parent.text_dialog('Inductive invariant found:',
                                   '\n'.join(str(conj) for conj in self.conjectures))
        return True

    def set_states(self,s0,s1):
        iu.dbg('s0.universe')
        sui = self.view_state(s0, reset=True)

    def show_result(self,res):
        print res

    def weaken(self, conjs = None, button=None):
        if conjs == None:
            udc = self.conjectures
            udc_text = [str(conj.to_formula()) for conj in udc]
            msg = "Select conjecture to remove:"
            cmd = lambda sel: self.weaken([udc[idx] for idx in sel])
            self.ui_parent.listbox_dialog(msg,udc_text,command=cmd,multiple=True)
        else:
            iu.dbg('conjs')
            for conj in conjs:
                self.conjectures.remove(conj)
            self.ui_parent.text_dialog('Removed the following conjectures:',
                                       '\n'.join(str(conj) for conj in conjs))

    pass

class ConceptGraphUI(ivy_graph_ui.GraphWidget):
    def menus(self):
        return [("menu","Action",
                 [("button","Undo",self.undo),
                  ("button","Redo",self.redo),
                  ("button","Gather",self.gather),
                  ("button","Conjecture",self.conjecture),
                  ("button","Strengthen",self.strengthen),
                  ("button","Export",self.export),
                  ]),
                ("menu","View",
                 [("button","Add relation",self.add_concept_from_string),
                  ])]


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
        rn = iu.UniqueRenamer()
        for c in sorted(facts_consts, key=lambda c: c.name):
            if c.is_numeral() and il.is_uninterpreted_sort(c.sort):
                prefix = str(c.sort)[:2].upper() + str(c)
                subs[c] = lg.Var(rn(prefix), c.sort)

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


    def strengthen(self, button=None):
        conj = self.get_selected_conjecture()
        self.ui_parent.text_dialog('Add the following conjecture:',str(conj.to_formula()),
                                   command = lambda : self.parent.conjectures.append(conj))



    def conjecture(self):
        print self.get_selected_conjecture()

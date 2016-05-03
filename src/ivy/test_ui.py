import ivy_ui
import ivy_logic as il
import logic as lg
from ivy_interp import State
import ivy_module as im
import ivy_logic_utils as ilu
import logic_util as lu
import ivy_utils as iu

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
                  ])]

    def start(self):
        ivy_ui.AnalysisGraphUI.start(self)
        self.transitive_relations = []
        self.relations_to_minimize = Thing('')
        self.conjectures = im.module.conjs
        self.view_state(self.node(0))


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

        self.set_states(False, False)
        self.show_result(
            'Inductive invariant found:\n' +
            '\n'.join(
                str(conj) for conj in self.conjectures
            )
        )
        return True

    def set_states(self,s0,s1):
        iu.dbg('s0.universe')
        self.view_state(s0, reset=True)

    def show_result(self,res):
        print res

    pass

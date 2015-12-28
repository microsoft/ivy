#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
An interactive UPDR user interaction
"""

from textwrap import dedent
from collections import OrderedDict

import IPython.html.widgets as widgets

import z3

import tactics_api as ta
import tactics as t
import ivy_transrel
from ivy_logic_utils import negate_clauses, Clauses, and_clauses, simplify_clauses
from ui_extensions_api import interaction, ShowModal, InteractionError, UserSelectMultiple
import ivy_solver
from ivy_solver import clauses_to_z3

class UserSelectCore(ShowModal):
    """
    A front end operation that asks the user to select a subset of
    constrains that are unsatisfiable with a given theory. The user is
    not forces to select an unsatisfiable core.

    The result is:
    (user_selection, False) if the user selected an unsatisfiable core.
    (user_selection, True) if the user selected a satisfiable core.
    (None, None) if the user clicked cancel.
    """

    def __init__(self, theory, constrains, title='', prompt=''):
        self.theory = theory
        self.constrains = list(constrains)
        self.s = z3.Solver()
        self.s.add(clauses_to_z3(self.theory))
        self.alits = [
            z3.Const('__core_aux{}'.format(n), z3.BoolSort())
            for n, c in enumerate(self.constrains)
        ]
        for a, c in zip(self.alits, self.constrains):
            self.s.add(z3.Or(z3.Not(a), ivy_solver.formula_to_z3(c)))
        options = OrderedDict(
            (str(c), n)
            for n, c in enumerate(self.constrains)
        )
        self.select = widgets.SelectMultiple(options=options, value=[])
        self.prompt = widgets.Latex(prompt)
        self.result = widgets.Latex('')
        self.check_button = widgets.Button(description='Check SAT')
        self.check_button.on_click(self.check)

        super(UserSelectCore, self).__init__(title, [
            self.prompt,
            self.select,
            self.check_button,
            self.result,
        ])

    def on_close(self, modal, button):
        if self.on_done is None:
            return

        if button != 'OK':
            result = (None, None)
        else:
            unsat = not self.check()
            result = (
                [self.constrains[i] for i in self.select.value],
                self.check()
            )

        self.on_done(result)

    def check(self, button=None):
        is_sat = self.s.check([self.alits[i] for i in self.select.value])
        if is_sat == z3.sat:
            self.result.value = 'SAT'
            return True
        elif is_sat == z3.unsat:
            self.result.value = 'UNSAT'
            return False
            #core = ivy_solver.minimize_core(s)
            #core_ids = [ivy_solver.get_id(a) for a in core]
            #core = Clauses([[c for a,c in zip(alits,fmlas) if get_id(a) in core_ids]])
            #x = (core, ivy_transrel.interp_from_unsat_core(goal_clauses, theory, core, None))
        else:
            self.result.value = str(is_sat)
            assert False, is_sat
            return None


@interaction
def interactive_updr():
    frames = ta._ivy_ag.states
    if len(frames) != 1:
        raise InteractionError("Interactive UPDR can only be started when the ARG " +
                               "contains nothing but the initial state.")

    bad_states = negate_clauses(ta.get_safety_property())
    action = ta.get_big_action()
    ta._ivy_ag.actions[repr(action)] = action

    init_frame = last_frame = frames[0]

    # TODO: test conjecture in initial

    while True:

        # the property is true in all frames and all "clauses" are pushed
        # the goal stack is empty

        # check if we found an infuctive invariant
        for i in range(len(frames) - 1):
            if t.check_cover(frames[i + 1], frames[i]):
                ta.step(msg="Inductive invariant found at frame {}".format(i), i=i)
                # return True

        # add new frame

        last_frame = ta.arg_add_action_node(last_frame, action, None)
        ta.push_goal(ta.goal_at_arg_node(bad_states, last_frame))
        ta.step(msg="Added new frame")

        # push facts to last frame
        t.recalculate_facts(last_frame, ta.arg_get_conjuncts(ta.arg_get_pred(last_frame)))

        while True:
            current_goal = ta.top_goal()
            if current_goal is None:
                # goal stack is empty
                break

            if t.remove_if_refuted(current_goal):
                continue

            if current_goal.node == init_frame:
                # no invariant
                print "No Invariant!"
                # return False

            dg = ta.get_diagram(current_goal, False)
            options = OrderedDict()
            for c in simplify_clauses(dg.formula).conjuncts():
                options[str(c)] = c
            user_selection = (yield UserSelectMultiple(
                options=options,
                title="Generalize Diagram",
                prompt="Choose which literals to take as the refutation goal",
                default=options.values()
            ))
            assert user_selection is not None
            ug = ta.goal_at_arg_node(Clauses(list(user_selection)), current_goal.node)
            ta.push_goal(ug)
            ta.step(msg='Pushed user selected goal', ug=ug)

            goal = ta.top_goal()
            preds, action = ta.arg_get_preds_action(goal.node)
            assert action != 'join'
            assert len(preds) == 1
            pred = preds[0]
            axioms = ta._ivy_interp.background_theory()
            theory = and_clauses(
                ivy_transrel.forward_image(
                    pred.clauses,
                    axioms,
                    action.update(ta._ivy_interp, None)
                ),
                axioms
            )
            goal_clauses = simplify_clauses(goal.formula)
            assert len(goal_clauses.defs) == 0

            s = z3.Solver()
            s.add(clauses_to_z3(theory))
            s.add(clauses_to_z3(goal_clauses))
            is_sat = s.check()
            if is_sat == z3.sat:
                bi = ta.backward_image(goal.formula, action)
                x, y = False, ta.goal_at_arg_node(bi, pred)
            elif is_sat == z3.unsat:
                user_selection, user_is_sat = yield UserSelectCore(
                    theory=theory,
                    constrains=goal_clauses.fmlas,
                    title="Refinement",
                    prompt="Choose the literals to use",
                )
                assert user_is_sat is False
                core = Clauses(user_selection)
                x, y = True, ivy_transrel.interp_from_unsat_core(goal_clauses, theory, core, None)
            else:
                assert False, is_sat

            t.custom_refine_or_reverse(goal, x, y, False)

        # propagate phase
        for i in range(1, len(frames)):
            facts_to_check = (set(ta.arg_get_conjuncts(frames[i-1])) -
                              set(ta.arg_get_conjuncts(frames[i])))
            t.recalculate_facts(frames[i], list(facts_to_check))

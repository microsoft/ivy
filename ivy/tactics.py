#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
"""

from textwrap import dedent

import tactics_api as ta
from tactics_api import (Tactic, tactic, arg_add_facts, push_goal,
                         arg_get_preds_action, implied_facts,
                         forward_image, arg_get_fact, get_diagram,
                         arg_initial_node, get_safety_property,
                         get_big_action, arg_add_action_node,
                         goal_at_arg_node, top_goal, arg_add_facts,
                         remove_goal, arg_is_covered, arg_get_pred,
                         arg_preorder_traversal, arg_get_conjuncts,
                         goal_tactic)
from ivy_logic_utils import negate_clauses, false_clauses
from logic import Or, And
from logic_util import normalize_quantifiers
import ivy_alpha
from z3_utils import z3_implies
from interrupt_context import InterruptContext


@goal_tactic
@tactic
class RemoveIfRefuted(Tactic):
    def apply(self, goal):
        if ta.refuted_goal(goal):
            ta.remove_goal(goal)
            self.step(goal=goal, active=ta.top_goal())
            return True
        else:
            return False


@goal_tactic
@tactic
class RemoveGoal(Tactic):
    def apply(self, goal):
        ta.remove_goal(goal)
        self.step(goal=goal, active=ta.top_goal())
        return True


@goal_tactic
@tactic
class RefineOrReverse(Tactic):
    def apply(self, goal, auto_remove=True):
        x, y = ta.refine_or_reverse(goal)
        info = dict(goal=goal, x=x, y=y)
        if x:
            ta.arg_add_facts(goal.node, y)
            removed = []
            removed_str = []
            if auto_remove:
                g = goal
                while g is not None and ta.refuted_goal(g):
                    removed.append(g)
                    removed_str.append(str(g))
                    ta.remove_goal(g)
                    g = g.parent
                info['removed'] = removed
                if g is not None:
                    info['active'] = g
                else:
                    info['active'] = goal.node
            info['msg'] = dedent("""
            Learned new fact at arg node {}:
            {}
            Removed goals: {}
            """).strip().format(
                goal.node.id,
                y,
                ', '.join(removed_str),
            )
        else:
            ta.push_goal(y)
            info['active'] = y
            info['msg'] = dedent("""
            No refinement for goal {}, pushed new goal {}
            """).strip().format(goal, y)
        self.step(**info)
        return x


@tactic
class CustomRefineOrReverse(Tactic):
    def apply(self, goal, x, y, auto_remove=True):
        info = dict(goal=goal, x=x, y=y)
        if x:
            ta.arg_add_facts(goal.node, y)
            removed = []
            removed_str = []
            if auto_remove:
                g = goal
                while g is not None and ta.refuted_goal(g):
                    removed.append(g)
                    removed_str.append(str(g))
                    ta.remove_goal(g)
                    g = g.parent
                info['removed'] = removed
                if g is not None:
                    info['active'] = g
                else:
                    info['active'] = goal.node
            info['msg'] = dedent("""
            Learned new fact at arg node {}:
            {}
            Removed goals: {}
            """).strip().format(
                goal.node.id,
                y,
                ', '.join(removed_str),
            )
        else:
            ta.push_goal(y)
            info['active'] = y
            info['msg'] = dedent("""
            No refinement for goal {}, pushed new goal {}
            """).strip().format(goal, y)
        self.step(**info)
        return x


@goal_tactic
@tactic
class PathReach(Tactic):
    def apply(self, goal):
        res = ta._analysis_state.ivy_ag.bmc(goal.node, goal.formula, ta._analysis_state.crg)
        reachable = res is not None
        self.step(goal=goal, reachable=reachable)
        return reachable

@goal_tactic
@tactic
class PathReach1(Tactic):
    def apply(self, goal):
        res = ta._analysis_state.ivy_ag.bmc(goal.node, goal.formula, ta._analysis_state.crg, 1)
        reachable = res is not None
        self.step(goal=goal, reachable=reachable)
        return reachable


@goal_tactic
@tactic
class PushDiagram(Tactic):
    def apply(self, goal, weaken=False):
        dg = ta.get_diagram(goal, weaken)
        ta.push_goal(dg)
        self.step(goal=goal, diagram=dg, active=ta.top_goal())


@tactic
class RecalculateFacts(Tactic):
    def apply(self, node, facts):
        preds, action = ta.arg_get_preds_action(node)
        assert action != 'join'
        assert len(preds) == 1
        pred = preds[0]
        already_implied = ta.implied_facts(
            arg_get_fact(node),
            facts
        )
        implied = ta.implied_facts(
            forward_image(arg_get_fact(pred), action),
            list(set(facts) - set(already_implied)),
        )
        if len(implied) > 0:
            for fact in implied:
                ta.arg_add_facts(node, fact)
            self.step(node=node, facts=facts, implied=implied)
            return True
        else:
            return False


@tactic
class RemoveFacts(Tactic):
    def apply(self, node, *facts):
        """
        Remove facts from arg node

        facts should be formulas from node.clauses.fmlas
        """
        ta.arg_remove_facts(node, *facts)
        self.step(node=node, facts=facts)


@tactic
class ExecuteAction(Tactic):
    def apply(self, node, action, abstractor):
        new_node = ta.arg_add_action_node(node, action, abstractor)
        self.step(node=node, action=action)


@tactic
class PushNewGoal(Tactic):
    def apply(self, formula, node):
        push_goal(goal_at_arg_node(formula, node))
        self.step(node=node, formula=formula, active=ta.top_goal())


@tactic
class CheckCover(Tactic):
    def apply(self, covered, by):
        result = ta.arg_is_covered(covered, by)
        self.step(covered=covered, by=by, result=result)
        return result

@tactic
class Join2(Tactic):
    def apply(self, node1, node2):
        ta._ivy_ag.join(node1,node2,lambda s: None)
        self.step(node1=node1,node2=node2)


@tactic
class UPDR(Tactic):
    def apply(self):
        frames = ta._ivy_ag.states
        bad_states = negate_clauses(get_safety_property())
        action = get_big_action()
        ta._ivy_ag.actions[repr(action)] = action

        init_frame = last_frame = frames[0]

        # TODO: test conjecture in initial

        with InterruptContext() as ic:
            while not ic.interrupted:

                # the property is true in all frames and all "clauses" are pushed
                # the goal stack is empty

                # check if we found an infuctive invariant
                for i in range(len(frames) - 1):
                    if check_cover(frames[i + 1], frames[i]):
                        return True

                # add new frame

                last_frame = ta.arg_add_action_node(last_frame, action, None)
                push_goal(goal_at_arg_node(bad_states, last_frame))
                self.step(label='new frame')

                # push facts to last frame
                recalculate_facts(last_frame, ta.arg_get_conjuncts(arg_get_pred(last_frame)))

                while not ic.interrupted:
                    current_goal = top_goal()
                    if current_goal is None:
                        # goal stack is empty
                        break

                    if remove_if_refuted(current_goal):
                        continue

                    if current_goal.node == init_frame:
                        # no invariant
                        print "No Invariant!"
                        return False

                    push_diagram(current_goal, False)

                    dg = top_goal()

                    if refine_or_reverse(dg, False):
                        pass
                        # dg is proved,

                        # # propagate phase
                        # for i in range(1, len(frames)):
                        #     facts_to_check = (set(arg_get_conjuncts(frames[i-1])) -
                        #                       set(arg_get_conjuncts(frames[i])))
                        #     recalculate_facts(frames[i], facts_to_check)

                    else:
                        # new goal pushed
                        pass

                # propagate phase
                for i in range(1, len(frames)):
                    facts_to_check = (set(arg_get_conjuncts(frames[i-1])) -
                                      set(arg_get_conjuncts(frames[i])))
                    recalculate_facts(frames[i], list(facts_to_check))

            assert ic.interrupted
            print "UPDR Interrupted by SIGINT"
            return None


if __name__ == '__main__':
    from proof import AnalysisSession
    #fn = '../src/ivy/test.ivy'
    fn = '../examples/ivy/client_server_sorted.ivy'
    #fn = '../examples/pldi16/leader_sorted.ivy'
    analysis_session = AnalysisSession(fn)
    updr = UPDR(analysis_session)
    res = updr()

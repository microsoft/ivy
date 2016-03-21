#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This module contains functions that should be used by tactics.

The idea is that tactics code is decoupled from the actual
implementation of these in terms of the internal data structures, and
if that changes, only this file needs to change but the tactics code
remains the same.
"""

import re
import inspect

from ivy_actions import ChoiceAction
import ivy_transrel
import ivy_solver
from ivy_transrel import is_skolem
import ivy_alpha
from ivy_logic_utils import (and_clauses, formula_to_clauses,
                             clauses_to_formula, true_clauses,
                             false_clauses, negate_clauses, Clauses)
from logic import And, Not
from logic_util import normalize_quantifiers
from proof import ProofGoal
import ui_extensions_api


# class Facts(object):
#     """
#     Wraps an Ivy1 ivy_interp.State.value triplet
#     """

# class ReachabilityNode(object):
#     """
#     Compatible with ivy_iterp.State
#     """

# session and state related


def set_context(analysis_session):
    global _analysis_session
    global _analysis_state
    global _ivy_interp
    global _ivy_ag
    _analysis_session = analysis_session
    _analysis_state = _analysis_session.analysis_state
    _ivy_interp = _analysis_state.ivy_interp
    _ivy_ag = _analysis_state.ivy_ag


def step(**step_info):
    _analysis_session.step(step_info)


# Model related

def get_safety_property():
    """
    Retrun the safety property
    """
    return _ivy_interp.conjs[0]


def get_action(action_name):
    return _ivy_ag.actions[action_name]


def get_big_action():
    """
    Return an action which is a big choice between all possible
    actions.
    """
    exported_action_names = [e.exported() for e in _ivy_ag.exports]
    exported_actions = [_ivy_ag.actions[k] for k in exported_action_names]
    result = ChoiceAction(*exported_actions)
    result.label = ' + '.join(exported_action_names)
    return result


# Abstract Reachability Graph related

def arg_node(key):
    """
    Get ARG node by key from the current context
    """
    return _ivy_ag.states[key]


def arg_initial_node():
    """
    Add an initial node to the abstract reachability graph (arg) and
    return it.
    """
    # right now, the initial state is already added as the first
    # state, so just return it
    return _ivy_ag.states[0]


def arg_is_covered(covered, by):
    """
    Return True iff covered is covered by by
    """
    return _ivy_ag.cover(covered, by)


def arg_add_action_node(pre, action, abstractor=None):
    """
    Add a new node with an action edge from pre, and return it.
    """
    try:
        label = [k for k, v in _ivy_ag.actions.iteritems() if v == action][0]
    except IndexError:
        label = None
    node = _ivy_ag.execute(action, pre, abstractor, label)
    if abstractor is None:
        node.clauses = true_clauses()
    return node

class Abstractors(object):
    """
    Container class for abstractors
    """

    @staticmethod
    def concrete(node):
        pass

    @staticmethod
    def top_bottom(node):
        # TODO: change this to use the concrete post already there
        preds, action = arg_get_preds_action(node)
        assert action != 'join'
        assert len(preds) == 1
        pred = preds[0]
        implied = implied_facts(
            forward_image(arg_get_fact(pred), action),
            [false_clauses()],
        )
        if len(implied) == 1:
            node.clauses = false_clauses()
        else:
            node.clauses = true_clauses()

    @staticmethod
    def propagate(node):
        """
        Propagate clauses from predecessor
        """
        preds, action = arg_get_preds_action(node)
        assert action != 'join'
        assert len(preds) == 1
        pred = preds[0]
        implied = implied_facts(
            forward_image(arg_get_fact(pred), action),
            list(arg_get_conjuncts(pred)),
        )
        node.clauses = true_clauses()
        for fact in implied:
            arg_add_facts(node, fact)

    @staticmethod
    def propagate_and_conjectures(node):
        """
        Propagate clauses from predecessor
        """
        preds, action = arg_get_preds_action(node)
        assert action != 'join'
        assert len(preds) == 1
        pred = preds[0]
        implied = implied_facts(
            forward_image(arg_get_fact(pred), action),
            list(_ivy_interp.conjs),
        )
        node.clauses = true_clauses()
        for fact in implied:
            arg_add_facts(node, fact)


    @staticmethod
    def concept_space(node):
        ivy_alpha.alpha(node)


def arg_add_join_node(*preds):
    """
    Add a new node that is the join of preds, and return it.
    """
    assert len(preds) == 2
    _ivy_ag.join_states(preds[0], preds[1])


def arg_add_facts(node, *facts):
    """
    Add facts to arg node
    """
    for f in facts:
        node.clauses = and_clauses(node.clauses, f)


def arg_remove_facts(node, *facts):
    """
    Remove facts from arg node

    facts should be formulas from node.clauses.fmlas
    """
    c = node.clauses
    to_remove = frozenset(facts)
    node.clauses = Clauses(
        [f for f in c.fmlas if f not in to_remove],
        list(c.defs),
    )


def arg_get_fact(node):
    """
    Return the facts at an arg node
    """
    # TODO: figure out if it's ok to remove these assertions...
    # assert node.clauses.is_universal_first_order()
    assert node.moded is None
    return node.clauses


def arg_get_conjuncts(node):
    """
    Return the facts at an arg node
    """
    # TODO: figure out if it's ok to remove these assertions...
    # assert node.clauses.is_universal_first_order()
    assert node.moded is None
    return node.clauses.conjuncts()


def arg_get_preds_action(node):
    """
    Returns a pair: preds, action
    """
    if node.pred is not None:
        return [node.pred], node.action

    elif hasattr(node, 'join_of') and node.join_of is not None:
        return node.join_of, 'join'

    else:
        assert False


def arg_get_pred(node):
    assert node.pred is not None
    return node.pred


def arg_preorder_traversal(node):
    # TODO
    return _ivy_ag.states


# "Semantics" and SMT-solving related


def forward_image(pre_fact, action):
    """
    """
    axioms = _ivy_interp.background_theory()
    return ivy_transrel.forward_image(
        pre_fact,
        axioms,
        action.update(_ivy_interp, None),
    )


def backward_image(post_fact, action):
    """
    """
    axioms = _ivy_interp.background_theory()
    return ivy_transrel.reverse_image(
        post_fact,
        axioms,
        action.update(_ivy_interp, None),
    )


def refine_or_reverse(goal):
    preds, action = arg_get_preds_action(goal.node)
    assert action != 'join'
    assert len(preds) == 1
    pred = preds[0]
    axioms = _ivy_interp.background_theory()
    #import IPython
    #IPython.embed()
    print "calling ivy_transrel.forward_interpolant"
    x = ivy_transrel.forward_interpolant(
        pred.clauses,
        action.update(_ivy_interp, None),
        goal.formula,
        axioms,
        None,
    )
    print "    got: {!r}".format(x)
    if x is None:
        bi = backward_image(goal.formula, action)
        return False, goal_at_arg_node(bi, pred)
    else:
        return True, x[1]


def implied_facts(premise, facts_to_check):
    """
    Return a list of facts from facts_to_check that are implied by
    theory
    """
    from z3_utils import z3_implies_batch
    axioms = _ivy_interp.background_theory()
    premise = normalize_quantifiers((and_clauses(axioms, premise)).to_formula())
    facts_to_check = [f.to_formula() if type(f) is Clauses else f for f in facts_to_check]
    result = z3_implies_batch(premise, facts_to_check, False)
    return [f for f, x in zip(facts_to_check, result) if x]


def get_diagram(goal, weaken=False):
    axioms = _ivy_interp.background_theory()
    d = ivy_solver.clauses_model_to_diagram(
        and_clauses(goal.node.clauses, goal.formula),
        is_skolem,
        #None,
        false_clauses(),
        axioms=axioms,
        weaken=weaken,
    )
    return goal_at_arg_node(d, goal.node)


def refuted_goal(goal):
    from z3_utils import z3_implies
    axioms = _ivy_interp.background_theory()
    premise = (and_clauses(axioms, goal.node.clauses)).to_formula()
    f = Not(goal.formula.to_formula())
    return z3_implies(premise, f)


# Goals related


def goal_at_arg_node(formula, node):
    """
    Create a new goal and return it
    """
    return ProofGoal(formula, node)


def push_goal(goal):
    """
    Push a goal in the goal stack
    """
    _analysis_state.goal_stack.push(goal)


def top_goal():
    """
    Returns the goal on top of the stack
    """
    return _analysis_state.goal_stack.top()


def remove_goal(goal):
    """
    Remove goal from stack
    """
    _analysis_state.goal_stack.remove(goal)


def goal(key):
    """
    Get goal by key from the current context
    """
    return _analysis_state.goal_stack.stack[key]


# Tactis


class Tactic(object):
    """
    """
    def __init__(self, analysis_session=None):
        if analysis_session is None:
            # get from global context
            analysis_session = _analysis_session

        self.analysis_session = analysis_session

    def __call__(self, *args, **kwargs):
        from IPython import embed
        set_context(self.analysis_session)
        # call pre hooks
        print "Applying tactic: {}".format(type(self).__name__)
        #embed()
        result = self.apply(*args, **kwargs)
        print "Applying tactic: {} resulted in {}".format(type(self).__name__, result)
        #embed()
        # call post hooks
        return result

    def apply(self, *args, **kwargs):
        raise NotImplementedError()

    def step(self, **step_info):
        step_info['tactic'] = type(self).__name__
        self.analysis_session.step(step_info)


# generate functions that apply tactics to the current context
def convert_from_camel_case(name):
    s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
    return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()


def tactic(tactic_cls):
    """
    Class decorator applied to tactics and adds a function for calling
    the tactic in the current context.
    """
    tactic_name = convert_from_camel_case(tactic_cls.__name__)

    # add function for calling the tactic on the current context to
    # the caller's namespace
    inspect.currentframe(1).f_globals[tactic_name] = (lambda t: (
        lambda *args, **kwargs: t()(*args, **kwargs)
    ))(tactic_cls)
    return tactic_cls


def goal_tactic(tactic_cls):
    """
    Class decorator applied to goal tactics.

    Adds an action to goal_node_actions to perform the tactic.

    The tactic must be applicable with a single goal argument.
    """
    tactic_name = convert_from_camel_case(tactic_cls.__name__)
    tactic_label = tactic_name.replace('_', ' ')

    # register the tactic with the ui
    ui_extensions_api.goal_node_actions.register(lambda goal: [
        (tactic_label, ui_extensions_api.apply_goal_tactic, tactic_name)
    ])

    # return unmodified
    return tactic_cls


if __name__ == '__main__':
    from proof import AnalysisSession

    session = AnalysisSession('../src/ivy/test.ivy')
    set_context(session)

    a = get_big_action()
    s0 = arg_initial_node()
    s1 = arg_add_action_node(s0, a)
    arg_is_covered(s1, s0)
    arg_add_facts(s0, arg_get_fact(s0))
    forward_image(arg_get_fact(s0), a)
    backward_image(arg_get_fact(s0), a)

    c = get_safety_property()
    g = goal_at_arg_node(negate_clauses(c), s1)
    d = get_diagram(g)
    x = refine_or_reverse(g)

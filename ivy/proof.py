#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This file contains various classes for the proof/analysis
process. It will later be split to multiple modules.
"""

from copy import deepcopy

from ivy_compiler import ivy_load_file, ivy_new, IvyError
from ivy_art import AnalysisGraph
from ivy_utils import use_numerals

class IvyModel(object):
    """
    This represents what comes out of the .ivy file. Namely, the set
    of actions, the initial state, and the axioms.

    Right now this is a wrapper around ivy1 objects, that will be
    replaced in the future.
    """
    def __init__(self, filename):
        ag = ivy_new()
        try:
            ivy_load_file(open(filename), ag)
        except IvyError as e:
            e.filename = filename
            raise e
        self.ivy_ag = ag
        self.ivy_interp = ag.domain


class AnalysisState(object):
    """
    This class represents the whole state of the analysis (or proof)
    process.

    Objects of this class are the containers for all the information
    heuristics use, such as list of known reachable states, known facts, etc.
    """
    def __init__(self, model):
        self.model = model # should be an IvyModel instance
        self.ivy_ag = model.ivy_ag
        self.ivy_interp = model.ivy_interp
        self.goal_stack = ProofGoalStack()
        self.conjectures = []
        # initialise an AnalysisGraph for the crg
        self.crg = AnalysisGraph(self.ivy_ag.domain, self.ivy_ag.pvars)
        self.crg.actions = self.ivy_ag.actions


class AnalysisSession(object):
    """
    """

    def __init__(self, filename, widget=None):

        # HACK: set this false until we can handle numerals in models.
        use_numerals.set("false")

        self.filename = filename
        try:
            m = IvyModel(filename)
        except IvyError as e:
            raise e
        self.analysis_state = AnalysisState(m)
        self.widget = widget
        self.history = []
        self.concept_domains = {}
        if self.widget is not None:
            self.widget.register_session(self)
        self.step(dict(label='init'))

    def step(self, info={}):
        # it's important to deepcopy both together to maintain refernces
        self.history.append(deepcopy(
            (self.analysis_state, info)
         ))
        if 'msg' in info:
            print info['msg']
        if self.widget is not None:
            self.widget.step()


class ProofGoal(object):
    def __init__(self, formula, node, parent=None):
        self.node = node
        self.formula = formula
        self.parent = parent
        self.id = None  # to be set by the ProofGoalStack

    def __str__(self):
        return str(self.id) if self.id is not None else repr(self)


class ProofGoalStack(object):
    def __init__(self):
        self.stack = []

    def push(self, goal):
        goal.id = len(self.stack)
        goal.parent = self.top()
        self.stack.append(goal)

    def pop(self):
        result = self.stack.pop()
        result.id = None
        return result

    def top(self):
        if len(self.stack) > 0:
            return self.stack[-1]
        else:
            return None

    def remove(self, goal):
        goal.id = None
        self.stack.remove(goal)


## classes not yet implemented / used


class ReachabilityGraph(object):
    """
    """
    def __init__(self):
        self.nodes = [] # list of ReachabilityNode objects, may should
                        # be a dict, mapping names to nodes
        self.edges = [] # tuples: (from, to, edge)

    def add_node(self):
        node = ReachabilityNode(self, None)
        self.nodes.append(node)
        return node

    def add_edge(self, source, target, edge):
        self.edge.append((source, target, edge))


class ReachabilityNode(object):
    """
    """
    def __init__(self, graph, state):
        self.graph = graph
        self.state = state


class ReachabilityEdge(object):
    """
    """
    def __init__(self, graph, action):
        self.graph = graph
        self.action = action


class AbstractState(object):
    """
    """
    def __init__(self, facts):
        self.facts = list(facts)


class ConcreteState(object):
    """
    """
    def __init__(self, x):
        self.x = x # TODO: change x to something else. In particular,
                   # we should be able to get a trace of a reachable
                   # state with intermediate values and annotations


class ProofManager(object):
    """
    """

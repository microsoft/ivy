#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
"""

from itertools import product
import copy

from concept_alpha import alpha
from logic import Var, Const, And, Not, ForAll, Eq, TopSort, SortError
from logic_util import (free_variables, used_constants,
                        is_tautology_equality, normalize_quantifiers, substitute)
from z3_utils import z3_implies
from concept import Concept

from ivy_utils import constant_name_generator, dbg


def _normalize_facts(facts):
    facts = normalize_quantifiers(And(*facts))
    assert type(facts) is And
    return [f for f in facts if not is_tautology_equality(f)]


class ConceptInteractiveSession(object):
    """
    """

    def __init__(self,
                 domain,
                 state,
                 axioms,
                 goal_constraints=[],
                 suppose_constraints=[],
                 widget=None,
                 analysis_session=None,
                 cache = None,
                 recompute = True):
        self.analysis_session = analysis_session
        self.domain = domain
        self.state = state
        self.axioms = axioms
        self.goal_constraints = goal_constraints
        self.suppose_constraints = suppose_constraints
        self.widget = widget
        self.undo_stack = []
        self.info = ''
        if self.widget is not None:
            self.widget.concept_session = self
        self.cache = cache
        if recompute:
            self.recompute()

    def clone(self,recompute=True):
        result = ConceptInteractiveSession(
            self.domain.copy(),
            self.state,
            self.axioms,
            self.goal_constraints[:],
            self.suppose_constraints[:],
            self.widget,
            self.analysis_session,
            copy.copy(self.cache),  # make shallow copy of cache!
            recompute
        )
        result.undo_stack = self.undo_stack[:]
        return result

    def _to_formula(self):
        return And(
            self.state,
            self.axioms,
            *(self.goal_constraints + self.suppose_constraints)
        )

    def _fresh_const_name(self, extra=frozenset()):
        contents = ([self._to_formula()] +
                    [c.formula for n,c in self.domain.concepts.iteritems() if isinstance(c,Concept)])
        used = frozenset(c.name for c in (
            used_constants(*contents) | extra
        ))
        return next(name for name in constant_name_generator()
                    if name not in used)

    def get_projection(self):
        if self.widget != None and hasattr(self.widget,'projection'):
            return self.widget.projection
        return None
            
    def recompute(self,projection = None):
        projection = projection or (lambda *args: True)
        self.abstract_value = alpha(self.domain, self._to_formula(), self.cache,
                                    projection = projection)
        if self.widget is not None:
            self.widget.render()

    def push(self):
        self.undo_stack.append((self.domain.copy(), self.suppose_constraints[:]))

    def pop(self):
        domain, suppose_constraints = self.undo_stack.pop()
        self.domain = domain.copy()
        self.suppose_constraints = suppose_constraints[:]

    def undo(self):
        self.pop()
        self.recompute()

    def split(self, concept, split_by):
        self.push()
        self.domain.split(concept, split_by)
        self.recompute()

    def remove_concepts(self, *concepts):
        self.push()
        for concept in concepts:
            del self.domain.concepts[concept]
            self.domain.replace_concept(concept, [])
        self.recompute()

    def _suppose_empty(self,concept):
        f = self.domain.concepts[concept].formula
        self.suppose_constraints.append(
            ForAll(free_variables(f), Not(f))
        )

    def suppose_empty(self, concept):
        self.push()
        self._suppose_empty(concept)
        self.recompute()

    def _get_witnesses(self, concept_name):
        # TODO: maybe this function should be in ConceptDomain? or Concept?
        """
        Return a list of constant that are witnesses for the given unary
        constant, or [] if none are found

        A witness is a constant c s.t. concept(x) implies x=c. Note
        that this does not necessarily mean that concept(c) holds.
        """
        concept = self.domain.concepts[concept_name]
        assert concept.arity == 1
        sort = concept.variables[0].sort
        assert sort != TopSort()

        if sort.name == 'unit':
            return [Const('0',sort)]

        constants = used_constants(concept.formula)
        x = Const(self._fresh_const_name(constants), sort)
        f = concept(x)
        def is_witness(c):
            try:
                return z3_implies(f, Eq(x, c))
            except SortError:
                return False

        return [c for c in constants if is_witness(c)]

    def _materialize_node(self, concept_name):
        """
        Materialize a node, returns the witness constant
        """
        concept = self.domain.concepts[concept_name]
        assert concept.arity == 1
        sort = concept.variables[0].sort
        assert sort != TopSort()
        witnesses = self._get_witnesses(concept_name)
        if len(witnesses) > 0:
            c = witnesses[0]
        else:
            c = Const(self._fresh_const_name(), sort)
            # TODO: maybe we shouldn't split here, and create the concepts explicitly
            X = Var('X', c.sort)
            name = '={}'.format(c.name)
            self.domain.concepts[name] = Concept(name,[X], Eq(X,c))
            self.domain.split(concept_name, name)
        self.suppose(concept(c))
        return c

    def suppose(self,fmla):
        if not is_tautology_equality(fmla):
            self.suppose_constraints.append(fmla)

    def materialize_node(self, concept_name):
        self.push()
        self._materialize_node(concept_name)
        self.recompute()

    def _materialize_edge(self, edge, source, target, polarity):
        edge_concept = self.domain.concepts[edge]
        source_c = self._materialize_node(source)
        if source == target:
            target_c = source_c
        else:
            target_c = self._materialize_node(target)        
        f = edge_concept(source_c, target_c)
        self.suppose(f if polarity else Not(f))
        return (source_c,target_c)

    def materialize_edge(self, edge, source, target, polarity):
        """
        Materialize an edge to either positive or negative
        """
        self.push()
        _materialize_edge(self, edge, source, target, polarity)
        self.recompute()

    def get_node_facts(self, node):
        """
        Returns a list of facts used by gather
        """
        a = dict(self.abstract_value)
        facts = []
        if a[('node_info', 'at_least_one', node)]:
            for c in self._get_witnesses(node):
                facts.append(self.domain.concepts[node](c))
                for nl in self.domain.concepts['node_labels']:
                    if a.get(('node_label', 'node_necessarily', node, nl)):
                        facts.append(self.domain.concepts[nl](c))
                    elif a.get(('node_label', 'node_necessarily_not', node, nl)):
                        facts.append(Not(self.domain.concepts[nl](c)))
                for nl in self.domain.concepts['enum_case']:
                    if a.get(('node_label', 'node_necessarily', node, nl)):
                        facts.append(self.domain.concepts[nl](c))
        return _normalize_facts(facts)

    def _get_edge_fact(self,edge,source,target,polarity):
        facts = []
        edge_concept = self.domain.concepts[edge]
        source_witnesses = self._get_witnesses(source)
        target_witnesses = self._get_witnesses(target)
        for source_c, target_c in product(source_witnesses, target_witnesses):
            f = edge_concept(source_c, target_c)
            facts.append(f if polarity else Not(f))

        return _normalize_facts(facts)

    def get_edge_facts(self, edge, source, target, filter_polarity=None):
        """
        Returns a list of facts used by gather

        If filter_polarity is None, returns both positive and negative
        facts. If filter_polarity is True/False, returns only
        positive/negative.
        """
        a = dict(self.abstract_value)
        x = (edge, source, target)

        if ('edge_info', 'all_to_all') + x not in a:
            # not a well-sorted edge
            return []

        if a[('edge_info', 'none_to_none') + x]:
            polarity = False
        elif a[('edge_info', 'all_to_all') + x]:
            polarity = True
        else:
            # not a definite edge
            return []

        if filter_polarity is not None and filter_polarity != polarity:
            return []

        return self._get_edge_fact(edge,source,target,polarity)

    def get_facts(self,projection=None):
        """
        Returns a list of facts used by gather
        """

        facts = []
        for node in self.domain.concepts['nodes']:
            facts.extend(self.get_node_facts(node))
        
        for tag,value in self.abstract_value:
            if value:
                if tag[0] == 'edge_info' and tag[1] in ('none_to_none','all_to_all'):
                    if projection is None or projection(tag[2],'edges',tag[1]):
                        facts.extend(self._get_edge_fact(tag[2],tag[3],tag[4],tag[1]=='all_to_all'))

        return facts

    def save_domain(self, name):
        self.analysis_session[name] = self.domain.copy()

    def load_domain(self, name):
        self.push()
        self.domain = self.analysis_session[name].copy()
        self.recompute()

    def replace_domain(self, new_domain, new_suppose_constraints=[]):
        self.push()
        self.domain = new_domain.copy()
        self.suppose_constraints = new_suppose_constraints[:]
        self.recompute()

    def get_projections(self, node):
        """
        Return a list of (name, binary_concept) with all possible
        projections at node
        """
        witnesses = self._get_witnesses(node)
        if len(witnesses) == 0:
            return []

        w = witnesses[0]
        result = []
        n_concept = self.domain.concepts[node]
        for t_name in self.domain.concepts_by_arity(3):
            t_concept = self.domain.concepts[t_name]
            for v in t_concept.variables:
                if v.sort == w.sort:
                    variables = [x for x in t_concept.variables if x is not v]
                    formula = substitute(t_concept.formula, {v: w})
                    name = str(formula)
                    concept = Concept(name,variables, formula)
                    result.append((name, concept))
        return result

    def add_edge(self, name, concept):
        self.push()
        self.domain.concepts[name] = concept
        self.domain.concepts['edges'].append(name)
        self.recompute()

    def add_custom_edge(self, edge, source, target):
        self.push()
        self.domain.combinations.append(
            ('custom_edge_info', 'edge_info', edge, source, target)
        )
        self.recompute()

    def add_custom_node_label(self, node, node_label):
        self.push()
        self.domain.combinations.append(
            ('custom_node_label', 'node_label', node, node_label)
        )
        self.recompute()

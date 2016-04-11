#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
#TODO: get z3 references out of this file
#TODO: the import *'s are creating conflicts
import z3
from ivy_logic import Literal,Atom,Variable,Constant,Symbol,App,sig,EnumeratedSort,equals,RelationSort,UninterpretedSort,all_symbols,Equals,And
from ivy_solver import *
from ivy_logic_utils import to_clause,to_literal,to_atom,used_constants_clauses,used_unary_relations_clauses,\
         rename_clause, substitute_clause, is_equality_lit, eq_lit, substitute_lit, is_taut_equality_lit,\
         unused_constant, used_symbols_clauses, used_symbols_clause, used_symbols_ast, used_unary_functions_clauses, used_functions_clauses,\
         has_enumerated_sort, var_to_skolem, variables_ast, used_variables_in_order_clauses, used_variables_in_order_clause,\
         substitute_clauses, substitute_constants_clause, clauses_to_formula, dual_clauses, true_clauses, and_clauses, Clauses, clause_to_formula, substitute_ast
import functools
from ivy_alpha import ProgressiveDomain
from ivy_concept_space import NamedSpace, SumSpace, ProductSpace
from ivy_transrel import is_skolem
from ivy_utils import union_to_list
import string
from collections import defaultdict

import ivy_logic as il
import concept as co
import concept_interactive_session as cis
from dot_layout import dot_layout
from cy_elements import CyElements


def get_projections_of_ternaries(wit):
#    print "witness: {}".format(wit)
    for sym in ivy_logic.all_symbols():
#        print "rel: {}. sort = {}".format(sym,sym.sort)
        if sym.is_relation() and len(sym.sort.dom) == 3:
#            print "ternary: {}, sort = {}".format(sym,sym.sort)
            for i in range(3):
                if sym.sort.dom[i] == wit.sort:
                    yield Literal(1,sym(*[t if t is wit else Variable(t,s) for t,s in zip(lins(['X','Y'],i,wit),sym.sort.dom)]))
                    


# This creates a concept from a formula with free variables, using the
# variables in alphabetical order.  A canonical concept name is
# generated from the formula.

def concept_from_formula(fmla):
    vs = sorted(list(used_variables_ast(fmla)),key=str)
    name = (','.join(str(v) + ':' + str(v.sort) for v in vs)
            + '.' + str(fmla))
    return co.Concept(name,vs,fmla)

def add_domain_concept(concepts,fmla,kind=None):
    con = concept_from_formula(fmla)
    arity = con.arity
    name = con.name
    if 1 <= arity and arity <= 2:
        kind = kind or ('node_labels' if arity==1 else 'edges')
        concepts[name] = con
        concepts[kind].append(name)
 
def empty_concepts():
    concepts = co.ConceptDict()
    concepts['nodes'] = []
    concepts['node_labels'] = []
    concepts['edges'] = []
    return concepts

def make_concept_domain(concepts):
    return co.ConceptDomain(concepts, co.get_standard_combiners(), co.get_standard_combinations())
    
# This creates the default initial concept graph, with one
# node for each sort.

def initial_concept_domain(sorts):

    concepts = empty_concepts()

    # add one node for each sort
    for sort in sorts:
        X = Variable('X', sort)
        add_domain_concept(concepts,Equals(X,X),kind='nodes')
        
    return make_concept_domain(concepts)

def replace_concept_domain_vocabulary(concept_domain,symbols):

    concepts = empty_concepts()

    # keep all the old nodes

    old_concepts = concept_domain.concepts
    for node in old_concepts['nodes']:
        concepts['nodes'].append(node)
        concepts[node] = old_concepts[node]

    # add concepts from the signature

    for c in sorted(symbols,key=str):

        dom,rng = c.sort.dom,c.sort.rng

        if il.is_enumerated_sort(rng):
            # TODO: we have no way to display enumerated constants
            if len(dom) in [1,2]:
                for cons in rng.constructors:
                    vs = [Variable(n,s) for n,s in zip(['X','Y'],dom)]
                    add_domain_concept(concepts,Equals(c(*vs),cons))

        elif il.is_boolean_sort(rng):
            # TODO: we have no way to display boolean constants
            if len(dom) in [1,2]:
                vs = [Variable(n,s) for n,s in zip(['X','Y'],dom)]
                add_domain_concept(concepts,c(*vs))

        elif il.is_first_order_sort(rng):
            if len(dom) == 0:
                add_domain_concept(concepts,Equals(Variable('X', rng),c))
            elif len(dom == 1):
                fmla = Equals(c(Variable('X', dom[0])),Variable('Y', rng))
                add_domain_concept(concepts,fmla)

    return make_concept_domain(concepts)

                


_edge_display_classes = ['all_to_all', 'edge_unknown', 'none_to_none']
_edge_display_checkboxes = _edge_display_classes + ['transitive']
_node_label_display_checkboxes = ['node_necessarily', 'node_maybe', 'node_necessarily_not']

class Option(object):
    def __init__(self,val=False):
        self.val = True if val else False
    @property
    def value(self):
        return self.val

_label_prefix = {
    'node_necessarily': '',
    'node_necessarily_not': u'\u00AC', # negation sign
    'node_maybe': '?',
}

_label_prefix_equality = {
    'node_necessarily': '=',
    'node_necessarily_not': u'\u2260', # not equal sign
    'node_maybe': u'\u225F', # =? sign
}

def get_shape(concept_name):
    return 'octagon'


def get_transitive_reduction(widget, a, edges):
    """
    Return a list of (edge, source, target) of edges that should not
    be displayed due to transitive reduction (also reflexive reduction).
    """

    # filter only all_to_all edges for which transitive reduction is turned on
    edges = [x for x in edges if
             widget.edge_display_checkboxes[x[0]]['transitive'].value and
             a[('edge_info', 'all_to_all') + x]]

    # first hide all self edges
    result = [x for x in edges if x[1] == x[2]]
    edges = [x for x in edges if x[1] != x[2]]

    by_source = defaultdict(list)
    for edge, source, target in edges:
        by_source[(edge, source)].append(target)

    for edge, x, y in edges:
        for z in by_source[(edge, y)]:
            result.append((edge, x, z))

    return frozenset(result)

def render_concept_graph(widget):
    """
    Render the result of concept_alpha to an annotated graph.

    The graph is represented using Python objects compatible with
    Cytoscape's JSON format.

    TODO: maybe this should be a method of ConceptSessionWidget
    """

    concept_session = widget.concept_session

    a = dict(concept_session.abstract_value)
    domain = concept_session.domain

    # treat custom_edge_info and custom_node_label
    custom = set()
    for tag in a.keys():
        if tag[0].startswith('custom_'):
            not_custom_tag = (tag[0][len('custom_'):],) + tag[1:]
            a[not_custom_tag] = a[tag]
            custom.add(tag[2:])

    # get information from the abstract value
    nodes = set()
    node_labels = set()
    edges = set()
    for tag in a:
        if tag[0] == 'node_info':
            nodes.add(tag[2])
        elif tag[0] == 'edge_info':
            nodes.add(tag[3])
            nodes.add(tag[4])
            edges.add(tag[2:])
        elif tag[0] == 'node_label':
            nodes.add(tag[2])
            node_labels.add(tag[3])
    nodes = sorted(nodes)
    node_labels = sorted(node_labels)
    edges = sorted(edges)

    g = CyElements()

    # add nodes
    non_existing_nodes = set()
    for node in nodes:
        if a[('node_info', 'none', node)]:
            non_existing_nodes.add(node)
            classes = ['non_existing']
            class_disp = 'non existing'
        elif a[('node_info', 'at_least_one', node)] and a[('node_info', 'at_most_one', node)]:
            classes = ['exactly_one']
            class_disp = 'exactly one'
        elif a[('node_info', 'at_least_one', node)]:
            classes = ['at_least_one']
            class_disp = 'at least one'
        elif a[('node_info', 'at_most_one', node)]:
            classes = ['at_most_one']
            class_disp = 'at most one'
        else:
            classes = ['node_unknown']
            class_disp = 'maybe non existing, maybe more than one'

        possible_splits = []
        label_lines = []
        for label_name in node_labels:
            if ('node_label', 'node_necessarily', node, label_name) not in a:
                # label not present, probably not well sorted, skip
                continue
            possible_splits.append(label_name)
            if a[('node_label', 'node_necessarily', node, label_name)]:
                k = 'node_necessarily'
            elif a[('node_label', 'node_necessarily_not', node, label_name)]:
                k = 'node_necessarily_not'
            else:
                k = 'node_maybe'
            if (widget.node_label_display_checkboxes[label_name][k].value is False and
                (node, label_name) not in custom):
                # don't add invisible labels
                continue
            label_lines.append(widget.concept_label(domain.concepts[label_name]))

        disp = widget.node_label(domain.concepts[node])
        label = '\n'.join([disp] + label_lines)
        info = '\n'.join(
            [
                node,
                str(domain.concepts[node]),
                class_disp,
            ] +
            label_lines
        )
        # cluster by sort in concrete models
        if '!' in node:
            cluster = node.split('!')[0].lower()
        else:
            cluster = None

        if hasattr(widget, 'apply_structure_renaming'):
            label = widget.apply_structure_renaming(label)
            info = widget.apply_structure_renaming(info)
            actions = [
                (widget.apply_structure_renaming(action[0]), ) + tuple(action[1:])
                for action in actions
            ]

        shape = get_shape(node)

        g.add_node(
            obj=node,
            label=label,
            classes=classes,
            short_info=info,
            long_info=info,
            events=[],
            locked=True,
            cluster=cluster,
            shape=shape,
        )

    # add edges
    hidden_by_transitive = get_transitive_reduction(widget, a, edges)
    for edge, source, target in edges:
        x = (edge, source, target)

        if (x in hidden_by_transitive and x not in custom):
            # don't draw edges hidden by transitive reduction
            continue

        if (source in non_existing_nodes or
            target in non_existing_nodes):
            # don't draw edges to non-existing nodes
            continue

        classes = []
        if a[('edge_info', 'none_to_none') + x]:
            classes.append('none_to_none')
        elif a[('edge_info', 'all_to_all') + x]:
            classes.append('all_to_all')
        else:
            classes.append('edge_unknown')

        if (widget.edge_display_checkboxes[edge][classes[0]].value is False and
            x not in custom):
            # don't add invisible edges
            continue

        if not a[('edge_info', 'none_to_none') + x]:
            classes += [
                c for c in [
                    'total',
                    'functional',
                    'surjective',
                    'injective',
                ] if a.get(('edge_info', c) + x)
            ]

        # TODO: custom edge labels
        labels = ['{}({}, {}):'.format(edge, source, target)]
        labels += [
            c.replace('_', ' ') for c in [
                'none_to_none',
                'all_to_all',
                'total',
                'functional',
                'surjective',
                'injective',
            ] if a.get(('edge_info', c) + x)
        ]

        if hasattr(widget, 'apply_structure_renaming'):
            labels[0] = widget.apply_structure_renaming(labels[0])

        g.add_edge(
            edge,
            source,
            target,
            label=edge,
            classes=classes,
            short_info='\n'.join(labels),
            long_info=[str(domain.concepts[edge])] + labels[1:],
            events=[],
        )

    return g


class ConceptStateViewWidget(object):
    def __init__(self,parent):

        self.parent = parent

        
    def copy(self):
        res = ConceptStateViewWidget(self.parent)
        return res



class Graph(object):
    def __init__(self,nodes,parent_state=None):
        self.constraints = true_clauses()
        self.parent_state = parent_state
        self.concept_domain = initial_concept_domain([s for n,f,s in nodes])

        # dict mapping edge names to widget tuples
        self.edge_display_checkboxes = defaultdict(
            lambda: dict((x, Option()) for x in _edge_display_checkboxes)
        )
        # dict mapping label names to widget tuples
        self.node_label_display_checkboxes = defaultdict(
            lambda: dict((x, Option()) for x in _node_label_display_checkboxes)
        )

        self.cy_elements = CyElements() # start with empty graph
        self.concept_session = None

    @property
    def sort_names(self):
        return sorted(list(sig.sorts))  # for now, display all declared sorts

    @property
    def relation_ids(self):
        """ Return ids of all the concepts that need check-boxes """
        return self.concept_domain.concepts['edges'] + self.concept_domain.concepts['node_labels']

    def concept_from_id(self,id):
        """ Get a relational concept from its id """
        return self.concept_domain.concepts[id]

    def id_from_concept(self,concept):
        """ Get a relational concept from its id """
        return concept.name

    @property
    def relations(self):
        """ Returns all the concepts that need check-boxes """
        return map(self.concept_from_id,self.relation_ids)

    @property
    def node_ids(self):
        """ Return ids of all the node concepts """
        return self.concept_domain.concepts['nodes']

    @property
    def nodes(self):
        """ Returns all the concepts that need check-boxes """
        return map(self.concept_from_id,self.node_ids)
    
    def node_sort(self,node):
        return node.sorts[0]

    # This gives the shorthand name for a concept used in node labels.
    
    def concept_label(self,concept):
        fmla = concept.formula
        for v in concept.variables:
            return str(substitute_ast(fmla,{v.rep:Variable('',v.sort)})).replace(' ','').replace('()','')
        return str(fmla)

    # This gives the top label of a node based on its concept

    def node_label(self,concept):
        return str(concept.sorts[0])

    # Get the projections of ternary relations using the witnesses of
    # a node.

    def get_projections(self,node):
        return self.concept_session.get_projections(node.name)

    # Parse a string into a concept

    def string_to_concept(self,text):
        # set up the signature with symbols in graph so
        # we can parse the formula.
        sig = ivy_logic.sig.copy()
        with sig:
            for c in used_constants_clauses(self.state):
                if not isinstance(c.sort,ivy_logic.EnumeratedSort):
                    ivy_logic.add_symbol(str(c),c.sort)
            for c in used_constants_clauses(self.constraints):
                if not isinstance(c.sort,ivy_logic.EnumeratedSort):
                    ivy_logic.add_symbol(str(c),c.sort)

            return to_literal(text)

    def set_state(self,clauses,recomp=True):
        self.state = clauses

        # Create a new concept domain using the vocabulary of the state

        vocab = set(list(all_symbols()) + list(used_symbols_clauses(clauses)))
        self.concept_domain = replace_concept_domain_vocabulary(self.concept_domain,vocab)
        state = clauses_to_formula(clauses)
        self.concept_session = cis.ConceptInteractiveSession(self.concept_domain,state,And(),cache={},recompute=False)
        self.recompute()

    def set_concrete(self,clauses):
        self.concrete = clauses

    def recompute(self):
        print "recompute..."
        self.concept_session.recompute(self.projection)
        self.cy_elements = dot_layout(render_concept_graph(self))

    # TODO: this seems to be unused -- remove?
    def get_facts(self,rels,definite=True):
        clauses = []
        if not definite:
            clauses += [[~lit for lit in n.fmla] for n in self.all_nodes if n.status == "false"]
            clauses += [rela_fact(1,equals,n,n)
                        for n in self.all_nodes
                        if (n.status != "false" and not n.summary and not any(is_equality_lit(lit) for lit in n.fmla))]
        for n in self.all_nodes:
            if n.status == 'true':
                wit = get_witness(n)
                if wit != None:
                    fmla = substitute_clause(n.fmla,{'X':(wit)})
                    clauses += [[lit] for lit in fmla if not is_taut_equality_lit(lit)]
        names = set(n.name for n in self.all_nodes if (n.status == "true" if definite else n.status != "false"))
        for (r,tvals) in rels:
            if tvals:
                clauses += r.get_definite_facts(names,tvals) if definite else r.get_facts(names,tvals)
        return clauses

    def set_checkbox(self,obj,idx,val):
        # HACK: can't tell if it's edge or node_label so set both
        val = Option(val)
        if idx < len(_edge_display_checkboxes):
            self.edge_display_checkboxes[obj][_edge_display_checkboxes[idx]] = val
        if idx < len(_node_label_display_checkboxes):
            self.node_label_display_checkboxes[obj][_node_label_display_checkboxes[idx]] = val

    def get_transitive_reduction(self):
        return [] # TODO: implement
        
    def projection(self,concept_name,concept_class):
        if concept_class in ('node_labels','edges'):
            cb = self.edge_display_checkboxes if concept_class == 'edges' else self.node_label_display_checkboxes
            boxes = cb[concept_name]
            return any(boxes[i].value for i in boxes if i != 'transitive')
        return True

    def copy(self):
        c = Graph([])
        c.cy_elements = self.cy_elements
        c.concept_session = self.concept_session.clone(recompute=False)
        c.parent_state = self.parent_state
        c.constraints = self.constraints.copy()
        c.attributes = []
        if hasattr(self,'reverse_result'):
            c.reverse_result = list(self.reverse_result)
        return c

    def state_implies_fmla(self,fmla):
        s = self.solver
        res = s_check_fmla(s,fmla)
        return res == z3.unsat

    def split_n_way(self,node,ps):
#        print "split_n_way, ps = {}".format([str(p) for p in ps])
        self.all_nodes = [n for n in self.all_nodes if n is not node]
        for p in ps:
            label = self.concept_label(p)
            posname = node.name + "+" + label
            self.all_nodes.append(GraphNode(posname, node.fmla + [p],node.sort))
        self.needs_recompute = True

    def split(self,node,p):
        if isinstance(p,tuple):
            self.split_n_way(node,[eq_lit(p[0],x) for x in p[1]])
            return
        nid,pid = (self.id_from_concept(x) for x in (node,p))
        self.concept_session.domain.split(nid,pid)
        self.recompute()

    def splatter(self,node,constants = None):
        if constants == None:
            constants = used_constants_clauses(self.constraints)
        eqs = [eq_lit(node.variable('X'),Constant(c)) for c in constants if c.sort == node.sort]
#        print "splatter eqs = {}".format(eqs)
        self.split_n_way(node,eqs)

    def add_constraints(self,cnstrs,recompute=True):
        g = self
#        fc = [c for c in cnstrs if not g.state_implies_fmla(c)]
        fc = cnstrs
        if fc:
            g.set_state(and_clauses(g.state,Clauses(fc)),recompute)
            g.constraints = and_clauses(g.constraints,Clauses(cnstrs))

    def empty(self,node):
        g = self
        fmla = il.Not(node.formula)
        self.add_constraints([fmla])

    def add_witness_constraint(self,node,nc):
        g = self
        fmla = substitute_clause(node.fmla,{'X':nc})
        self.add_constraints([[lit]
                              for lit in fmla if not is_taut_equality_lit(lit)],False)

    def witness(self,node):
        g = self
        for lit in node.fmla:
#            print lit
            if is_equality_lit(lit) and isinstance(lit.atom.args[0],Variable):
                self.add_witness_constraint(node,lit.atom.args[1])
                return lit.atom.args[1]
        uc = used_symbols_clauses(g.state)
        fmlas = [n.fmla for n in g.all_nodes]
        for f in fmlas:
            uc.update(used_symbols_clause(f))
        nc = unused_constant(uc,node.sort)
#        print "type(nc) = {}".format(type(nc))
        self.add_witness_constraint(node,nc)
        self.split(node,eq_lit(Variable('X',node.sort),nc))
        return nc 

    def materialize(self,node):
        self.witness(node)

    def empty_edge(self,rel_lit,head,tail):
        g = self
        fmla = [~lit for lit in head.fmla] + [~substitute_lit(lit,{'X':Variable('Y')}) for lit in tail.fmla] + [~rel_lit]
#        print "adding clause: %s" % fmla
        self.add_constraints([fmla])


    def materialize_edge(self,rel_lit,head,tail):
        g = self
        head_witness = self.witness(head)
        if tail is head:
            tail_witness = head_witness
        else:
            tail_witness = self.witness(tail)
        fmla = [apply_edge_rel(rel_lit,head_witness,tail_witness)]
#        print "adding clause: %s" % fmla
        self.add_constraints([fmla])

    @property
    def attributes(self):
        if not hasattr(self,'_attributes'):
            self._attributes = []
        return self._attributes

    @attributes.setter
    def attributes(self,value):
        self._attributes = value

# we want graphs to be picklable, but can't pickle Z3, so we reconstruct Z3 on unpickling

    def __getstate__(self):
        odict = self.__dict__.copy()     # copy the dict since we change it
        del odict['solver']              # remove the sover entry
        if 'post' in odict:
            del odict['post']                # remove the Z3 version of clauses
        return odict

    def __setstate__(self, state):
        self.__dict__.update(state)   # update attributes
        # get Z3 up to date
        self.solver = z3.Solver()
        self.solver.push()
        with self.parent_state.domain.sig:
            s_add(self.solver,clauses_to_z3(self.solver_clauses))

class GraphStack(object):
    """ A Graph with an undo/redo stack. """
    def __init__(self,graph):
        self.current = graph
        self.undo_stack = []
        self.redo_stack = []
        
    def can_undo(self):
        return len(self.undo_stack) > 0

    def undo(self):
        """ Roll back to most recent checkpoint """
        if self.undo_stack:
            self.redo_stack.append(self.current)
            self.current = self.undo_stack[-1]
            del self.undo_stack[-1]

    def redo(self):
        """ Undo most recent undo """
        if self.redo_stack:
            self.undo_stack.append(self.current)
            self.current = self.redo_stack[-1]
            del self.redo_stack[-1]

    def checkpoint(self):
        """ Record a checkpoint """
        self.undo_stack.append(self.current.copy())
        del self.redo_stack[:]

def standard_graph(parent_state=None):
    gsig = parent_state.domain.sig if parent_state else sig
    nodes = [(str(s),[],s) for name,s in gsig.sorts.iteritems() if isinstance(s,UninterpretedSort)]

    g = Graph(nodes,parent_state)

    if hasattr(parent_state,'universe'):
        print "parent_state.universe: {}".format(parent_state.universe)
        for n in g.all_nodes:
            if n.sort in parent_state.universe:
                g.splatter(n,parent_state.universe[n.sort])
    return GraphStack(g)
    


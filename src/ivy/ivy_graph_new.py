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
from collections import defaultdict, OrderedDict

import ivy_logic as il
import concept as co
import concept_interactive_session as cis
from dot_layout import dot_layout
from cy_elements import CyElements

def cube_to_z3(cube):
    if len(cube) == 0:
        return z3.BoolVal(True)
    fmla = z3.And([literal_to_z3(lit) for lit in cube])
    return fmla

def s_add(s,f):
#    print "add: {}".format(f)
    s.add(f)

def s_check_fmla(s,fmla):
    s.push()
    f = z3.Not(formula_to_z3(fmla))
    s_add(s,f)
    cr = s.check()
    s.pop()
    return cr

def s_check_cube_p(s,polarity,cube,assump = None):
    s.push()
    if assump is not None:
        s_add(s,formula_to_z3(assump))
    f = cube_to_z3(cube)
    if polarity == 0:
        f = z3.Not(f)
    s_add(s,f)
    cr = s.check()
#    print "cr: {}".format(cr)
    s.pop()
    return cr

def s_check_cube(s,cube,assump = None):
    if s_check_cube_p(s,1,cube) == z3.unsat:
        res = "false"
    elif s_check_cube_p(s,0,cube,assump) == z3.unsat:
        res = "true"
    else:
        res = "undef"
    return res

def make_lit_label(lit):
    # pred = lit.atom.relname
    # if pred != "=":
    #     label = pred
    # else:
    #     terms = lit.atom.args
    #     arg = 1 if isinstance(terms[0],Variable) else 0
    #     label = "=" + lit.atom.args[arg].rep
    for v in used_variables_ast(lit):
        return str(substitute_lit(lit,{v.rep:Variable('',v.sort)})).replace(' ','').replace('()','')
    label = str(lit.atom)
    return label if lit.polarity == 1 else "~" + label

class GraphNode(object):
    def __init__(self,name,fmla,sort):
#        print "GraphNode: name: {}".format(name)
#        print "GraphNode: type(name): {}".format(type(name))
        self.name = name
        self.fmla = fmla
        self.sort = sort
    def copy(self):
        c = GraphNode(self.name,self.fmla,self.sort)
        c.__dict__ = self.__dict__.copy() 
        return c
    def text_name(self):
        return '___' + self.name
    def variable(self,name):
        return Variable(name,self.sort)
    def to_concept_space(self):
        return Atom(self.text_name(),[self.variable('X')]), ProductSpace([NamedSpace(x) for x in self.fmla])
    def extra_concepts(self):
        tn = self.text_name()
        X,Y = self.variable('X'),self.variable('Y')
        c = [Literal(1,Atom(tn,[X])),~eq_lit(X,Y),Literal(1,Atom(tn,[Y]))]
        cs = [ProductSpace([NamedSpace(x) for x in c])]
        w = get_witness(self)
        if w:
            cls = [[~lit,eq_lit(X,w)] for lit in self.fmla]
            cs += [ProductSpace([NamedSpace(x) for x in c]) for c in cls]
        return cs

def definite_node(n):
    if n.status != true:
        return None
    return get_witness(n)

def rela_fact(polarity,relname,n1,n2):
    return ([~lit for lit in fmla1]
            + [~lit for lit in substitute_clause(n2.fmla,{'X':Variable('Y',n2.sort)})]
            + [Literal(polarity,Atom(relname,[Variable('X',n1.sort),Variable('Y',n2.sort)]))])

def str_of_edge(e):
    return e[0][0].name + '|' + e[0][1].name + '|' + e[1]

class GraphRelation(object):
    def __init__(self,parent,rel_lit):
        self.parent = parent
        self.rel_lit = rel_lit
        params = dict((v.name,v) for v in used_variables_ast(rel_lit.atom))
#        self.sorts = [a.get_sort() for a in rel_lit.atom.args]
        self.sorts = [params['X'].sort,params['Y'].sort]
#        print "GraphRelation: rel = {}, sorts = {}".format(rel_lit,self.sorts)
        self.properties = {'transitive':False,'reflexive':False}
    def arity(self):
        return 2
    @property
    def sort(self):
        return RelationSort(self.sorts)
    def copy(self,new_parent):
        r = type(self)(new_parent,self.rel_lit)
        r.edges = self.edges # these are immutable I hope
        if hasattr(self,'solver'):
            r.solver = self.solver
        r.properties = self.properties.copy()
        return r
    def compute_edges(self,solver):
        self.edges = None # compute them lazily
# don't save solver, use parent's
#        self.solver = solver
    def really_compute_edges(self,solver):
        self.edges = []
        self.parent.enable_relation(self)
        for n1 in self.parent.nodes:
            if n1.sort == self.sorts[0]:
                for n2 in self.parent.nodes:
                    if n2.sort == self.sorts[1]:
                        status = self.check_edge(n1.fmla,n2.fmla,solver)
                        self.edges.append(((n1,n2),status))
#        self.solver = None #once edges are computed, we don't need solver
    def get_edges(self):
        if self.edges == None:
            self.really_compute_edges(self.parent.solver)
        edges = self.edges
        if self.properties['reflexive']:
            edges = [((x,y),status) for (x,y),status in edges if x is not y]
        if self.properties['transitive']:
            idx = defaultdict(list)
            for e in edges:
                idx[e[0][0].name].append(e)
            d = set()
            for ((n1,n2),s1) in edges:
                if s1 == 'true':
                    for (n3,n4),s2 in idx[n2.name]:
                        if s2 == 'true':
                            d.add(str_of_edge(((n1,n4),'true')))
            edges = [e for e in edges if str_of_edge(e) not in d]
        return edges
    # TODO: this seems to be unused -- remove?
    def get_facts(self,names,tvals):
        edges = self.get_edges()
        return [rela_fact(1 if status =='true' else 0,self.name(),p1,p2)
                for (p1,p2),status in edges
                if status != 'undef' and status in tvals and p1.name in names and p2.name in names]
    # here, we trust that all the named states are definite
    def get_definite_facts(self,names,tvals):
        edges = self.get_edges()
        return [[substitute_lit(Literal(1 if status =='true' else 0,self.rel_lit.atom),
                               {'X':get_witness(p1),'Y':get_witness(p2)})]
                for (p1,p2),status in edges
                if status != 'undef' and status in tvals and p1.name in names and p2.name in names]
    def check_edge(self,f1,f2,solver):
        x = var_to_skolem('__',Variable('X',self.sorts[0])).suffix(str(self.sorts[0]))
        y = var_to_skolem('__',Variable('Y',self.sorts[1])).suffix(str(self.sorts[1]))
        solver.push()
        s_add(solver,cube_to_z3(substitute_clause(f1,{'X':x})))
        s_add(solver,cube_to_z3(substitute_clause(f2,{'X':y})))
#        print "xsort: {}, ysort: {}".format(x.get_sort(),y.get_sort())
#        print "rel_lit: {}, subs: {}".format(self.rel_lit,substitute_lit(self.rel_lit,{'X':x,'Y':y}))
        res = s_check_cube(solver,[substitute_lit(self.rel_lit,{'X':x,'Y':y})])
        solver.pop()
        return res
    @property
    def id(self):
        return il.to_str_with_var_sorts(self.rel_lit.atom)
    def name(self):
        return str(self.rel_lit.atom)
    def to_concept_space(self):
        rel_lit = self.rel_lit
        return Atom('__' + rel_lit.atom.rep,rel_lit.atom.args),SumSpace([NamedSpace(rel_lit),NamedSpace(~rel_lit)])

class GraphRelationUnary(GraphRelation):
    def __init__(self,parent,rel_lit):
        self.parent = parent
        self.rel_lit = rel_lit
        params = dict((v.name,v) for v in used_variables_ast(rel_lit.atom))
#        self.sorts = [a.get_sort() for a in rel_lit.atom.args]
        self.sorts = [params['X'].sort]
#        print "GraphRelation: rel = {}, sorts = {}".format(rel_lit,self.sorts)
        self.properties = {'transitive':False,'reflexive':False}
    def arity(self):
        return 1
    def really_compute_edges(self,solver):
        self.edges = []
        self.parent.enable_relation(self)
        for n1 in self.parent.nodes:
            if n1.sort == self.sorts[0]:
                status = self.check_edge(n1.fmla,solver)
                self.edges.append(((n1,),status))
#        self.solver = None #once edges are computed, we don't need solver
    def get_edges(self):
        if self.edges == None:
            self.really_compute_edges(self.parent.solver)
        return self.edges
    # TODO: this seems to be unused -- remove?
    def get_facts(self,names,tvals):
        edges = self.get_edges()
        return [rela_fact(1 if status =='true' else 0,self.name(),p1)
                for (p1,),status in edges
                if status != 'undef' and status in tvals and p1.name in names]
    # here, we trust that all the named states are definite
    def get_definite_facts(self,names,tvals):
        edges = self.get_edges()
        return [[substitute_lit(Literal(1 if status =='true' else 0,self.rel_lit.atom),
                               {'X':get_witness(p1)})]
                for (p1,),status in edges
                if status != 'undef' and status in tvals and p1.name in names]
    def check_edge(self,f1,solver):
        x = var_to_skolem('__',Variable('X',self.sorts[0])).suffix(str(self.sorts[0]))
        solver.push()
        s_add(solver,cube_to_z3(substitute_clause(f1,{'X':x})))
        #  print "xsort: {}, ysort: {}".format(x.get_sort(),y.get_sort())
#        print "rel_lit: {}, subs: {}".format(self.rel_lit,substitute_lit(self.rel_lit,{'X':x,'Y':y}))
        res = s_check_cube(solver,[substitute_lit(self.rel_lit,{'X':x})])
        solver.pop()
        return res

class GraphFunctionUnary(GraphRelationUnary):
    def __init__(self,parent,rel_lit):
#        print "GraphFunctionUnary: {} : {}".format(rel_lit,type(rel_lit))
        self.parent = parent
        fmla = rel_lit.atom
        self.fmla = fmla
        self.rel_lit = rel_lit # this is fake
        params = dict((v.name,v) for v in used_variables_ast(fmla))
#        self.sorts = [a.get_sort() for a in rel_lit.atom.args]
        self.sorts = [params['X'].sort]
#        print "GraphRelation: rel = {}, sorts = {}".format(rel_lit,self.sorts)
        self.properties = {'transitive':False,'reflexive':False}
    def status_lit(self,status):
        return Literal(1,Atom(equals,[self.fmla,status]))
    def test_lit(self,param,status):
        return substitute_lit(self.status_lit(status),{'X':param})
    def get_definite_facts(self,names,tvals):
        edges = self.get_edges()
        return [[self.test_lit(get_witness(p1),status)]
                for (p1,),status in edges
                if status != 'undef' and p1.name in names]
    def check_edge(self,f1,solver):
        x = var_to_skolem('__',Variable('X',self.sorts[0])).suffix(str(self.sorts[0]))
        solver.push()
        s_add(solver,cube_to_z3(substitute_clause(f1,{'X':x})))
        #  print "xsort: {}, ysort: {}".format(x.get_sort(),y.get_sort())
#        print "rel_lit: {}, subs: {}".format(self.rel_lit,substitute_lit(self.rel_lit,{'X':x,'Y':y}))
        f = self.fmla
        vals = [Constant(Symbol(y,f.sort.rng)) for y in f.sort.rng.defines()]
        status = 'undef'
        for v in vals:
            if s_check_fmla(solver,self.test_lit(x,v).atom) == z3.unsat:
                status = v
                break
        solver.pop()
        return status

                    
def get_witness(n):
    for lit in n.fmla:
#        print "get_witness: lit = {}, iseq = {}, type(lit) = {}, type(lit.atom) = {}, lit.atom.rep = {}, lit.atom.rep == equals = {}".format(lit,is_equality_lit(lit),type(lit), type(lit.atom), lit.atom.rep, lit.atom.rep == equals)
        if is_equality_lit(lit) and isinstance(lit.atom.args[0],Variable):
            return lit.atom.args[1]
    return None

def lins(l,i,e):
    l.insert(i,e)
    return l

def get_projections_of_ternaries(wit):
#    print "witness: {}".format(wit)
    for sym in ivy_logic.all_symbols():
#        print "rel: {}. sort = {}".format(sym,sym.sort)
        if sym.is_relation() and len(sym.sort.dom) == 3:
#            print "ternary: {}, sort = {}".format(sym,sym.sort)
            for i in range(3):
                if sym.sort.dom[i] == wit.sort:
                    yield Literal(1,sym(*[t if t is wit else Variable(t,s) for t,s in zip(lins(['X','Y'],i,wit),sym.sort.dom)]))
                    

def node_concept(sort,varname):
    return Literal(1,Atom('__node:' + sort,[Variable(varname,sort)])) 

def xtra_concept(sort,vn1,vn2):
    return Literal(1,Atom('__xtra:' + sort,[Variable(vn1,sort),Variable(vn2,sort)])) 

def apply_edge_rel(rel_lit,arg1,arg2):
    return substitute_lit(rel_lit,{'X':arg1,'Y':arg2})

use_ivy_alpha = False


# This creates a concept from a formula with free variables,
# using the variables in alphabetical order.

def concept_from_formula(fmla):
    vs = sorted(list(used_variables_ast(fmla)),key=str)
    return co.Concept(vs,fmla)

def concept_name(concept):
    return il.to_str_with_var_sorts(concept.formula)

def add_domain_concept(concepts,fmla,name=None,kind=None):
    con = concept_from_formula(fmla)
    arity = con.arity
    name = '.' + (name or concept_name(con))
    if 1 <= arity and arity <= 2:
        kind = kind or ('node_labels' if arity==1 else 'edges')
        concepts[name] = con
        concepts[kind].append(name)
    return name    

def empty_concepts():
    concepts = OrderedDict()
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
        add_domain_concept(concepts,Equals(X,X),name=sort.name,kind='nodes')
        
    # add equality concept
    if False:
        X = Variable('X', TopSort())
        Y = Variable('Y', TopSort())
        concepts['='] = co.Concept([X, Y], Equals(X, Y))

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

    print "concepts: {}".format(concepts)

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
            if label_name.startswith('='):
                disp = _label_prefix_equality[k] + label_name[1:]
            else:
                disp = _label_prefix[k] + label_name
            label_lines.append(disp)

        disp = node
        if '+' in disp or '-' in disp:
            # for concepts that are the result of splits, display just the sort
            disp = str(domain.concepts[node].sorts[0])
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

        print "getting edge: {} {}".format(edge,classes[0])
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
    def __init__(self):
        # dict mapping edge names to widget tuples
        self.edge_display_checkboxes = defaultdict(
            lambda: dict((x, Option()) for x in _edge_display_checkboxes)
        )
        # dict mapping label names to widget tuples
        self.node_label_display_checkboxes = defaultdict(
            lambda: dict((x, Option()) for x in _node_label_display_checkboxes)
        )
        self.ignore_display_checkbox_change = False
        
        # TODO: temporary since cy_render needs

        self.remove_concept = None
        self.suppose_empty = None
        self.materialize_node = None
        self.add_projection = None

    def set_checkbox(self,obj,idx,val):
        obj = '.' + obj  # get name in graph
        # HACK: can't tell if it's edge or node_label so set both
        val = Option(val)
        if idx < len(_edge_display_checkboxes):
            print "setting edge: {} {}".format(obj,_edge_display_checkboxes[idx])
            self.edge_display_checkboxes[obj][_edge_display_checkboxes[idx]] = val
        if idx < len(_node_label_display_checkboxes):
            self.node_label_display_checkboxes[obj][_node_label_display_checkboxes[idx]] = val

    def get_transitive_reduction(self):
        return [] # TODO: implement

    def render(self):
        print "rendering..."
        self.cy_elements = dot_layout(render_concept_graph(self))
        print self.cy_elements.elements
        
    def projection(self,concept_name,concept_class):
        print 'thing: {} {}'.format(concept_name,concept_class)
        if concept_class == 'node_labels':
            return concept_name in set(['.s(X:server)'])
        return True

class Graph(object):
    def __init__(self,nodes,parent_state=None):
        self.constraints = true_clauses()
        self.parent_state = parent_state
        self.concept_domain = initial_concept_domain([s for n,f,s in nodes])
        self.widget = ConceptStateViewWidget()
        self.session = cis.ConceptInteractiveSession(self.concept_domain,And(),And(),widget=self.widget)

    @property
    def sort_ids(self):
        return ['.' + s for s in sig.sorts]  # for now, display all declared sorts

    @property
    def relation_ids(self):
        """ Return ids of all the concepts that need check-boxes """
        return self.concept_domain.concepts['edges'] + self.concept_domain.concepts['node_labels']

    def concept_from_id(self,id):
        """ Get a relational concept from its id """
        return self.concept_domain.concepts[id]

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

    def concept_label(self,concept):
        fmla = concept.formula
        for v in concept.variables:
            return str(substitute_ast(fmla,{v.rep:Variable('',v.sort)})).replace(' ','').replace('()','')
        return str(fmla)

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

    def add_relation(self,rela):
        self.relations.append(rela)
    def check_node(self,n):
        x = var_to_skolem('__',Variable('X',n.sort)).suffix(str(n.sort))
        y = var_to_skolem('__',Variable('Y',n.sort)).suffix(str(n.sort))
#        print "x.sort: {}",format(x.sort)
        self.solver.push()
        s = self.solver
        # if we have a witness we can show node is definite (present in all models)
        wit = get_witness(n)
#        print "checking: {}".format(n.fmla)
        cube = substitute_clause(n.fmla,{'X':x})
#        print "cube: {!r}".format(cube)
#        print wit
#        if wit != None:
##            print "wit: {}, wit.sort: {}, x.sort: {}".format(wit,wit.sort,x.sort)
        res = s_check_cube(s,cube,(Atom(equals,[x,wit]) if wit != None else None))
##        print"check cube: %s = %s" % (cube,res)
#        res = s_check_cube(s,substitute_clause(n.fmla,{'X':x}))
#        print "status: {}".format(res)
        n.status = res
        s_add(s,cube_to_z3(substitute_clause(n.fmla,{'X':x})))
        s_add(s,cube_to_z3(substitute_clause(n.fmla,{'X':y})))
        s_add(s,cube_to_z3([Literal(0,Atom(equals,[x,y]))]))
        n.summary = s.check() != z3.unsat
        self.solver.pop()
        
    def concept(c):
        """ Get the node corresponding to a concept """
        if isinstance(c,str):
            c = to_cube(c)
        
    def get_predicates(self,clauses):
#        print "get_predicates: {}".format(clauses)
        d = self.parent_state.domain
        sig = d.sig
        urs = [x for x in used_unary_relations_clauses(clauses) if not is_skolem(x)]
        cs = [x for x in used_constants_clauses(clauses)
              if not is_skolem(x) and not has_enumerated_sort(sig,x) and not x.is_numeral()]
        ufs = [x for x in used_unary_functions_clauses(clauses)
               if not is_skolem(x) and  has_enumerated_sort(sig,x)]
        nrs = [x for x,arity in d.relations.iteritems() if arity == 0]
        union_to_list(urs,[x for x,arity in d.relations.iteritems() if arity == 1])
        union_to_list(cs,[x for x,arity in d.functions.iteritems()
                          if arity == 0 and not has_enumerated_sort(sig,x)])
        union_to_list(ufs,[x for x,arity in d.functions.iteritems()
                           if arity == 1 and has_enumerated_sort(sig,x)])
#        print "ufs: {}".format(ufs)
        ccs = [Constant(c) for c in cs]
#        print "sorts: {}".format([(c,c.get_sort()) for c in ccs])
        return ([Literal(1,Atom(c,[])) for c in nrs] +
                [Literal(1,Atom(equals,[Variable("X",c.get_sort()),c])) for c in ccs] +
                [Literal(1,Atom(r,[Variable("X",r.sort.dom[0])])) for r in urs] +
                [(App(f,Variable('X',f.sort.dom[0])),[Constant(Symbol(x,f.sort.rng)) for x in f.sort.rng.defines()]) for f in ufs])

    def make_rel_lit(self,rel,varnames):
        args = [Variable(v,t) for v,t in zip(varnames,rel.sort.dom)]
        return Literal(1,Atom(rel,args))

    def set_state(self,clauses,recomp=True):
        self.state = clauses

        # Create a new concept domain using the vocabulary of the state

        vocab = set(list(all_symbols()) + list(used_symbols_clauses(clauses)))
        self.concept_domain = replace_concept_domain_vocabulary(self.session.domain,vocab)
        state = clauses_to_formula(clauses)
        self.session = cis.ConceptInteractiveSession(self.concept_domain,state,And(),widget=self.widget)

        if recomp:
            self.recompute()

    def new_relation(self,lit):
        self.brels.append(lit)
        r = GraphRelation(self,lit)
        self.relations.append(r)
        r.compute_edges(self.solver)

    def set_concrete(self,clauses):
        self.concrete = clauses

    def relation_concepts(self,relations):
        rcons = [r.to_concept_space() for r in relations]
        rprods = [ProductSpace([NamedSpace(x) for x in [node_concept(r.sorts[0],'X'),Literal(1,cs[0]),node_concept(r.sorts[1],'Y')]]) for (r,cs) in zip(relations,rcons)]
        rsp = to_atom('__rsp(X,Y)'), SumSpace(rprods)
        return rcons + [rsp]

    def compile_concepts(self,concepts):
        clauses = self.post.post_step(concepts)
#        print "compile_concepts clauses={}".format(clauses)
        vs = used_variables_in_order_clauses(clauses)
        sksubs = dict((v.rep,var_to_skolem('__',Variable(v.rep,v.sort))) for v in vs)
        clauses = substitute_clauses(clauses,sksubs)
#        print "clauses: {}".format(clauses)
        return clauses

    def enable_relation(self,relation):
        if relation.name() in self.enabled_relations:
            return
        self.enabled_relations.add(relation.name())
        if use_ivy_alpha:
            concepts = self.relation_concepts([relation])
#    #        print concepts
            self.post.concept_spaces += concepts
            clauses = self.compile_concepts(concepts)
#    #        print clauses
            s_add(self.solver,clauses_to_z3(clauses))
            self.solver_clauses = and_clauses(self.solver.clauses,clauses)

    def get_solver_clauses(self):
#        expr = self.state_as_z3_expr
        if use_ivy_alpha:
            d = ProgressiveDomain(verbose=True)
            self.post = d
            sorts = sorted(set(n.sort for n in self.all_nodes))
            concepts = []
            for s in sorts:
                nconcepts = [n.to_concept_space() for n in self.all_nodes]
                nconcepts.append((node_concept(s,'X').atom, SumSpace([NamedSpace(Literal(1,x)) for x,y in nconcepts])))
                nconcepts.append((xtra_concept(s,'X','Y').atom,SumSpace([x for n in self.all_nodes for x in n.extra_concepts()])))
                concepts += nconcepts
            concepts = concepts + self.relation_concepts([r for r in self.relations if r.name() in self.enabled_relations])
            d.concept_spaces = concepts
#    #        print "concepts: %s" % concepts
            d.post_init(self.state,[],{},[])
            clauses = self.compile_concepts(concepts)
#    #        print "clauses: %s" % clauses
        else:
            clauses = self.state
#        print "graph solver clauses = {}".format(clauses)
        s_add(self.solver,clauses_to_z3(clauses))
        self.solver_clauses = and_clauses(self.solver_clauses,clauses)

    def recompute(self):
        self.session.recompute()

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

    def copy(self):
        c = Graph([])
        c.all_nodes = [n.copy() for n in self.all_nodes] #deep copy cause we mutate this
        c.nodes = list(self.nodes)
        c.edges = list(self.edges)
        c.relations = [rel.copy(c) for rel in self.relations]
        c.enabled_relations = set(self.enabled_relations)
        c.state = self.state.copy()
        c.solver_clauses = self.solver_clauses.copy()
        s_add(c.solver,clauses_to_z3(self.solver_clauses))
        c.concrete = self.concrete # this should be immutable so don't copy
        c.predicates = list(self.predicates)
        c.pred = self # remember we are the predcessor of the new graph
        c.parent_state = self.parent_state
        c.constraints = self.constraints.copy()
        c.attributes = []
        if hasattr(self,'brels'):
            c.brels = list(self.brels)
        if hasattr(self,'reverse_result'):
            c.reverse_result = list(self.reverse_result)
#        print "self.constraints = {}".format(self.constraints)
#        print "c.constraints = {}".format(c.constraints)
        return c

    def state_implies_fmla(self,fmla):
        s = self.solver
        res = s_check_fmla(s,fmla)
        return res == z3.unsat

    def node(self,name):
        return next(n for n in self.all_nodes if n.name == name)

    def split_n_way(self,node,ps):
#        print "split_n_way, ps = {}".format([str(p) for p in ps])
        self.all_nodes = [n for n in self.all_nodes if n is not node]
        for p in ps:
            label = make_lit_label(p)
            posname = node.name + "+" + label
            self.all_nodes.append(GraphNode(posname, node.fmla + [p],node.sort))
        self.needs_recompute = True

    def split(self,node,p):
        if isinstance(p,tuple):
            self.split_n_way(node,[eq_lit(p[0],x) for x in p[1]])
            return
        label = make_lit_label(p)
        posname = node.name + "+" + label
        negname = node.name + "-" + label
        self.all_nodes = [n for n in self.all_nodes if n is not node]
        self.all_nodes.append(GraphNode(posname, node.fmla + [p],node.sort))
        neg_p = Literal(1-p.polarity,p.atom)
        self.all_nodes.append(GraphNode(negname, node.fmla + [neg_p],node.sort))
        self.needs_recompute = True

    def splatter(self,node,constants = None):
        if constants == None:
            constants = used_constants_clauses(self.constraints)
        eqs = [eq_lit(node.variable('X'),Constant(c)) for c in constants if c.sort == node.sort]
#        print "splatter eqs = {}".format(eqs)
        self.split_n_way(node,eqs)

    def add_constraints(self,cnstrs,recompute=True):
        g = self
        fc = [c for c in cnstrs if not g.state_implies_fmla(clause_to_formula(c))]
#        print "fc: %s" % fc
        if fc:
            g.set_state(and_clauses(g.state,Clauses(fc)),recompute)
            g.constraints = and_clauses(g.constraints,Clauses(cnstrs))
#        print "g.constraints: %s" % g.constraints

    def empty(self,node):
        g = self
        fmla = [~lit for lit in node.fmla]
##        print "adding clause: %s" % fmla
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
    


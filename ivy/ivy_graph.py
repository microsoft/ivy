#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
#TODO: get z3 references out of this file
#TODO: the import *'s are creating conflicts

from ivy_logic import Variable,EnumeratedSort,UninterpretedSort,all_symbols,Equals,And
import ivy_logic as il
import  ivy_logic_utils as ilu
import functools
from collections import defaultdict
import concept as co
import concept_interactive_session as cis
from dot_layout import dot_layout
from cy_elements import CyElements
import ivy_utils as iu
from copy import deepcopy

# This creates a concept from a formula with free variables, using the
# variables in alphabetical order.  A canonical concept name is
# generated from the formula.

def concept_from_formula(fmla,vs = None):
    if vs is None:
        vs = sorted(list(ilu.used_variables_ast(fmla)),key=str)
    name = (','.join(str(v) + ':' + str(v.sort) for v in vs)
            + '.' + str(fmla))
    return co.Concept(name,vs,fmla)

def add_domain_concept(concepts,con,kind=None):
    arity = con.arity
    name = con.name
    concepts[name] = con
    if kind or (1 <= arity and arity <= 2):
        kind = kind or ('node_labels' if arity==1 else 'edges')
        concepts[kind].append(name)
 
def add_domain_concept_fmla(concepts,fmla,kind=None,vs=None):
    con = concept_from_formula(fmla,vs)
    add_domain_concept(concepts,con,kind)
    return con

def empty_concepts():
    concepts = co.ConceptDict()
    concepts['nodes'] = []
    concepts['node_labels'] = []
    concepts['edges'] = []
    concepts['enum'] = []
    concepts['enum_case'] = []
    return concepts

def make_concept_domain(concepts):
    combinations = co.get_standard_combinations() + [('enum','node_necessarily','nodes','enum')]
    return co.ConceptDomain(concepts, co.get_standard_combiners(), combinations)
    
# This creates the default initial concept graph, with one
# node for each sort.

def initial_concept_domain(sorts):

    concepts = empty_concepts()

    # add one node for each sort
    for sort in sorts:
        X = Variable('X', sort)
        add_domain_concept_fmla(concepts,Equals(X,X),kind='nodes')
        
    return make_concept_domain(concepts)

# This is a concept set for t erm of enumerated type. 

class enum_concepts(co.ConceptSet,list):
    def __init__(self,name,variables,formula):
        list.__init__(self)
        self.name = name
        self.variables = variables
        self.formula = formula
        self.sorts = [v.sort for v in variables] if variables != None else []

# This creates concepts and concept sets from the signature. 

def create_unit_sort(concepts):
    sort = il.UninterpretedSort('unit')
    if 'unit' not in il.sig.sorts:
        il.sig.sorts['unit'] = sort
    if 'has_unit' not in concepts:  # HACK: will this damage anything?
        X = Variable('X', sort)
        add_domain_concept_fmla(concepts,Equals(X,X),kind='nodes')
        concepts['has_unit'] = []

    return il.sig.sorts['unit']

def concepts_from_sig(symbols,concepts):

    for c in sorted(symbols,key=str):

        dom,rng = c.sort.dom,c.sort.rng

        if il.is_enumerated_sort(rng):
            if len(dom) in [0,1,2]:
                if len(dom) == 0:
                    if c in il.sig.constructors:
                        continue
                    # Hack: we treat enumerated constants as labels on the bogus sort "unit"
                    vs,xvs = [],[Variable('X',create_unit_sort(concepts))]
                else:
                    vs,xvs = [Variable(n,s) for n,s in zip(['X','Y'],dom)],None
                ec = concept_from_formula(c(*vs),vs=xvs)
                concepts['enum'].append(ec.name)
                concepts[ec.name] = enum_concepts(ec.name,vs,c(*vs))
                for cons in rng.constructors:
                    c1 = add_domain_concept_fmla(concepts,Equals(c(*vs),cons),kind='enum_case',vs=xvs)
                    concepts[ec.name].append(c1.name)                

        elif il.is_boolean_sort(rng):
            # TODO: we have no way to display boolean constants
            if len(dom) in [0,1,2,3]:
                if len(dom) == 0:
                    if c in il.sig.constructors:
                        continue
                    # Hack: we treat boolean constants as labels on the bogus sort "unit"
                    vs,xvs = [],[Variable('X',create_unit_sort(concepts))]
                else:
                    vs,xvs = [Variable(n,s) for n,s in zip(['X','Y','Z'],dom)],None
                add_domain_concept_fmla(concepts,c(*vs),vs=xvs)

        elif il.is_first_order_sort(rng):
            if len(dom) == 0:
                add_domain_concept_fmla(concepts,Equals(Variable('X', rng),c))
            elif len(dom) in [1,2]:
                vs = [Variable(n,s) for n,s in zip(['X','Y','Z'],dom+(rng,))]
                fmla = Equals(c(*vs[0:-1]),vs[-1])
                add_domain_concept_fmla(concepts,fmla)
    
# replace the signature concepts in a concept domain

def replace_concept_domain_vocabulary(concept_domain,symbols):

    concepts = empty_concepts()

    # keep all the old nodes

    old_concepts = concept_domain.concepts
    for node in old_concepts['nodes']:
        concepts['nodes'].append(node)
        concepts[node] = old_concepts[node]

    # add concepts from the signature

    concepts_from_sig(symbols,concepts)

    return make_concept_domain(concepts)

def witness_concept(c):
    return concept_from_formula(Equals(Variable('X', c.sort),c))


# These define the checkbox controls
# TODO: these should be exported to the UI

_edge_display_classes = ['all_to_all', 'edge_unknown', 'none_to_none']
_edge_display_checkboxes = _edge_display_classes + ['transitive']
_node_label_display_checkboxes = ['node_necessarily', 'node_maybe', 'node_necessarily_not']

class Option(object):
    def __init__(self,val=False):
        self.val = True if val else False
    @property
    def value(self):
        return self.val

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
            lab = widget.concept_label(domain.concepts[label_name])
            if k == 'node_maybe':
                lab += '?'
            elif k == 'node_necessarily_not':
                lab = '~' + lab
            label_lines.append(lab)

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
        
        cluster = domain.concepts[node].sort.name


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

        transitive = widget.edge_display_checkboxes[edge]['transitive'].value

        g.add_edge(
            edge,
            source,
            target,
            label=edge,
            classes=classes,
            short_info='\n'.join(labels),
            long_info=[str(domain.concepts[edge])] + labels[1:],
            events=[],
            transitive = transitive,
        )

    return g

def node_gt(n1,n2):
    return n1 > n2

# In concept labels, we drop the variable X from formulas
# of the form p(X), X=e and f(X)=e where e is ground.

def can_abbreviate_formula(v,fmla):
    return (len(fmla.args) == 1 and fmla.args[0] == v or
            il.is_eq(fmla)
            and (fmla.args[0] == v or 
                 len(fmla.args[0].args) ==1 and fmla.args[0].args[0] == v)
            and not any(ilu.variables_ast(fmla.args[1])))

# Return true if concept is of the form X=n where n is a numeral

def is_numeral_concept(c):
    return (len(c.variables) == 1 and il.is_eq(c.formula) and isinstance(c.formula.args[0],il.Variable) and
            il.is_numeral(c.formula.args[1]))


class Graph(object):
    def __init__(self,sorts,parent_state=None):
        self.parent_state = parent_state
        self.sorts = sorts

        # dict mapping edge names to widget tuples
        self.edge_display_checkboxes = defaultdict(
            lambda: dict((x, Option()) for x in _edge_display_checkboxes)
        )
        # dict mapping label names to widget tuples
        self.node_label_display_checkboxes = defaultdict(
            lambda: dict((x, Option()) for x in _node_label_display_checkboxes)
        )

        self.reset()
        render_concept_graph(self)

    def reset(self):
        
        concept_domain = initial_concept_domain(self.sorts)
        self.new_relations = []
        self.concept_session = cis.ConceptInteractiveSession(concept_domain,And(),And(),cache={},recompute=True)

        if hasattr(self.parent_state,'universe'):
            for n in self.nodes:
                if n.sort in self.parent_state.universe:
                    self.splatter(n,self.parent_state.universe[n.sort])


    @property
    def constraints(self):
        return ilu.Clauses(self.concept_session.suppose_constraints)


    @property
    def concept_domain(self):
        return self.concept_session.domain

    def sorts(self):
        return ivy_logic.sig.sorts  # for now, display all declared sorts

    @property
    def sort_names(self):
        return sorted(list(il.sig.sorts))  # for now, display all declared sorts

    @property
    def relation_ids(self):
        """ Return ids of all the concepts that need check-boxes """
        concepts = self.concept_domain.concepts
        nls = [n for n in concepts['node_labels'] if not is_numeral_concept(concepts[n])]
        rels = concepts['edges'] + nls + concepts['enum']
        return sorted(rels,key=lambda r: self.concept_label(self.concept_from_id(r)))

    @property
    def default_labels(self):
        """ Return ids of all the concepts that are shown by default """
        concepts = self.concept_domain.concepts
        return [n for n in concepts['node_labels'] if is_numeral_concept(concepts[n])]

    def concept_from_id(self,id):
        """ Get a relational concept from its id """
        return self.concept_domain.concepts[id]

    def id_from_concept(self,concept):
        """ Get a relational concept from its id """
        return concept.name

    def edge_cy_id(self,edge):
        """Get the cy_elements id of an edge """
        return self.cy_elements.edge_id[tuple(self.id_from_concept(c) for c in edge)]

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
        if len(concept.variables) == 1:
            v = concept.variables[0]
            if can_abbreviate_formula(v,fmla):
                res = il.fmla_to_str_ambiguous(ilu.substitute_ast(fmla,{v.rep:Variable('',v.sort)}))
                return res.replace(' ','').replace('()','')
        return str(fmla)

    # This gives the top label of a node based on its concept

    def node_label(self,concept):
        return str(concept.sorts[0])

    # Get the projections of ternary relations using the witnesses of
    # a node.

    def find_node_with_labels(self,labels):
        for elem in self.cy_elements.elements:
            if elem['group'] == 'nodes':
                nlabs = set(elem['data']['label'].split('\n'))
                if all((l in nlabs or l.startswith('!') and l[1:] not in nlabs) for l in labels):
                    return self.concept_domain.concepts[elem['data']['obj']]

    # find a relation with the given label

    def find_relation_with_label(self,label):
        for rel in self.relations:
            if self.concept_label(rel) == label:
                return rel

    def get_projections(self,node):
        return self.concept_session.get_projections(node.name)

    # Parse a string into a concept

    def string_to_concept(self,text):
        # set up the signature with symbols in graph so
        # we can parse the formula.
        sig = il.sig.copy()
        with sig:
            for c in ilu.used_constants_clauses(self.state):
                if not isinstance(c.sort,il.EnumeratedSort) and not c.is_numeral():
                    il.add_symbol(str(c),c.sort)
            for c in ilu.used_constants_clauses(self.constraints) and not c.is_numeral():
                if not isinstance(c.sort,il.EnumeratedSort):
                    il.add_symbol(str(c),c.sort)
            return concept_from_formula(ilu.to_formula(text))

    def formula_to_concept(self,fmla):
        return concept_from_formula(fmla)

    def new_relation(self,concept):
        if concept.name not in self.concept_domain.concepts:
            add_domain_concept(self.concept_domain.concepts,concept)
            self.new_relations.append(concept)
            
    def state_changed(self,recomp=True):
        cs = self.concept_session
        cs.cache.clear()
        vocab = list(ilu.used_symbols_asts([c.formula for c in self.nodes]))
        fsyms = list(s for s in ilu.used_symbols_ast(cs._to_formula()) if not s.is_skolem())
        vocab += list(all_symbols()) + fsyms
        vocab = [il.normalize_symbol(s) for s in vocab]
        cs.domain = replace_concept_domain_vocabulary(cs.domain,set(vocab))
        for concept in self.new_relations:
            add_domain_concept(self.concept_domain.concepts,concept)
        if recomp:
            self.recompute()
            

    def set_state(self,clauses,recomp=True,clear_constraints=False,reset=False):
        self.state = clauses        
        
        if clear_constraints:
            self.concept_session.suppose_constraints = []
        if reset:
            self.reset()
        self.concept_session.state = ilu.clauses_to_formula(clauses)
        self.state_changed(recomp)

    def set_concrete(self,clauses):
        self.concrete = clauses

    def recompute(self):
        self.concept_session.recompute(self.projection)
        self.cy_elements = dot_layout(render_concept_graph(self),subgraph_boxes=True,node_gt = node_gt)

    def get_facts(self,rels,definite=True):
        facts = self.concept_session.get_facts(self.projection)
        self.concept_session.suppose_constraints = facts

    def set_facts(self,facts):
        self.concept_session.suppose_constraints = facts

    def set_checkbox(self,obj,idx,val):

        # if object is a concept set, set boxes for all elements

        concept = self.concept_domain.concepts[obj]
        if isinstance(concept,co.ConceptSet):
            for sobj in concept:
                self.set_checkbox(sobj,idx,val)
#            return

        # HACK: can't tell if it's edge or node_label so set both
        val = Option(val)
        if idx < len(_edge_display_checkboxes):
            self.edge_display_checkboxes[obj][_edge_display_checkboxes[idx]] = val
        if idx < len(_node_label_display_checkboxes):
            self.node_label_display_checkboxes[obj][_node_label_display_checkboxes[idx]] = val

    def get_checkbox(self,obj,idx):

        # if object is a concept set, set boxes for all elements

        concept = self.concept_domain.concepts[obj]
        if isinstance(concept,co.ConceptSet):
            for sobj in concept:
                return self.get_checkbox(sobj,idx)
            return

        # HACK: can't tell if it's edge or node_label so get from one
        if idx < len(_edge_display_checkboxes):
            return self.edge_display_checkboxes[obj][_edge_display_checkboxes[idx]].value
        if idx < len(_node_label_display_checkboxes):
            return self.node_label_display_checkboxes[obj][_node_label_display_checkboxes[idx]].value
        assert False,'graph checkbox problem'

    def show_checkboxes(self):
        def thing(n,c):
            return (str(n) + ':' + str(set(x for x,y in c.iteritems() if y.value)))
        return '\n'.join(thing(n,c) for n,c in self.edge_display_checkboxes.iteritems())

    def get_transitive_reduction(self):
        return [] # TODO: implement
        
    def projection(self,concept_name,concept_class,concept_combiner=None):
#        print "projection: {} {} {}".format(concept_name,concept_class,concept_combiner)
        if concept_class in ('node_labels','edges','enum'):
            cb = self.edge_display_checkboxes if concept_class == 'edges' else self.node_label_display_checkboxes
            boxes = cb[concept_name]
            if concept_combiner is None:
                res = any(boxes[i].value for i in boxes if i != 'transitive')
            else:
                res = boxes[concept_combiner].value
            return res
        return True

    def copy(self):
        c = Graph(list(self.sorts))
        c.state = self.state.copy()
        c.cy_elements = self.cy_elements
        c.concept_session = self.concept_session.clone(recompute=False)
        c.parent_state = self.parent_state
        c.attributes = list(self.attributes)
        if hasattr(self,'reverse_result'):
            c.reverse_result = list(self.reverse_result)
        # dict mapping edge names to widget tuples
        c.edge_display_checkboxes = deepcopy(self.edge_display_checkboxes)
        c.node_label_display_checkboxes = deepcopy(self.node_label_display_checkboxes)
        return c

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
            constants = ilu.used_constants_clauses(self.constraints)
        concepts = self.concept_session.domain.concepts
        name = node.name + '.splatter'
        concepts[name] = enum_concepts(name,None,None)
        for cons in constants:
            c1 = concept_from_formula(Equals(Variable('X',node.sort),cons))
            concepts[c1.name] = c1
            concepts[name].append(c1.name)
        self.concept_session.domain.split(node.name,name)
        self.recompute()
        

    def add_constraints(self,cnstrs,recompute=True):
        self.concept_session.suppose_constraints.extend(cnstrs)
        self.state_changed(recomp=recompute)

    def empty(self,node,recompute=True):
        self.concept_session._suppose_empty(node.name)
        self.state_changed(recomp=recomp)

    def materialize(self,node,recomp=False):
        witness = self.concept_session._materialize_node(node.name)
        self.state_changed(recomp=recomp)
        return witness_concept(witness)

    def empty_edge(self,edge,recomp=False):
        self.materialize_edge(edge,false)

    def materialize_edge(self,edge,truth,recomp=False):
        rel,head,tail = edge
        witness = self.concept_session._materialize_edge(rel.name,head.name,tail.name,truth)
        self.state_changed(recomp=recomp)
        return tuple(witness_concept(w) for w in witness)

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

    def checkpoint(self,set_backtrack_point=False):
        """ Record a checkpoint """
        self.undo_stack.append(self.current.copy())
        if set_backtrack_point:
            self.undo_stack[-1].attributes.append("backtrack_point")
        del self.redo_stack[:]

def standard_graph(parent_state=None):
    sorts = [s for s in il.sig.sorts.values() if il.is_first_order_sort(s)]
    g = Graph(sorts,parent_state)
    return GraphStack(g)
    


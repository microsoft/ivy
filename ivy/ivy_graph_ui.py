#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
""" User interface component for displaying and interacting with
concept graphs """

#
# To run this you need packages python-tk, libgv-tcl and tix
#

#TODO: the import *'s are creating conflicts
import functools
import string
from ivy_graph import *
import ivy_logic
import ivy_logic_utils as lu
import ivy_interp
from ivy_utils import topological_sort
from collections import defaultdict

repr = str

class GraphWidget(object):

    # Shorthand accessor for the current concept graph:

    @property
    def g(self):
        return self.graph_stack.current

    # This defines the menus items we provide. The actual menus might be
    # tool buttons or other such things.

    def menus(self):
        return [("menu","Action",
                 [("button","Undo",self.undo),
                  ("button","Redo",self.redo),
                  ("button","Concrete",self.concrete),
                  ("button","Gather",self.gather),
                  ("button","Reverse",self.reverse),
                  ("button","Path reach",self.path_reach),
                  ("button","Reach",self.reach),
                  ("button","Conjecture",self.conjecture),
                  ("button","Backtrack",self.backtrack),
                  ("button","Recalculate",self.recalculate),
                  ("button","Diagram",self.diagram),
                  ("button","Remember",self.remember),
                  ("button","Export",self.export),
                  ]),
                ("menu","View",
                 [("button","Add relation",self.add_concept_from_string),
                  ])]


    def set_update_callback(self,update_callback):
        self.update_callback = update_callback

    # Sort a list of nodes, taking into account transitive relations
    # This has no specific semantics and is just used to make the display prettier.

    def sort_nodes(self,nodes):
        g = self.g
        order = []
        nodes_by_name = dict((x.name,x) for x in nodes)
        for r in g.relations:
            if r.arity() != 2:
                continue
            ena = self.get_enabled(r)
            if ena[0].get() and ena[3].get(): # if positive arcs enabled and transitive
                r.properties['reflexive'] = False
                r.properties['transitive'] = False
                for e in r.get_edges():
                    (x,y),status = e
                    if status == 'true':
                        order.append((nodes_by_name[x.name],nodes_by_name[y.name]))
        nodes = topological_sort(nodes,order,lambda n: n.name)
        return nodes

    # Returns a map from node names to node labels
    # TODO: parameter "nodes" seems to be ignored

    def get_node_labels(self,nodes):
        labels = defaultdict(list)
        g = self.g
        for idx,r in enumerate(g.relations):
            if r.arity() != 1:
                continue
            ena = self.get_enabled(r)
            if any(e.get() for e in ena[0:2]):  # avoid computing edges we don't need
                for (x,),status in r.get_edges():
                    if isinstance(r,GraphFunctionUnary):
                        if status == 'undef':
                            if ena[1].get():
                                labels[x.name].append(make_lit_label(r.fmla)+'=?')
                        elif ena[0].get():
                            lit = r.status_lit(status)
                            labels[x.name].append(make_lit_label(lit))
                    else: 
                        style = {'true':0,'undef':1,'false':2}[status]
                        if ena[style].get():
                            if style != 1:
                                lit = ~r.rel_lit if style==2 else r.rel_lit
                                labels[x.name].append(make_lit_label(lit))
                            else:
                                labels[x.name].append(make_lit_label(r.rel_lit) + '?')
        return labels

    # Return label for a node as a list of string

    def make_node_label(self,n):
        foo = [lit for lit in n.fmla if not(lit.polarity == 0 and lit.atom.relname == "=")] 
    #    foo = n.fmla
        return [repr(n.sort)] + [make_lit_label(lit) for lit in foo]

    # Should we group sorts into subgraphs?

    def make_subgraphs(self):
        return True

    # This returns a list of (name,action) pairs for the node menu.
    # The actions are functions of one parameter, a node. You can also
    # add a label by using action None, and a separator with label
    # '---'.

    def get_node_actions(self,node,click='left'):
        if click == 'left':
            return [
                ("Select",self.select),
                ("Empty",self.empty),
                ("Materialize",self.materialize),
                ("Materialize edge",self.materialize_from_selected),
                ("Splatter",self.splatter),
                ("Split with...",None),
                ("---",None),
                ] + self.get_node_splitting_actions(node) + self.get_node_projection_actions(node)
        else:
            return [] # nothing on right click

    # get splitting predicates for node

    def get_node_splitting_actions(self,node):
        res = []
        for p in self.g.relations:
            act = functools.partial(self.split,p)
            vs = p.variables
            node_sort = self.g.node_sort(node)
            if len(vs) == 1 and vs[0].sort == node_sort:
                res.append((self.g.concept_label(p),act))
        return res

    # add projections

    def get_node_projection_actions(self,node):
        projs = self.g.get_projections(node)
        res = []
        if len(projs) > 0:
            res.append(("Add projection...",None))
            res.append(("---",None))
            for (name,p) in projs:
                    res.append((name,lambda n,p=p: self.add_concept(p)))
        return res

    # get the edge menu actions

    def get_edge_actions(self,edge,click='left'):
        if click != 'left':
            return []
        return [
            ("Empty",self.empty_edge),
            ("Materialize",self.materialize_edge),
            ("Dematerialize",self.dematerialize_edge),
        ]

    # Look up a node in the current graph by name

    def lookup_node(self,name):
        return next(n for n in self.g.all_nodes if n.name == name)

    def checkpoint(self,set_backtrack_point=False):
        self.graph_stack.checkpoint(set_backtrack_point)
#        self.g.enabled_relations = set(x.name for x in self.visible_relations())

    def undo(self):
        self.graph_stack.undo()
        self.reverse_sync_checkboxes()
        self.update()

    def redo(self):
        self.graph_stack.redo()
        self.reverse_sync_checkboxes()
        self.update()

    # Undo to the most recent backtrack point

    def backtrack(self):
        gs = self.graph_stack
        while gs.can_undo() and "backtrack_point" not in gs.current.attributes:
            gs.undo()
        if "backtrack_point" in gs.current.attributes:
            gs.current.attributes.remove("backtrack_point")
        self.update()
        
    # make the state concrete by adding concrete state constraints

    def concrete(self):
        self.checkpoint()
        g = self.g
        g.set_state(g.state + g.concrete)
        self.update()

    # return the set of visible concepts (those represented in any way
    # in the graph)
    
    def visible_relations(self):
        return [rel for rel in self.g.relations if any(e.get() for e in self.get_enabled(rel.name))]

    # DEPRECATED: replace abstract state with visible facts

    def replace(self):
        rels = self.visible_relations()
        clauses = self.g.get_facts(rels)
        if self.parent != None and self.g.parent_state != None:
            self.parent.set_state(self.g.parent_state,clauses)

    # Get the enabled polarities for a concept

    def displayed_relation_values(self,rel):
        return [val for (val,idx) in [('true',0),('false',2)] if self.get_enabled(rel)[idx].get()]

    # Gather the definite facts in the graph into a new goal

    def gather(self):
        self.checkpoint()
        g = self.g
        rels = [(rel,self.displayed_relation_values(rel)) for rel in self.g.relations]
        self.g.get_facts(rels)
        self.update()

    def clear_elem_selection(self):
        self.node_selection = set()
        self.edge_selection = set()

    def highlight_selected_facts(self):
        self.clear_elem_selection()
        if hasattr(self,'fact_elems'):
            for fact in self.get_active_facts():
                for elem in self.fact_elems[fact]:
                    concepts = map(self.g.concept_from_id,elem)
                    if len(elem) == 1: # a node
                        self.select_node(concepts[0],True)
                    elif len(elem) == 3: # an edge
                        self.select_edge(concepts,True)

    # Set the current facts
    
    def set_facts(self,facts):
        self.checkpoint()
        self.g.set_facts(facts)
        self.update()
            
        
    # Find a current fact whose printed form is "text"

    def fact(self,text):
        for fact in self.g.constraints.conjuncts():
            if str(fact) == text:
                return fact
        raise KeyError

    # Push the goal back to the the state's predecessor, if possible.
    # If infeasible, refine the abstract domain with an interpolant.
    # Sets the current goal as a backtrack point.

    def reverse(self):
        if self.parent != None and self.g.parent_state != None:
            self.checkpoint(set_backtrack_point=True)
            g = self.g
            p = self.parent.reverse_update_concrete_clauses(g.parent_state, g.constraints)
            if p == None:
                self.ui_parent.ok_dialog("Cannot reverse.")
                return
            clauses, parent_state = p
            g.parent_state = parent_state
            g.set_state(ilu.and_clauses(parent_state.clauses,clauses),clear_constraints=True)
            print "reverse: state = {}".format(g.state)
            # This is a HACK to support "diagram"
            g.reverse_result = (parent_state.clauses,clauses)
            self.update()

    # Recalculate the current state

    def recalculate(self):
        if self.parent != None and self.g.parent_state != None:
            g = self.g
            p = self.parent.recalculate_state(g.parent_state)
            clauses = g.parent_state.clauses
#            clauses = ilu.remove_duplicates_clauses(and_clauses(g.state,clauses)) 
#            print "recalculate clauses={}".format(clauses)
            g.set_state(clauses)
            self.update()

    # Add new concept to the graph, given as a string. If not given, a
    # dialog is presented to the user.

    def add_concept_from_string(self,text=None):
        if text == None:
            msg = "Add a relation [example: p(X,a,Y)]:"
            cmd = self.add_concept_from_string
            self.ui_parent.entry_dialog(msg,command=cmd,command_label="Add")
        else:
            with self.ui_parent.run_context():  # to catch errors
                lit = self.g.string_to_concept(text)
                self.add_concept(lit)


    # Record the current goal with a string name

    def remember(self,text):
        if text == None:
            msg = "Enter a name for this goal:"
            self.ui_parent.entry_dialog(msg,command=self.remember,command_label="Remember")
        else:
            with self.ui_parent.run_context():  # to catch errors
                self.parent.remember_graph(text,self.g.copy())
                
    # Call this if relations might have changed

    def update_relations(self):
        if self.update_callback != None:
            self.update_callback()
            
        

    # Add a concept to the graph

    def add_concept(self,p):
        self.g.new_relation(p)
        self.update_relations()

    # Split a node using all available constants

    def splatter(self,node):
        self.checkpoint()
        self.g.splatter(node)
        self.update()

    # Change the parent state. Keeps the display checkboxes. If
    # "reset" is false, also keeps the concepts. If reset is true,
    # reverts to the default concepts.

    def set_parent_state(self,new_parent_state,clauses = None,reset=False):
        self.checkpoint()
        self.g.parent_state = new_parent_state
        self.g.set_state(clauses if clauses else new_parent_state.clauses, reset=reset)
        self.update_relations()
        self.update()
                         
    # Check whether the goal is reachable in one step from
    # a known-reachable state

    def reach(self):
        if self.parent != None and self.g.parent_state != None:
#            self.checkpoint()
            g = self.g
            rs = self.parent.one_step_reach(g.parent_state, g.constraints)
            if rs != None:
                clauses = rs.clauses
                msg = "Goal reached! A reachable state has been added."
                bcs = [("View state", functools.partial(self.set_state,clauses)),
                       ("OK", lambda: None)]
                self.ui_parent.buttons_dialog_cancel(msg,bcs)
            else:
                self.ui_parent.ok_dialog("Cannot reach this state in on step from any "
                                         + 'known reachable state. Try "reverse".')

    # Set the current state

    def set_state(self,clauses):
        self.checkpoint()
        self.g.set_state(clauses)
        self.update_relations()
        self.update()

    # Check reachability of the goal along the path the current state.

    def path_reach(self):
        if self.parent != None and self.g.parent_state != None:
            cnstr = self.g.constraints if not self.g.constraints.is_true() else self.g.state
            return self.parent.bmc(self.g.parent_state,cnstr)

    # Conjecture an invariant the separates known reachable states and
    # current goal. TODO: we shouldn't be computing the goal from the
    # core here.

    def conjecture(self):
        if self.parent != None and self.g.parent_state != None:
            self.checkpoint()
            g = self.g
            s = g.state if g.constraints.is_true() else g.constraints
            ri = self.parent.conjecture(g.parent_state, s)
            if ri != None:
                core,interp = ri
                dlg = Toplevel(self)
                msg = ("Based on this goal and the known reached states, " +
                       "we can conjecture the following invariant:")
                text = str(clauses_to_formula(interp))
                self.ui_parent.text_dialog(msg,text,on_cancel=None)
                goal = lu.reskolemize_clauses(core,self.g.parent_state.domain.skolemizer())
                g.constraints = goal
                g.set_state(goal)
                self.update()
            else:
                msg = ("Cannot form a conjecture based in the known reached states " +
                       "and this goal. Suggest manually materializing a goal pattern.")
                self.ui_parent.ok_dialog(msg)

    # Diagram the goal.

    def diagram(self):
        if self.parent != None and self.g.parent_state != None:
            self.checkpoint()
            g = self.g
            if hasattr(g,'reverse_result'):
                dgm = ivy_interp.diagram(self.g.parent_state,
                                         self.g.reverse_result[1],
                                         extra_axioms = self.g.reverse_result[0])
            else:
                dgm = ivy_interp.diagram(self.g.parent_state,self.g.state)
            if dgm != None:
                goal = lu.reskolemize_clauses(dgm,self.g.parent_state.domain.skolemizer())
                g.constraints = goal
                g.set_state(goal)
                self.update()
            else:
                self.ui_parent.ok_dialog("The current state is vacuous.")
        

    def split(self,p,node):
        self.checkpoint()
        self.g.split(node,p)
        self.show_node_label(p)
        self.update()

    # Select a node for a future action

    def select(self,node):
        self.show_mark(False)
        self.mark = node
        self.show_mark(True)
        
    def empty(self,node):
        self.checkpoint()
        self.g.empty(node)
        self.update()

    # Materialize a node.

    def materialize(self,node):
        self.checkpoint()
        witness = self.g.materialize(node)
        self.update_relations()
        self.show_node_label(witness)
        self.update()

    # Materialize an edge from the selected node to this one. User
    # chooses a binary concept from a list

    def materialize_from_selected(self,node):
        if hasattr(self,'mark'):
            sorts = tuple(self.g.node_sort(x) for x in [self.mark,node])
            print "sorts: {}".format(sorts)
            for r in self.g.relations:
                print "{}".format(r)
                print ": {}".format(r.sorts)
            rels = [r for r in self.g.relations if r.sorts == sorts]
            items = [self.g.concept_label(r) for r in rels]
            msg = "Materialize this relation from selected node:"
            cmd = functools.partial(self.materialize_from_selected_aux,rels,node)
            self.ui_parent.listbox_dialog(msg,items,command=cmd)
            
    def materialize_from_selected_aux(self,rels,node,idx):
        edge = (rels[idx],self.mark,node)
        self.materialize_edge(edge)

    # Negate an edge

    def empty_edge(self,edge):
        self.checkpoint()
        self.g.empty_edge(edge)
        self.update()

    # Materialize an edge

    def materialize_edge(self,edge,truth=True):
        self.checkpoint()
        witness = self.g.materialize_edge(edge,truth)
        self.update_relations()
        for w in witness:
            self.show_node_label(w)
        self.show_edge(edge[0])
        self.update()
        
    # Materialize a negative edge

    def dematerialize_edge(self,edge):
        self.materialize_edge(edge,truth=False)

    # find a node with given labels

    def node(self,*labels):
        return self.g.find_node_with_labels(labels)

    # find a relation with given label

    def relation(self,label):
        return self.g.find_relation_with_label(label)

    # tick a checkbox on a concept

    def show_relation(self,concept,boxes='+',value=True,update=True):
        for box in boxes:
            self.show_edge(concept,box,value)
        if update:
            self.update()


if __name__ == '__main__':
    nodes = [("p",to_clause("[]"))]
    state = to_clauses("[[~n(_nil,V)], [~n(V,_x)], [~n(V,_y)], [~_r_x(V),~n(V,W),_r_x(W)], [~_r_y(V),~n(V,W),_r_y(W)], [~_r_y(W),~n(_x,W)], [_r_x(W),~n(_x,W)], [_r_y(W),~n(_y,W)], [~_r_x(V),~n(_y,V)], [~_r_x(V),~_r_y(W),~n(V,W),=(W,_nil)], [~_r_x(V),~_r_y(W),~n(W,V),=(V,_nil)], [~=(_x, _nil)], [~=(_nil, _x)], [_r_x(_nil)], [~=(_x, _y)], [~=(_y, _nil)], [~_r_x(_y)], [_r_y(_nil)], [~_r_y(_x), =(_x, _nil)], [~_r_y(_x), =(_nil, _x)], [~_r_y(Xp), =(Xp, _nil), ~_r_x(Xp)], [~_r_y(Xp), =(_nil, Xp), ~_r_x(Xp)], [~=(_nil, _y)], [~_r_x(_x)], [~_r_y(_y)],[~_r_x(X),_p(X)], [~_r_y(X),_p(X)], [_p(_x)], [_p(_y)]]")
    g = Graph(nodes)
    r = GraphRelation(g,to_literal("n(X,Y)"),{"undef":"dotted","true":"solid"})
    g.add_relation(r)
    g.set_state(state)
    show_graph(g)



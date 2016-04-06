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

    # TODO: ???

    def make_subgraphs(self):
        return True

    # This returns a list of (name,action) pairs for the node menu.
    # The actions are functions of one parameter, a node. You can also
    # add a label by using action None, and a separator with label
    # '---'.

    def get_node_actions(self,node):
        return [
            ("Select",self.select),
            ("Empty",self.empty),
            ("Materialize",self.materialize),
            ("Materialize edge",self.materialize_from_selected),
            ("Splatter",self.splatter),
            ("Split with...",None),
            ("---",None),
        ] + self.get_node_splitting_actions(node) + self.get_node_projection_actions(node)

    # get splitting predicates for node

    def get_node_splitting_actions(self,node):
        res = []
        for p in self.g.predicates:
            act = functools.partial(self.split,p)
            if isinstance(p,tuple):
                res.append((make_lit_label(p[0]),act))
            else:
                vs = used_variables_ast(p)
                if not vs or next(v for v in vs).sort == self.lookup_node(node.name).sort:
                    res.append((make_lit_label(p),act))
        return res

    # add projections

    def get_node_projection_actions(self,node):
        res = []
        wit = get_witness(node)
        if wit != None:
            trs = list(get_projections_of_ternaries(wit))
            if trs != []:
                res.append(("Add projection...",None))
                for p in trs:
                    res.append((str(p),lambda p=p: self.project(p)))
        return res

    # get the edge menu actions

    def get_edge_actions(self,edge):
        return [
            ("Empty",self.empty_edge),
            ("Materialize",self.materialize_edge),
            ("Dematerialize",self.dematerialize_edge),
        ]

    def lookup_node(self,name):
        return next(n for n in self.g.all_nodes if n.name == name)

    def checkpoint(self):
        if hasattr(self,'redo_stack'):
            del self.redo_stack
        c = self.g.copy()
        # Tricky: we want this to be a side effect on self.g, since
        # this is shared with other objects. So instead of assigning
        # self.g = c, we swap the contents of the objects. This could be fixed
        # by changing copy() so that x.copy().pred = x, but carefully :-).
#        self.g.__dict__, c.__dict__ = c.__dict__, self.g.__dict__
#        self.g.pred = c
        if self.parent != None:
            self.parent.remove_state_graph(self.g)
            self.parent.add_state_graph(c)
        self.g = c
        self.g.enabled_relations = set(x.name() for x in self.visible_relations())

    def undo(self):
        if self.g.pred != None:
            if self.parent != None:
                self.parent.remove_state_graph(self.g)
                self.parent.add_state_graph(self.g.pred)
            if not hasattr(self,'redo_stack'):
                self.redo_stack = []
            self.redo_stack.append(self.g)
            self.g = self.g.pred
            self.update()

    def redo(self):
        if not hasattr(self,'redo_stack') or not self.redo_stack:
            return
        if self.parent != None:
            self.parent.remove_state_graph(self.g)
        self.g = self.redo_stack.pop()
        if self.parent != None:
            self.parent.add_state_graph(self.g)
        self.update()

    def backtrack(self):
        g = self.g
        while g.pred != None and "backtrack_point" not in g.attributes:
#            print "backing up..."
            g = g.pred
        if "backtrack_point" in g.attributes:
            g.attributes.remove("backtrack_point")
        if self.parent != None:
            self.parent.remove_state_graph(self.g)
            self.parent.add_state_graph(g)
        self.g = g
        self.update()
        
    def concrete(self):
        self.checkpoint()
        g = self.g
        # make the state concrete by adding concrete state constraints
#        print "concrete: %s" % g.concrete
        g.set_state(g.state + g.concrete)
        self.update()

    def visible_relations(self):
        return [rel for rel in self.g.relations if any(e.get() for e in self.get_enabled(rel))]

    def replace(self):
        rels = self.visible_relations()
##        print "rels: %s" % rels
        clauses = self.g.get_facts(rels)
        if self.parent != None and self.g.parent_state != None:
##            print "foo!"
            self.parent.set_state(self.g.parent_state,clauses)

    def displayed_relation_values(self,rel):
        return [val for (val,idx) in [('true',0),('false',2)] if self.get_enabled(rel)[idx].get()]

    def gather(self):
        self.checkpoint()
        g = self.g
        rels = [(rel,self.displayed_relation_values(rel)) for rel in self.g.relations]
##        print "rels: %s" % rels
        clauses = self.g.get_facts(rels)
##        print "clauses: %s" % clauses
        g.constraints = Clauses(clauses)
        self.update()

    def reverse(self):
        if self.parent != None and self.g.parent_state != None:
            self.g.attributes.append("backtrack_point")
            self.checkpoint()
            g = self.g
##            print "g.constraints: %s" % g.constraints
            p = self.parent.reverse_update_concrete_clauses(g.parent_state, g.constraints)
            if p == None:
                self.ui_parent.ok_dialog("Cannot reverse.")
                return
            clauses, parent_state = p
            g.constraints = true_clauses()
            g.parent_state = parent_state
            g.set_state(and_clauses(parent_state.clauses,clauses))
            print "reverse: state = {}".format(g.state)
            g.reverse_result = (parent_state.clauses,clauses)
            self.update()

    def recalculate(self):
        if self.parent != None and self.g.parent_state != None:
            g = self.g
            p = self.parent.recalculate_state(g.parent_state)
            clauses = g.parent_state.clauses
            clauses = remove_duplicates_clauses(and_clauses(g.state,clauses)) 
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
            self.g.new_relation(lit)
            if self.update_callback != None:
                self.update_callback()

    def remember(self,text):
        if text == None:
            msg = "Enter a name for this goal:"
            self.ui_parent.entry_dialog(msg,command=self.remember,command_label="Remember")
        else:
            with self.ui_parent.run_context():  # to catch errors
                self.parent.remember_graph(text,self.g.copy())
                
    # Add a concept to the graph

    def add_concept(self,p):
        self.g.new_relation(p)
        if self.update_callback != None:
            self.update_callback()

    # Split a node using all available constants

    def splatter(self,node):
        self.checkpoint()
        cn = self.lookup_node(node.name)
        self.g.splatter(cn)
        self.update()

    # Change the parent state, keeping concepts

    def set_parent_state(self,new_parent_state,clauses = None):
        self.checkpoint()
        self.g.parent_state = new_parent_state
        self.g.set_state(clauses if clauses else new_parent_state.clauses)
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
        self.update()

    # Check reachability of the goal along the path the current state.

    def path_reach(self):
        if self.parent != None and self.g.parent_state != None:
            cnstr = self.g.constraints if not self.g.constraints.is_true() else self.g.state
            self.parent.bmc(self.g.parent_state,cnstr)

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
        cn = self.lookup_node(node.name)
        self.g.split(cn,p)
        self.update()

    def show_mark(self,on=True):
        if hasattr(self,'mark') and self.mark in self.node_to_handle:
            for item in self.find_withtag("1"+self.node_to_handle[self.mark]):
                self.itemconfig(item,fill=('red' if on else 'white'))

    # Select a node for a future action

    def select(self,node):
        self.show_mark(False)
        self.mark = node.name
        self.show_mark(True)
        
    def empty(self,node):
        self.checkpoint()
        cn = self.lookup_node(node.name)
        self.g.empty(cn)
        self.update()

    # Materialize a node.

    def materialize(self,node):
#        if not self.lookup_node(node.name).summary:
#            return # no point in materializing singleton nodes
        self.checkpoint()
        cn = self.lookup_node(node.name)
        self.g.materialize(cn)
        self.update()

    # Materialize an edge from the selected node to this one. User
    # chooses a binary concept from a list

    def materialize_from_selected(self,node):
        if hasattr(self,'mark'):
            sorts = [self.lookup_node(x).sort for x in [self.mark,node.name]]
            required_sort = ivy_logic.RelationSort(sorts)
            rels = [r for r in self.g.relations if r.sort == required_sort]
            items = [str(r.rel_lit) for r in rels]
            msg = "Materialize this relation from selected node:"
            cmd = functools.partial(self.materialize_from_selected_aux,rels,node)
            self.ui_parent.listbox_dialog(msg,items,command=cmd)
            
    def materialize_from_selected_aux(self,rels,node,idx):
        edge = (rels[idx].rel_lit,self.mark,node.name)
        self.materialize_edge(edge)

    # Negate an edge

    def empty_edge(self,edge):
        self.checkpoint()
        rel_lit,head,tail = edge
        head,tail = self.lookup_node(head), self.lookup_node(tail)
        self.g.empty_edge(rel_lit,head,tail)
        self.update()

    # Materialize an edge

    def materialize_edge(self,edge):
        self.checkpoint()
        rel_lit,head,tail = edge
        head,tail = self.lookup_node(head), self.lookup_node(tail)
        self.g.materialize_edge(rel_lit,head,tail)
        self.update()

    # Materialize a negative edge

    def dematerialize_edge(self,edge):
        rel_lit,head,tail = edge
        edge = (Literal(0,rel_lit.atom),head,tail)
        self.materialize_edge(edge)

#        if self.update_callback != None:
#            self.update_callback()



if __name__ == '__main__':
    nodes = [("p",to_clause("[]"))]
    state = to_clauses("[[~n(_nil,V)], [~n(V,_x)], [~n(V,_y)], [~_r_x(V),~n(V,W),_r_x(W)], [~_r_y(V),~n(V,W),_r_y(W)], [~_r_y(W),~n(_x,W)], [_r_x(W),~n(_x,W)], [_r_y(W),~n(_y,W)], [~_r_x(V),~n(_y,V)], [~_r_x(V),~_r_y(W),~n(V,W),=(W,_nil)], [~_r_x(V),~_r_y(W),~n(W,V),=(V,_nil)], [~=(_x, _nil)], [~=(_nil, _x)], [_r_x(_nil)], [~=(_x, _y)], [~=(_y, _nil)], [~_r_x(_y)], [_r_y(_nil)], [~_r_y(_x), =(_x, _nil)], [~_r_y(_x), =(_nil, _x)], [~_r_y(Xp), =(Xp, _nil), ~_r_x(Xp)], [~_r_y(Xp), =(_nil, Xp), ~_r_x(Xp)], [~=(_nil, _y)], [~_r_x(_x)], [~_r_y(_y)],[~_r_x(X),_p(X)], [~_r_y(X),_p(X)], [_p(_x)], [_p(_y)]]")
    g = Graph(nodes)
    r = GraphRelation(g,to_literal("n(X,Y)"),{"undef":"dotted","true":"solid"})
    g.add_relation(r)
    g.set_state(state)
    show_graph(g)



#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
""" User interface component for displaying and interacting with
concept graphs """

#
# To run this you need packages python-tk, libgv-tcl and tix
#

#TODO: the import *'s are creating conflicts
from Tkinter import *
import Tkconstants, tkFileDialog
import Tix
import functools
import string
from ivy_graph import *
import ivy_ui_util as uu
import ivy_logic
import ivy_logic_utils as lu
import ivy_interp
from ivy_utils import topological_sort
from collections import defaultdict
from tkColorChooser import askcolor

repr = str

def make_node_label(n):
    foo = [lit for lit in n.fmla if not(lit.polarity == 0 and lit.atom.relname == "=")] 
#    foo = n.fmla
    return [repr(n.sort)] + [make_lit_label(lit) for lit in foo]

line_colors = ["black","blue","red","green","VioletRed4","brown1",
"DarkSlateGray4","navy","DeepPink4","DarkOliveGreen4","purple4","RosyBrown4",
"SkyBlue4","tomato4",'DarkSeaGreen4','DarkOrchid2','DarkOrange3',
"DeepSkyBlue4", "IndianRed1", "maroon4", "DarkOrchid3", "chocolate1",
"RoyalBlue1", "OrangeRed4", "green2", "MediumPurple4", "brown4",
]
def line_color(idx):
    return line_colors[idx % len(line_colors)]

class GraphWidget(Canvas):
    def __init__(self,tk,g,root=None):
        if root == None:
            root = tk
        Canvas.__init__(self,root)
        self.g = g
        self.tk = tk
        tk.eval('package require Tcldot')
        self.pack(fill=BOTH,expand=1)
        self.root = root
        self.rel_enabled = dict()
        self.rebuild()
        self.update_callback = None
    def destroy(self):
##        print "destroying graph canvas"
        if self.parent != None:
##            print "removing state graph"
            self.parent.remove_state_graph(self.g)
        Canvas.destroy(self)
    def set_update_callback(self,update_callback):
        self.update_callback = update_callback
    def get_enabled(self,r):
#        rel = repr(r.rel_lit.atom)
        rel = r.rel_lit.atom
        if rel in self.rel_enabled:
            return self.rel_enabled[rel]
        res = [IntVar(self,0),IntVar(self,0),IntVar(self,0),IntVar(self,0)]
        self.rel_enabled[rel] = res
        return res

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


    def make_subgraphs(self):
        return True

    def rebuild(self):
##        print "rebuild"
        with uu.RunContext(self):
            tk = self.tk
            g = self.g
            g.recompute()
            tk.eval('set graph [dotnew digraph forcelabels true]')
            handle_to_node = dict()
            handle_to_edge = dict()
            self.node_to_handle = dict()
            if hasattr(self,'mark'):
                del self.mark
            i = 0
            sorted_nodes = self.sort_nodes([n for n in g.all_nodes if n.status != "false"])
            node_labels = self.get_node_labels(sorted_nodes)
            sort_colors = dict((sort,line_color(i)) for i,sort in enumerate(ivy_logic.sig.sorts))

            # make subgraphs for sorts
            sort_graph = {}
            for sort in ivy_logic.sig.sorts:
                if self.make_subgraphs():
                    sg = tk.eval('$graph addsubgraph cluster_' + sort + ' rank min')
                else:
                    sg = '$graph'
                sort_graph[sort] = sg

            for n in sorted_nodes:
                if n.status != "false":
                    p = n.name
    #                print "rebuild: p = {}, type(p) = {}".format(p,type(p))
                    shape = "doubleoctagon" if n.summary else "octagon"
                    labels = make_node_label(n) + node_labels[n.name]
    #                labels = node_labels[n.name]
                    if not labels:
                        labels = [str(n.sort)]
                    label = '\n'.join(labels)
                    penwidth = '4.0' if n.status == 'true' else '2.0'
                    color = sort_colors[n.sort.name]
                    handle = tk.eval(sort_graph[n.sort.name] + ' addnode {' + p + '} label {' + label + '} shape ' + shape + ' fontsize 10 penwidth ' + penwidth + ' color ' + color)
                    handle = 'node' + str(i+1)  if handle.startswith('node0x') else handle
                    i += 1
                    handle_to_node[handle] = n
                    self.node_to_handle[n.name] = handle
    ##        print "relations: %s" % g.relations
            i = 0 
            for idx,r in enumerate(g.relations):
                if r.arity() != 2:
                    continue
                ena = self.get_enabled(r)
                if any(e.get() for e in ena[0:2]):  # avoid computing edges we don't need
                    transitive = ena[3].get()
                    r.properties['reflexive'] = transitive
                    r.properties['transitive'] = transitive
                    for (x,y),status in r.get_edges():
                        style = {'true':0,'undef':1,'false':2}[status]
                        if ena[style].get():
                            style = ["solid","dotted","dashed"][style]
                            weight = '10' if transitive else '0'
                            ge = '$graph addedge {' + x.name + '} {' + y.name + '} style ' + style+ ' color {' + line_color(idx) + '} penwidth 2.0 weight ' + weight
                            handle = tk.eval(ge)
                            handle = 'edge' + str(i+1) if handle.startswith('edge0x') else handle
                            i += 1
                            rl = ~r.rel_lit if status == 'false' else r.rel_lit
                            handle_to_edge[handle] = (rl,x.name,y.name)
            tk.eval('eval [$graph render ' + self._w  + ' DOT]')
            if not g.constraints.is_true():
                bb = self.bbox(ALL)
    ##            print "bbox: {}".format(bb)
                if not bb or bb == None: # what does bbox return if canvas is empty?
                    bb = (3,3,3,3) # put text somewhere if empty canvas
                text = ['Constraints:\n' + '\n'.join(repr(clause) for clause in g.constraints.conjuncts())]
                self.create_text((bb[0],bb[3]),anchor=NW,text=text)
            self.config(scrollregion=self.bbox(ALL))
            tk.eval(self._w + ' configure -scrollregion [' + self._w + ' bbox all]')
            for x in handle_to_node:
                n = handle_to_node[x]
                self.tag_bind("0" + x, "<Button-1>", lambda y, n=n: self.left_click_node(y,n))
                self.tag_bind("1" + x, "<Button-1>", lambda y, n=n: self.left_click_node(y,n))
            for x in handle_to_edge:
                r,h,t = handle_to_edge[x]
    ##            print "r,h,t: %s %s %s" % (r,h,t)
                self.tag_bind("0" + x, "<Button-1>", lambda y, r=r,h=h,t=t: self.left_click_edge(y,r,h,t))
                self.tag_bind("1" + x, "<Button-1>", lambda y, r=r,h=h,t=t: self.left_click_edge(y,r,h,t))
            self.edge_popup = Menu(tk, tearoff=0)
            self.edge_popup.add_command(label="Empty",command=self.empty_edge)
            self.edge_popup.add_command(label="Materialize",command=self.materialize_edge)
            self.edge_popup.add_command(label="Dematerialize",command=self.dematerialize_edge)

    def export(self):
            tk = self.tk
            f = tkFileDialog.asksaveasfilename(filetypes = [('dot files', '.dot')],title='Export graph as...',parent=self)
            tk.eval('set myfd [open {' + f + '} w]')
            tk.eval('$graph write $myfd dot')
            tk.eval('close $myfd')

    def make_popup(self):
        tk = self.tk
        g = self.g
        popup = Menu(tk, tearoff=0)
        popup.add_command(label="Select",command=self.select)
        popup.add_command(label="Empty",command=self.empty)
        popup.add_command(label="Materialize",command=self.materialize)
        popup.add_command(label="Materialize edge",command=self.materialize_from_selected)
        popup.add_command(label="Splatter",command=self.splatter)
        popup.add_command(label="Split with...")
        popup.add_separator()
        for p in g.predicates:
            if isinstance(p,tuple):
                popup.add_command(label=make_lit_label(p[0]),command = lambda p=p: self.split(p))
            else:
                vs = used_variables_ast(p)
                if not vs or next(v for v in vs).sort == self.lookup_node(self.current_node).sort:
                    popup.add_command(label=make_lit_label(p),command = lambda p=p: self.split(p))
        wit = get_witness(self.lookup_node(self.current_node))
        if wit != None:
            trs = list(get_projections_of_ternaries(wit))
            if trs != []:
                popup.add_command(label="Add projection...")
                for p in trs:
                    popup.add_command(label=str(p),command = lambda p=p: self.project(p))
        return popup

    def left_click_node(self,event,n):
        # display the popup menu
        self.current_node = n.name # must be a better way...
        popup = self.make_popup()
        try:
            popup.tk_popup(event.x_root, event.y_root, 0)
        finally:
            # make sure to release the grab (Tk 8.0a1 only)
            popup.grab_release()

    def left_click_edge(self,event,rel_lit,head,tail):
        # display the popup menu
        self.current_edge = (rel_lit,head,tail)
        try:
            self.edge_popup.tk_popup(event.x_root, event.y_root, 0)
        finally:
            # make sure to release the grab (Tk 8.0a1 only)
            self.edge_popup.grab_release()
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
                dlg = Toplevel(self)
                Label(dlg, text="Cannot reverse.").pack()
                b = Button(dlg, text="OK", command=dlg.destroy)
                b.pack(padx=5,side=TOP)
                uu.center_window_on_window(dlg,self.root)
                self.tk.wait_window(dlg)
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

    def add_relation(self):
        dlg = Toplevel(self)
        Label(dlg, text="Add a relation [example: p(X,a,Y)]:").pack()
        e = Entry(dlg)
        e.focus()
        e.pack()
        action = functools.partial(self.add_rel_lit,dlg,e)
        e.bind('<Return>', lambda q,action=action: action())
        Button(dlg, text="Add",command=action).pack(padx=5,side=TOP)
        b = Button(dlg, text="Cancel", command=dlg.destroy).pack(padx=5,side=TOP)
        uu.center_window_on_window(dlg,self.root)
        self.tk.wait_window(dlg)
        
    def add_rel_lit(self,dlg,entry):
        with uu.RunContext(self):
#            with ivy_logic.UnsortedContext():
#                lit = to_literal(entry.get())
            sig = ivy_logic.sig.copy()
            with sig:
                for c in used_constants_clauses(self.g.state):
                    if not isinstance(c.sort,ivy_logic.EnumeratedSort):
#                        print "found constant {!r}".format(c)
                        ivy_logic.add_symbol(str(c),c.sort)
                for c in used_constants_clauses(self.g.constraints):
                    if not isinstance(c.sort,ivy_logic.EnumeratedSort):
#                        print "found constant {!r}".format(c)
                        ivy_logic.add_symbol(str(c),c.sort)
                lit = to_literal(entry.get())
#                lit = ivy_logic.sortify(lit)
            dlg.destroy()
#            print "add_rel_lit: {}".format(lit)
            self.g.new_relation(lit)
            if self.update_callback != None:
                self.update_callback()

    def remember(self):
        dlg = Toplevel(self)
        Label(dlg, text="Enter a name for this goal:").pack()
        e = Entry(dlg)
        e.focus()
        e.pack()
        action = functools.partial(self.remember_aux,dlg,e)
        e.bind('<Return>', action)
        Button(dlg, text="Remember",command=action).pack(padx=5,side=TOP)
        b = Button(dlg, text="Cancel", command=dlg.destroy).pack(padx=5,side=TOP)
        uu.center_window_on_window(dlg,self.root)
        self.tk.wait_window(dlg)

    def remember_aux(self,dlg,entry,*args):
        with uu.RunContext(self):
            name = entry.get()
            dlg.destroy()
            self.parent.remember_graph(name,self.g.copy())

    def project(self,p):
        self.g.new_relation(Literal(1,p))
        if self.update_callback != None:
            self.update_callback()

    def busy(self):
        self.tk.config(cursor="watch")
        self.tk.update()
        self.config(cursor="watch")

    def ready(self):
        self.tk.config(cursor="")
        self.tk.update()
        self.config(cursor="")

    def splatter(self):
        self.checkpoint()
        cn = self.lookup_node(self.current_node)
        self.g.splatter(cn)
        self.update()

    def set_parent_state(self,new_parent_state,clauses = None):
        self.checkpoint()
        self.g.parent_state = new_parent_state
        self.g.set_state(clauses if clauses else new_parent_state.clauses)
        self.update()
                         
    def reach(self):
        if self.parent != None and self.g.parent_state != None:
#            self.checkpoint()
            g = self.g
##            print "g.constraints: %s" % g.constraints
            rs = self.parent.one_step_reach(g.parent_state, g.constraints)
            if rs != None:
                clauses = rs.clauses
#                print "reach clauses: {}".format(clauses)
                dlg = Toplevel(self)
                Label(dlg, text="Goal reached! A reachable state has been added.").pack()
                b = Button(dlg, text="View state", command=functools.partial(self.view_reached,clauses,dlg))
                b.pack(padx=5,side=TOP)
                b = Button(dlg, text="OK", command=dlg.destroy)
                b.pack(padx=5,side=TOP)
                uu.center_window_on_window(dlg,self.root)
                self.tk.wait_window(dlg)
#                g.constraints = []
#                g.set_state(clauses)
#                self.update()
            else:
                dlg = Toplevel(self)
                Label(dlg, text="Cannot reach this state in on step from any known reachable state. Try \"reverse\".").pack()
                b = Button(dlg, text="OK", command=dlg.destroy)
                b.pack(padx=5,side=TOP)
                uu.center_window_on_window(dlg,self.root)
                self.tk.wait_window(dlg)

    def view_reached(self,clauses,dlg):
        dlg.destroy()
        self.checkpoint()
        self.g.set_state(clauses)
        self.update()

    def path_reach(self):
        if self.parent != None and self.g.parent_state != None:
            self.parent.bmc(self.g.parent_state,self.g.constraints if not self.g.constraints.is_true() else self.g.state)

    def conjecture(self):
        if self.parent != None and self.g.parent_state != None:
            self.checkpoint()
            g = self.g
#            print "g.constraints: %s" % g.constraints
#            print "g.state: %s" % g.state
#            print "g.constraints.is_true: %s" % g.constraints.is_true()
            s = g.state if g.constraints.is_true() else g.constraints
#            print "s: {}".format(s)
            ri = self.parent.conjecture(g.parent_state, s)
            if ri != None:
                core,interp = ri
                dlg = Toplevel(self)
                Label(dlg, text="Based on this goal and the known reached states, we can conjecture the following invariant:").pack()
                S = Scrollbar(dlg)
                T = Text(dlg, height=4, width=100)
                S.pack(side=RIGHT, fill=Y)
                T.pack(side=LEFT, fill=Y)
                S.config(command=T.yview)
                T.config(yscrollcommand=S.set)
                T.insert(END, repr(clauses_to_formula(interp)))
                b = Button(dlg, text="OK", command=dlg.destroy)
                b.pack(padx=5,side=TOP)
                uu.center_window_on_window(dlg,self.root)
                self.tk.wait_window(dlg)
#                goal = dual_clauses(interp,skolemizer=self.g.parent_state.domain.skolemizer())
                goal = lu.reskolemize_clauses(core,self.g.parent_state.domain.skolemizer())
                g.constraints = goal
                g.set_state(goal)
                self.update()
            else:
                dlg = Toplevel(self)
                Label(dlg, text="Cannot form a conjecture based in the known reached states and this goal. Suggest manually materializing a goal pattern.").pack()
                b = Button(dlg, text="OK", command=dlg.destroy)
                b.pack(padx=5,side=TOP)
                uu.center_window_on_window(dlg,self.root)
                self.tk.wait_window(dlg)

    def diagram(self):
        if self.parent != None and self.g.parent_state != None:
            self.checkpoint()
            g = self.g
##            print "g.constraints: %s" % g.constraints
            if hasattr(g,'reverse_result'):
#                "print reverse diagram"
                dgm = ivy_interp.diagram(self.g.parent_state,self.g.reverse_result[1],extra_axioms = self.g.reverse_result[0])
            else:
                dgm = ivy_interp.diagram(self.g.parent_state,self.g.state)
            if dgm != None:
                goal = lu.reskolemize_clauses(dgm,self.g.parent_state.domain.skolemizer())
                g.constraints = goal
                g.set_state(goal)
                self.update()
            else:
                dlg = Toplevel(self)
                Label(dlg, text="The current state is vacuous.").pack()
                b = Button(dlg, text="OK", command=dlg.destroy)
                b.pack(padx=5,side=TOP)
                uu.center_window_on_window(dlg,self.root)
                self.tk.wait_window(dlg)
        

    def split(self,p):
        self.checkpoint()
        cn = self.lookup_node(self.current_node)
        self.g.split(cn,p)
        self.update()

    def show_mark(self,on=True):
        if hasattr(self,'mark') and self.mark in self.node_to_handle:
            for item in self.find_withtag("1"+self.node_to_handle[self.mark]):
                self.itemconfig(item,fill=('red' if on else 'white'))

    def select(self):
        self.show_mark(False)
        self.mark = self.current_node
        self.show_mark(True)
        
    def empty(self):
        self.checkpoint()
        cn = self.lookup_node(self.current_node)
        self.g.empty(cn)
        self.update()

    def materialize(self):
#        if not self.lookup_node(self.current_node).summary:
#            return # no point in materializing singleton nodes
        self.checkpoint()
        cn = self.lookup_node(self.current_node)
        self.g.materialize(cn)
        self.update()

    def materialize_from_selected(self):
        if hasattr(self,'mark'):
            sorts = [self.lookup_node(x).sort for x in [self.mark,self.current_node]]
            required_sort = ivy_logic.RelationSort(sorts)
            rels = [r for r in self.g.relations if r.sort == required_sort]
            items = [str(r.rel_lit) for r in rels]
            msg = "Materialize this relation from selected node:"
            uu.listbox_dialog(self.tk,self.root,msg,items,command=functools.partial(self.materialize_from_selected_aux,rels))
            
    def materialize_from_selected_aux(self,rels,idx):
        self.current_edge = (rels[idx].rel_lit,self.mark,self.current_node)
        self.materialize_edge()

    def empty_edge(self):
        self.checkpoint()
        rel_lit,head,tail = self.current_edge
        head,tail = self.lookup_node(head), self.lookup_node(tail)
        self.g.empty_edge(rel_lit,head,tail)
        self.update()

    def materialize_edge(self):
        self.checkpoint()
        rel_lit,head,tail = self.current_edge
        head,tail = self.lookup_node(head), self.lookup_node(tail)
        self.g.materialize_edge(rel_lit,head,tail)
        self.update()

    def dematerialize_edge(self):
        rel_lit,head,tail = self.current_edge
        self.current_edge = (Literal(0,rel_lit.atom),head,tail)
        self.materialize_edge()

    def update(self):
        self.delete(ALL)
        self.rebuild()
#        if self.update_callback != None:
#            self.update_callback()


def foo():
    pass
##    print "foo"

def show_graph(g,tk=None,frame=None,parent=None):
#    tk = Tix.Tk()
#    scrwin = Tix.ScrolledWindow(tk, scrollbar='both')
#    scrwin.pack(fill=BOTH,expand=1)
#    gw = GraphWidget(tk,g,scrwin.window)
    global foo
    if tk == None:
        tk = Tk()
        frame = tk
    elif frame == None:
        frame = Toplevel(tk)
    legend = Frame(frame)
#    legend = Tix.ScrolledWindow(frame, scrollbar=Y) # just the vertical scrollbar
    legend.pack(side=RIGHT,fill=Y)
    menubar = uu.MenuBar(frame)
    menubar.pack(side=TOP,fill=X)
    hbar=Scrollbar(frame,orient=HORIZONTAL)
    hbar.pack(side=BOTTOM,fill=X)
    vbar=Scrollbar(frame,orient=VERTICAL)
    vbar.pack(side=RIGHT,fill=Y)
    gw = GraphWidget(tk,g,frame)
    gw.parent = parent
    hbar.config(command=gw.xview)
    vbar.config(command=gw.yview)
#    gw.config(width=300,height=300)
    gw.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
#    gw.pack(side=LEFT,expand=True,fill=BOTH)
    relbuttons = Frame(legend)
    relbuttons.pack(side=RIGHT,fill=Y,expand=1)
    update_relbuttons(gw,relbuttons)
    gw.set_update_callback(functools.partial(update_relbuttons,gw,relbuttons))

#    menubar = Menu(frame)
    actionmenu = menubar.add("Action")
#    actionmenu = Menu(menubar, tearoff=0)
    actionmenu.add_command(label="Undo",command=gw.undo)
    actionmenu.add_command(label="Redo",command=gw.redo)
    actionmenu.add_command(label="Concrete",command=gw.concrete)
    actionmenu.add_command(label="Gather",command=gw.gather)
    actionmenu.add_command(label="Reverse",command=gw.reverse)
    actionmenu.add_command(label="Path reach",command=gw.path_reach)
    actionmenu.add_command(label="Reach",command=gw.reach)
    actionmenu.add_command(label="Conjecture",command=gw.conjecture)
    actionmenu.add_command(label="Backtrack",command=gw.backtrack)
    actionmenu.add_command(label="Recalculate",command=gw.recalculate)
    actionmenu.add_command(label="Diagram",command=gw.diagram)
    actionmenu.add_command(label="Remember",command=gw.remember)
    actionmenu.add_command(label="Export",command=gw.export)
#    menubar.add_cascade(label="Action", menu=actionmenu)
    viewmenu = menubar.add("View")
    viewmenu.add_command(label="Add relation",command=gw.add_relation)
#    menubar.add_cascade(label="View", menu=viewmenu)
#    frame.config(menu=menubar)
    return gw

    # undo = Button(legend,text="Undo",command=gw.undo)
    # undo.pack(side=TOP)
    # conc = Button(legend,text="Concrete",command=gw.concrete)
    # conc.pack(side=TOP)
    # gather = Button(legend,text="Gather",command=gw.gather)
    # gather.pack(side=TOP)
    # reverse = Button(legend,text="Reverse",command=gw.reverse)
    # reverse.pack(side=TOP)
#    # print "foo!!!"
    # export = Button(legend,text="Export",command=gw.export)
    # export.pack(side=TOP)
#    tk.mainloop()

def onFrameConfigure(canvas):
   bbox = canvas.bbox("all")
   canvas.configure(scrollregion=bbox,width=bbox[2]-4)
   

def update_relbuttons(gw,relbuttons):
    for child in relbuttons.winfo_children():
        child.destroy()
    lb = Label(relbuttons,text="State: {}".format(gw.parent.state_label(gw.g.parent_state)))
    lb.pack(side = TOP)

    # make the grid of buttons scrollable
    canvas = Canvas(relbuttons, borderwidth=0, background="#ffffff")
    btns = Frame(canvas, background="#ffffff")
    vsb = Scrollbar(relbuttons, orient="vertical", command=canvas.yview)
    canvas.configure(yscrollcommand=vsb.set)
    vsb.pack(side="right", fill="y")
    canvas.pack(side="left", fill="both", expand=True)
    canvas.create_window((4,4), window=btns, anchor="nw")
    btns.bind("<Configure>", lambda event, canvas=canvas: onFrameConfigure(canvas))

    foo = Label(btns,text = '+')
    foo.grid(row = 0, column = 0)
    foo = Label(btns,text = '?')
    foo.grid(row = 0, column = 1)
    foo = Label(btns,text = '-')
    foo.grid(row = 0, column = 2)
    foo = Label(btns,text = 'T')
    foo.grid(row = 0, column = 4)
    rels = list(sorted(enumerate(gw.g.relations),key=lambda r:r[1].name()))
    for idx,(num,rel) in enumerate(rels):
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[0],command=gw.update)
        foo.grid(row = idx+1, column = 0)
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[1],command=gw.update)
        foo.grid(row = idx+1, column = 1)
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[2],command=gw.update)
        foo.grid(row = idx+1, column = 2)
        foo = Label(btns,text=rel.name(),fg=line_color(num),justify=LEFT,anchor="w")
        foo.grid(sticky=W,row = idx+1, column = 3)
        foo.bind("<Button-1>", lambda e: askcolor())
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[3],command=gw.update)
        foo.grid(row = idx+1, column = 4)
        


if __name__ == '__main__':
    nodes = [("p",to_clause("[]"))]
    state = to_clauses("[[~n(_nil,V)], [~n(V,_x)], [~n(V,_y)], [~_r_x(V),~n(V,W),_r_x(W)], [~_r_y(V),~n(V,W),_r_y(W)], [~_r_y(W),~n(_x,W)], [_r_x(W),~n(_x,W)], [_r_y(W),~n(_y,W)], [~_r_x(V),~n(_y,V)], [~_r_x(V),~_r_y(W),~n(V,W),=(W,_nil)], [~_r_x(V),~_r_y(W),~n(W,V),=(V,_nil)], [~=(_x, _nil)], [~=(_nil, _x)], [_r_x(_nil)], [~=(_x, _y)], [~=(_y, _nil)], [~_r_x(_y)], [_r_y(_nil)], [~_r_y(_x), =(_x, _nil)], [~_r_y(_x), =(_nil, _x)], [~_r_y(Xp), =(Xp, _nil), ~_r_x(Xp)], [~_r_y(Xp), =(_nil, Xp), ~_r_x(Xp)], [~=(_nil, _y)], [~_r_x(_x)], [~_r_y(_y)],[~_r_x(X),_p(X)], [~_r_y(X),_p(X)], [_p(_x)], [_p(_y)]]")
    g = Graph(nodes)
    r = GraphRelation(g,to_literal("n(X,Y)"),{"undef":"dotted","true":"solid"})
    g.add_relation(r)
    g.set_state(state)
    show_graph(g)



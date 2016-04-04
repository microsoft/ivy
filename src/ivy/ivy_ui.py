#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_interp import *
from ivy_graph import *
from string import *
import copy
import functools
from Tkinter import *
import Tkconstants, tkFileDialog
import Tix
import pickle
from ivy_concept_space import clauses_to_concept
import ivy_actions
import ivy_graph_ui
import ivy_alpha
from ivy_art import AnalysisGraph, AnalysisSubgraph
import ivy_ui_util as uu
import ivy_utils as iu

# Following is a hint to center window. Needs more research.
# from tkinter import *
# app = Tk()
# app.eval('tk::PlaceWindow %s center' % app.winfo_pathname(app.winfo_id()) )



modes = ["abstract","concrete","bounded","induction"]
default_mode = iu.Parameter("mode","abstract",lambda s: s in modes)

class AnalysisGraphWidget(Canvas):

    # Save the current arg and maybe concept graph in a file

    def save(self):
        f = self.ui_parent.saveas_dialog('Save analysis state as...',[('analysis files', '.a2g')])
        if f:
            pickle.dump(self.g,f, protocol=2)
            f.close()

    # Save the current abstract domain in a file

    def save_abstraction(self):
        f = self.ui_parent.saveas_dialog('Save abstraction as...',[('ivy files', '.ivy')])
        if f:
            for concept in self.g.domain.concept_spaces:
                f.write('concept ' + repr(concept[0]) + ' = ' + repr(concept[1]) + '\n')
            f.close()
    
    # Get the display color of an ARG node. Used by UI.

    def node_color(self,node):
        return "green" if hasattr(node,'safe') and node.safe else "black"

    # Show a state in the current concept graph, or create a concept graph

    def view_state(self,n,clauses):
        print "state: {}".format(clauses)
        if hasattr(self,'current_concept_graph') and self.current_concept_graph.winfo_exists():
            self.current_concept_graph.set_parent_state(n,clauses)
            return
        sg = self.g.concept_graph(n,clauses)
        self.current_concept_graph = self.show_graph(sg)

    # TODO: unsure what this does

    def view_concrete_trace(self,n,conc):
        pass
#        ui_create(self.g.make_concrete_trace(n,conc))


    # Get the commands for the node context menu

    def node_commands(self):
        return [
          ('Check safety',self.check_safety_node),
          ('Extend',self.find_extension),
          ('Mark',self.mark_node),
          ('Cover by marked',self.cover_node),
          ('Join with marked',self.join_node),
          ('Try conjecture',self.try_conjecture),
          ('Try remembered goal',self.try_remembered_graph),
          ('Delete',self.delete_node),
        ]

    # Get the commands for the node execute menu

    def node_execute_commands(self,n):
        state_equations = self.g.state_actions(n)
        return [(state_equation_label(a), lambda a=a: self.do_state_action(a))
                for a in sorted(state_equations, key=state_equation_label)]

    # Get the actions for the edge context menu

    def edge_actions(self,transition):
        return [
            ("Recalculate",self.recalculate_edge),
            ("Decompose",self.decompose_edge),
            ("View Source",self.view_source_edge),
            ]


    # Set the marked node

    def mark_node(self,n):
        self.show_mark(False)
        self.mark = n.id
        self.show_mark(True)

    # Get the marked node

    def get_mark(self):
        return self.g.states[self.mark]

    # Try covering a node by the marked node

    def cover_node(self,covered_node):
        g = self.g
        try:
            covering_node = self.get_mark()
        except:
            return
        print "Trying to cover %s by %s" % (covered_node.id,covering_node.id)
        with self.ui_parent.run_context():
            if not g.cover(covered_node,covering_node):
                raise IvyError(None,"Covering failed")
        self.rebuild()

    # Join a node with the marked node

    def join_node(self,node2):
        g = self.g
        try:
            node1 = self.get_mark()
        except:
            return
        with self.ui_parent.run_context():
            g.join(node1,node2,self.get_alpha())
        self.rebuild()

    # Delete a node from the ARG

    def delete_node(self,deleted_node):
        g = self.g
        g.delete(deleted_node)
        self.rebuild()

    # Set the abstract value of a state

    def set_state(self,state,clauses):
        state.clauses = clauses

    # Get the abstraction operator

    def get_alpha(self):
        return (None if self.mode.get() == "concrete"
                else ivy_alpha.alpha if (self.mode.get() == "abstract" or self.mode.get() == "induction")
                else top_alpha)

    # Evaluate a state equation to generate a new node

    def do_state_action(self,a):
        with self.ui_parent.run_context():
            with EvalContext(check=False):
                print "action {"
                s = self.g.do_state_action(a,self.get_alpha())
                print "state = {}".format(s)
                print "} action %s" % a.args[0]
        self.rebuild()

    # Evaluate an action at a node

    def execute_action(self,n,a):
        with self.ui_parent.run_context():
            print "action %s {" % a
            s = self.g.execute_action(a,n,self.get_alpha())
            print "} action %s" % a
        self.rebuild()

    # Display the reached states tree

    def show_reachable_states(self):
        ui_create(self.reachable_tree)

    # Reevaluate all the nodes in the ARG

    def recalculate_all(self):
        done = set()
        for transition in self.g.transitions:
            if transition[-1].id not in done:
                self.recalculate_edge(transition)
                done.add(transition[-1].id)

    # Reevaluate just one edges of the ARG
    # DEPRECATED: use recalculate_state

    def recalculate_edge(self,transition):
        with self.ui_parent.run_context():
            self.g.recalculate(transition,self.get_alpha())
        self.rebuild()

    # Decompose an edge into smaller actions

    def decompose_edge(self,transition):
        with self.ui_parent.run_context():
            art = self.g.decompose_edge(transition)
            if art == None:
                raise IvyError(None,'Cannot decompose action')
            ui_create(art)

    # Browse the source of an edge

    def view_source_edge(self,transition):
        with self.ui_parent.run_context():
            act = transition[1]
            assert isinstance(act,Action)
            if hasattr(act,'lineno'):
                filename,lineno = act.lineno
                self.ui_parent.browse(filename,lineno)

    # Recalculate a state based on its equation

    def recalculate_state(self,state):
        with self.ui_parent.run_context():
            self.g.recalculate_state(state,self.get_alpha())
        self.rebuild()
        
    # Return a concrete reachability graph with all the known
    # reachable states

    @property
    def reachable_tree(self):
        if  not hasattr(self,'_reachable_tree'):
            self._reachable_tree = AnalysisGraph(self.g.domain,self.g.pvars)
            for s in self.g.domain.unders[0:1]:
                self._reachable_tree.add(s)
        return self._reachable_tree

    # Try to reach a state in one step from known reached states under
    # a constraint. TODO: the computation part should be moved to AnalysisGraph

    def one_step_reach(self,state,clauses):
        with self.ui_parent.run_context():
            rs = reach_state_from_pred_no_abduction(state,clauses)
            if rs != None:
                self.reachable_tree.add(rs)
                t = self.g.transition_to(state)
                if t:
                    pre,action,label,post = t
                    self.reachable_tree.transitions.append((rs.pred,action,label,rs))
                f = filter_conjectures(state,rs.clauses)
                if f:
                    msg = "The following conjectures have been eliminated:"
                    items = [repr(clauses_to_formula(conj)) for conj in f]
                    self.ui_parent.listbox_dialog(msg,items,on_cancel=None)
            return rs

    def check_safety_node(self,node):
        if self.mode.get() != "bounded":
            node.safe = self.g.check_safety(node)
            self.update_node_color(node)
            if not node.safe:
                bcs = []
                if node.safe.clauses != None:
                    bcs.append(("View unsafe states",functools.partial(self.view_state,node.safe.state,node.safe.clauses)))
                if node.safe.conc != None:
                    bcs.append(("View concrete trace",functools.partial(self.view_concrete_trace,node.safe.state,node.safe.conc)))
                uu.buttons_dialog_cancel(self.tk,self.root,"The node is not proved safe: {}".format(node.safe.msg),bcs)
        else:
#                print "bounded check: node.safe.clauses={}".format(node.safe.clauses)
            res = self.g.check_bounded_safety(node)
            if res == None:
                node.safe = True
                self.update_node_color(node)
            else:
                node.safe = False
                uu.ok_cancel_dialog(self.tk,self.root,"The node is unsafe: View error trace?",
                                        command=functools.partial(self.view_ag,res))

    def view_ag(self,res):
        ui_create(res)
            
    def find_extension(self,node):
        try:
            with self.ui_parent.run_context():
                a = next(self.g.state_extensions(node))
                self.do_state_action(a)
        except StopIteration:
            uu.ok_dialog(self.tk,self.root,"State {} is closed.".format(node.id))
            

    def try_conjecture(self,node,conj=None):
        if conj == None:
            udc = undecided_conjectures(node)
            udc_text = [repr(clauses_to_formula(conj)) for conj in udc]
            msg = "Choose a conjecture to prove:"
            cmd = lambda idx: self.try_conjecture(node,udc[idx])
            self.ui_parent.listbox_dialog(msg,udc_text,command=cmd)
        else:
            print "type(conj) = {}".format(type(conj))
            if hasattr(conj,'lineno'):
                filename,lineno = conj.lineno
                self.ui_parent.browse(filename,lineno)
            dual = dual_clauses(conj)
            if self.mode.get() == "induction":
                self.bmc(node,dual)
            else:
                sg = self.g.concept_graph(node)
                sg.add_constraints(dual.clauses)
                self.show_graph(sg)

    def try_remembered_graph(self,node):
        dlg = Toplevel(self)
        lbl = "Choose a remembered goal:"
        Label(dlg, text=lbl).pack()
        S = Scrollbar(dlg)
        T = Listbox(dlg, height=8, width=50, selectmode=SINGLE)
        S.pack(side=RIGHT, fill=Y)
        T.pack(side=LEFT, fill=Y)
        S.config(command=T.yview)
        T.config(yscrollcommand=S.set)
        if not hasattr(self,'remembered_graphs'):
            self.remembered_graphs = {}
        names = [n for n in self.remembered_graphs]
        for name in names:
            T.insert(END, name)
        b = Button(dlg, text="Try", command=functools.partial(self.do_try_remembered_graph,node,T,dlg,names))
        b.pack(padx=5,side=TOP)
        b = Button(dlg, text="Cancel", command=dlg.destroy)
        b.pack(padx=5,side=TOP)
        uu.center_window_on_window(dlg,self.root)
        self.tk.wait_window(dlg)
        

    def do_try_remembered_graph(self,node,T,dlg,names):
        sel = map(int, T.curselection())
        dlg.destroy()
        if sel:
            sg = self.remembered_graphs[names[sel[0]]].copy()
            sg.parent_state = node
            sg.set_state(and_clauses(node.clauses,sg.constraints))
            self.g.state_graphs.append(sg)
            ivy_graph_ui.show_graph(sg,self.tk,parent=self)

    def remember_graph(self,name,graph):
        if not hasattr(self,'remembered_graphs'):
            self.remembered_graphs = {}
        self.remembered_graphs[name] = graph

    def reverse_update_concrete_clauses(self,state, clauses):
        with self.ui_parent.run_context():
            try:
                if state.pred != None:
                    print "reverse from %s to %s: post_state = %s" % (state.id,state.pred.id,clauses)
                    next_state = state.pred
                    clauses = reverse_update_concrete_clauses(state,clauses)
                    return (clauses,state.pred)

                elif hasattr(state,'join_of') and state.join_of:
                    next_state = state
                    return reverse_join_concrete_clauses(state,state.join_of,clauses)

                return None

            except UnsatCoreWithInterpolant as ici:
#                print "core: %s" % ici.core
#                print "interp: %s" % ici.interp
                if ici.interp != None:
                    used_names = used_symbols_clauses(Clauses([[Literal(0,a)] for a,d in self.g.domain.concept_spaces]))
                    name = unused_name_with_base('itp',set(s.name for s in used_names))
                    concept = clauses_to_concept(name,ici.interp)
                    dlg = Toplevel(self)
                    Label(dlg, text="The pre-state is vacuous. The following concept can be used to prove your goal in the post-state:").pack()
                    S = Scrollbar(dlg)
                    T = Text(dlg, height=4, width=100)
                    S.pack(side=RIGHT, fill=Y)
                    T.pack(side=LEFT, fill=Y)
                    S.config(command=T.yview)
                    T.config(yscrollcommand=S.set)
                    T.insert(END, 'concept ' + repr(concept[0]) + ' = ' + repr(concept[1]))
                    b = Button(dlg, text="OK", command=dlg.destroy)
                    b.pack(padx=5,side=TOP)
                    b = Button(dlg, text="Refine", command=functools.partial(self.refine,concept,dlg))
                    b.pack(padx=5,side=TOP)
                    uu.center_window_on_window(dlg,self.root)
                    self.tk.wait_window(dlg)
                    return (false_clauses(),next_state)
                raise IvyError(None,"UNSAT, but interpolant could not be computed")
        return ([[]],next_state)

    def conjecture(self,state,clauses):
        with self.ui_parent.run_context():
            return case_conjecture(state,clauses)

    def refine(self,concept,dlg):
        print "concept: {}".format(concept)
        self.g.domain.concept_spaces.append((concept[0],concept[1]))
#        print "current concepts: {}".format(self.g.domain.concept_spaces)
        dlg.destroy()
    def state_label(self,state):
        return str(state.id)
    def add_state_graph(self,sg):
        self.g.state_graphs.append(sg)
    def remove_state_graph(self,sg):
        self.g.state_graphs.remove(sg)

    def bmc(self,state,err_cond):
        res = self.g.bmc(state,err_cond)
        if res == None:
            dlg = Toplevel(self)
            Label(dlg, text="The condition is unreachable along the given path").pack()
            b = Button(dlg, text="OK", command=dlg.destroy)
            b.pack(padx=5,side=TOP)
            uu.center_window_on_window(dlg,self.root)
            self.tk.wait_window(dlg)
            return
        ui_create(res)


def state_equation_label(se):
    ac = se.args[0]
    al = str(se.args[1].rep)
    return al if ac is None else al + ' -> ' + str(se.args[0])

class IvyUI(object):
    def __init__(self,tk=None,frame=None):
        pass

ui = None

def ui_create(art,tk=None,frame=None):
    # if ui exists, ignore the requested frame and put the art in a
    # tab of the global ui
    global ui
    if ui == None:
        ui = IvyUI(tk,frame)
    ui.add(art)

def ui_main_loop(art, tk = None, frame = None):
    ui_create(art,tk,frame)
    ui.tk.mainloop()


if __name__ == '__main__':
    d = ShapeDomain(["x", "y", "t"], True)
    ag = AnalysisGraph(d)
    s = State(d, to_clauses("[[~n(V1,V2)],[~=(x,y)],[~r_x(y)],[~r_y(x)]]")) # start with empty next relation
    ag.add(s)
    ag.execute("alloc t")
    ag.execute("t.n := x")
    s1 = ag.execute("x := t")
    ag.execute("alloc t")
    ag.execute("t.n := x")
    ag.execute("x := t")
    ag.join(s1)
    ag.execute("alloc t")
    ag.execute("t.n := y")
    ag.execute("y := t")
    ag.display()


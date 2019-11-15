#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_interp import *
from ivy_graph import *
from string import *
import copy
import functools
import pickle
from ivy_concept_space import clauses_to_concept
import ivy_actions
import ivy_graph_ui
import ivy_alpha
from ivy_art import AnalysisGraph, AnalysisSubgraph
from ivy_graph_ui import GraphWidget
import ivy_ui_util as uu
import ivy_utils as iu

# Following is a hint to center window. Needs more research.
# from tkinter import *
# app = Tk()
# app.eval('tk::PlaceWindow %s center' % app.winfo_pathname(app.winfo_id()) )



modes = ["abstract","concrete","bounded","induction"]
default_mode = iu.Parameter("mode","abstract",lambda s: s in modes)

class AnalysisGraphUI(object):

    # This defines the menus items we provide. The actual menus might be
    # tool buttons or other such things.

    def menus(self):
        return [("menu","File",
                 [("button","Save",self.save),
                  ("button","Save abstraction",self.save_abstraction),
                  ("separator",),
                  ("button","Remove tab",lambda self=self: self.ui_parent.remove(self)),
                  ("button","Exit", lambda self=self: self.ui_parent.exit()),]),
                ("menu","Mode",
                 [("radiobuttons","mode",default_mode.get(),
                   [("Concrete","concrete"),
                    ("Abstract","abstract"),
                    ("Bounded","bounded"),
                    ("Induction","induction")])]),
                 ("menu","Action",
                  [("button","Recalculate all",self.recalculate_all),
                   ("button","Show reachable states",self.show_reachable_states),])]

    # get the mode variable

    @property 
    def mode(self):
        return self.radiobutton('mode')

    # This is called on startup of the ui. We initialize by creating an intitial
    # node in the ART. Whether we abstract or not depends on the mode. For historical
    # reasons, abstract mode uses a concrete initial state.

    def start(self):
        if len(self.g.states) == 0:
            self.g.initialize(self.init_alpha())
        self.rebuild()

    def init_alpha(self):
        if 'mode' in self.radios:
            return (None if (self.mode.get() == "concrete" or self.mode.get() == "abstract")
                    else ivy_alpha.alpha if self.mode.get() == "induction"
                    else top_alpha)
        return top_alpha
        

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

    # Actions to perform on nodes

    def get_node_actions(self,node,click='left'):
        if click == 'left':
            return [("<>",self.view_state)]
        else:
            return ([("Execute action:",None),
                     ("---",None),] +
                    self.node_execute_commands(node) +
                    [("---",None),] +
                    self.node_commands())

    # When left-clicking a node, we view it

    def get_edge_actions(self,transition,click='right'):
        if click == 'left':
            return [] # nothing on right click yet
        else:
            return ([("Dismiss",lambda t: None),
                     ("Recalculate",self.recalculate_edge),
                     ("Step in",self.decompose_edge),
                     ("View Source",self.view_source_edge),])


    # Show a state in the current concept graph, or create a concept graph

    def view_state(self,n,clauses = None, reset=False):
        clauses = clauses or n.clauses
#        print "state: {}".format(clauses)
        if hasattr(self,'current_concept_graph'):
           #  and self.current_concept_graph.winfo_exists():
#            print "current cg: {}".format(type(self.current_concept_graph))
            self.current_concept_graph.set_parent_state(n,clauses,reset=reset)
            return
        sg = self.g.concept_graph(n,standard_graph,clauses)
        self.current_concept_graph = self.show_graph(sg)
        return self.current_concept_graph

    # TODO: unsure what this does

    def view_concrete_trace(self,n,conc):
        pass
#        self.ui_parent.add(self.g.make_concrete_trace(n,conc))


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
        return [(state_equation_label(a), functools.partial(self.do_state_action,a))
                for a in sorted(state_equations, key=state_equation_label)]

    # Set the marked node

    def mark_node(self,n):
        self.show_mark(False)
        self.mark = n
        self.show_mark(True)

    # Get the marked node

    def get_mark(self):
        return self.mark

    # Try covering a node by the marked node

    def cover_node(self,covered_node):
        g = self.g
        covering_node = self.get_mark()
        if covering_node is not None:
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

    # Get the node with given id

    def node(self,id):
        return self.g.states[id]

    # Evaluate a state equation to generate a new node

    def do_state_action(self,a,node=None):
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
        self.ui_parent.add(self.reachable_tree)

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
            return self.ui_parent.add(art,ui_class=AnalysisGraphUI)

    # Decompose incoming edge of a node into smaller actions

    def decompose_node(self,node):
        with self.ui_parent.run_context():
            art = self.g.decompose_state(node)
            if art == None:
                raise IvyError(None,'Cannot decompose action')
            return self.ui_parent.add(art,ui_class=AnalysisGraphUI)

    # Browse the source of an edge

    def view_source_edge(self,transition):
        with self.ui_parent.run_context():
            act = transition[1]
            assert isinstance(act,Action)
            if hasattr(act,'lineno'):
                filename,lineno = act.lineno.filename,act.lineno.line
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
    # a constraint. TODO: the computation part should be moved to
    # AnalysisGraph

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

    # Check the safety of a state on a path from the initial
    # state. This is not really BMC checking since only the last state
    # is checked. To be marked safe, the node must satsify any
    # specified safety condition, and the incoming transition must not
    # have any failures.

    def check_bounded_safety(self,node):
        res = self.g.check_bounded_safety(node)
        if res == None:
            node.safe = True
            self.update_node_color(node)
        else:
            node.safe = False
            msg = "The node is unsafe: View error trace?"
            cmd = functools.partial(self.view_ag,res)
            self.ui_parent.ok_cancel_dialog(msg,cmd)

    # Check local safety of a node. A node is locally safe if its
    # abstract state implies any safety conditions and if if its
    # predecessor's abstrafct state implies the weakest precondition
    # of its incoming action.

    def check_local_safety(self,node):
        node.safe = self.g.check_safety(node)
        self.update_node_color(node)
        if not node.safe:
            bcs = []
            if node.safe.clauses != None:
                bcs.append(("View unsafe states",functools.partial(self.view_state,node.safe.state,node.safe.clauses)))
            if node.safe.conc != None:
                bcs.append(("View concrete trace",functools.partial(self.view_concrete_trace,node.safe.state,node.safe.conc)))
            msg = "The node is not proved safe: {}".format(node.safe.msg)
            self.ui_parent.buttons_dialog_cancel(msg,bcs)
        
    # Check safety of a node using the current mode.

    def check_safety_node(self,node):
        if self.mode.get() != "bounded" and self.mode.get() != "induction":
            self.check_local_safety(node)
        else:
            self.check_bounded_safety(node)

    # Add an ARG to the UI

    def view_ag(self,res):
        self.ui_parent.add(res)
            
    # Find an action that can extend the ARG at the given node,
    # without being covered. This is a useful operation for lazy
    # abstraction.

    def find_extension(self,node):
        try:
            with self.ui_parent.run_context():
                a = next(self.g.state_extensions(node))
                self.do_state_action(a)
        except StopIteration:
            self.ui_parent.ok_dialog("State {} is closed.".format(node.id))
            

    # Set up to prove a conjecture at the given node. If no conjecture
    # is given, display a list of not-yet-proven conjectures for the
    # user to choose from. Also browses the source code of the
    # conjecture. The proof method depends on the current mode.

    def try_conjecture(self,node,conj=None,msg=None,bound=None):
        if conj == None:
            udc = undecided_conjectures(node)
            udc_text = [repr(clauses_to_formula(conj)) for conj in udc]
            msg = msg or "Choose a conjecture to prove:"
            cmd = lambda idx: self.try_conjecture(node,udc[idx],bound=bound)
            self.ui_parent.listbox_dialog(msg,udc_text,command=cmd)
        else:
            if hasattr(conj,'lineno'):
                filename,lineno = conj.lineno
                self.ui_parent.browse(filename,lineno)
            dual = dual_clauses(conj)
            if self.mode.get() == "induction":
                self.bmc(node,dual,bound=bound)
            else:
                sg = self.g.concept_graph(node,standard_graph)
                sg.current.add_constraints(dual.conjuncts)
                self.show_graph(sg)

    # Set up to prove a remembered subgoal. If no goal is given, display a list
    # of remembered subgoals for the user. 

    def try_remembered_graph(self,node, goal=None):
        if not hasattr(self,'remembered_graphs'):
            self.remembered_graphs = {}
        if goal == None:
            msg = "Choose a remembered goal:"
            names = [n for n in self.remembered_graphs]
            cmd = lambda idx: self.try_remembered_graph(node,names[idx])
            self.ui_parent.listbox_dialog(msg,names,command=cmd)
        else:
            sg = self.remembered_graphs[goal].copy()
            sg.parent_state = node
            sg.set_state(and_clauses(node.clauses,sg.constraints))
            self.g.state_graphs.append(sg)
            self.show_graph(sg)

    # Save a proof goal under a given name.

    def remember_graph(self,name,graph):
        if not hasattr(self,'remembered_graphs'):
            self.remembered_graphs = {}
        self.remembered_graphs[name] = graph

    # This is the "reverse" step from lazy annotation or IC3, with
    # refinement.  It tries to push back the proof goal "clauses" at
    # node "state" to the predecessor state. If this feasible, the new
    # proof goal is returned as a pair (clauses,state). If infeasible,
    # an interpolant is computed that can be used as a refinement for
    # the current node. In this case, the returned goal is "false". If
    # here is no predecessor node, None is returned.

    def reverse_update_concrete_clauses(self,state, clauses):
        with self.ui_parent.run_context():
            try:
                return self.reverse_goal(state, clauses)
            except UnsatCoreWithInterpolant as ici:
#                print "core: %s" % ici.core
#                print "interp: %s" % ici.interp
                if ici.interp != None:
                    self.refine_with_interpolant(ici.interp)
                    return (false_clauses(),state.pred)
                raise IvyError(None,"UNSAT, but interpolant could not be computed")

    # This is the "reverse" step from lazy annotation or IC3.
    # It tries to push back the proof goal "clauses" at node "state"
    # to the predecessor state. If this feasible, the new proof goal
    # is returned as a pair (clauses,state). If infeasible, an
    # UnsatCoreWithInterpolant exception is raised. If
    # here is no predecessor node, None is returned.

    # TODO: this should really move to ARG, since there are not UI actions

    def reverse_goal(self, state, clauses):
        if state.pred != None:
            print "reverse from %s to %s: post_state = %s" % (state.id,state.pred.id,clauses)
            next_state = state.pred
            clauses = reverse_update_concrete_clauses(state,clauses)
            return (clauses,state.pred)
        elif hasattr(state,'join_of') and state.join_of:
            next_state = state
            return reverse_join_concrete_clauses(state,state.join_of,clauses)
        return None

    # Refine the abstract domain with an interpolant (as a Clauses)
    # Displays the refinement and gives the user the option to apply
    # it.

    def refine_with_interpolant(self,interp):
        concept = self.interp_to_refinement(interp)
        msg = "The pre-state is vacuous. The following concept can be used to prove your goal in the post-state:"
        text = 'concept ' + repr(concept[0]) + ' = ' + repr(concept[1])
        cmd = functools.partial(self.refine,concept)
        self.ui_parent.text_dialog(msg,text,command=cmd,command_label="Refine")

    # Refine the abstract domain with an interpolant (as a Clauses)
    # Displays the refinement and gives the user the option to apply
    # it. TODO: move to ARG.

    def interp_to_refinement(self,interp):
        used_names = used_symbols_clauses(Clauses([[Literal(0,a)] for a,d in self.g.domain.concept_spaces]))
        name = unused_name_with_base('itp',set(s.name for s in used_names))
        return clauses_to_concept(name,interp)

    # Conjecture a separator between state underapprox and clauses.
    # The separator must be true of all models of the underapprox and
    # false in at least one model of clauses.

    def conjecture(self,state,clauses):
        with self.ui_parent.run_context():
            return case_conjecture(state,clauses)

    # Refines the abstract domain by adding a new concept space.

    def refine(self,concept):
        self.g.domain.concept_spaces.append((concept[0],concept[1]))

    # Get a label for an ARG node

    def state_label(self,state):
        return str(state.id)

    # DEPRECATED: add a concept graph to the ARG's list

    def add_state_graph(self,sg):
        pass

    # DEPRECATED: remove a concept graph to the ARG's list

    def remove_state_graph(self,sg):
        pass

    # Bounded reachability: find a concrete path from initial node to
    # a given state satisfying err_cond in state.

    def bmc(self,state,err_cond,bound=None):
        res = self.g.bmc(state,err_cond,bound=bound)
        if res == None:
            msg = "The condition is unreachable along the given path"
            self.ui_parent.ok_dialog(msg)
            return None
        return self.ui_parent.add(res)

    def CGUI(self):
        # This returns the default Concept Graph UI class
        return GraphWidget

def state_equation_label(se):
    ac = se.args[0]
    al = str(se.args[1].rep)
    return al if ac is None else al + ' -> ' + str(se.args[0])

class IvyUI(object):

    # This returns the default Analysis Graph UI class
    def AGUI(self):
        return AnalysisGraphUI

    # Set up to prove a background property. If no property
    # is given, display a list of not-yet-proven properties for the
    # user to choose from. Also browses the source code of the
    # property. The proof method depends on the current mode.

    def try_property(self,prop=None):
        if prop == None:
            udc = false_properties()
            udc_text = [str(prop) for prop in udc]
            msg = "Choose a property to see counterexample:"
            cmd = lambda idx: self.try_property(udc[idx])
            self.listbox_dialog(msg,udc_text,command=cmd)
        else:
            print "type(prop) = {}".format(type(prop))
            if hasattr(prop,'lineno'):
                filename,lineno = prop.lineno
                self.browse(filename,lineno)
            dual = dual_clauses(formula_to_clauses(prop.formula))
            dual = and_clauses(dual,get_property_context(prop))
            ag = AnalysisGraph(initializer=top_alpha)
            oag = ag.bmc(ag.states[0],dual)
            self.add(oag)


ui = None

def ui_main_loop(art, tk = None, frame = None):
    ui_create(art,tk,frame)
    ui.tk.mainloop()

compile_kwargs = {}


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


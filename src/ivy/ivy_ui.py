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


class RunContext(object):
    """ Context Manager that handles exceptions and reports errors. """
    def __init__(self,parent):
        """ parent should be a window """
        self.parent = parent
    def __enter__(self):
        self.parent.busy()
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        self.parent.ready()
        if exc_type == IvyError:
            dlg = Toplevel(self.parent)
            Label(dlg, text=repr(exc_val)).pack(side=TOP)
            b = Button(dlg, text="OK", command=dlg.destroy)
            b.pack(padx=5,side=TOP)
#            uu.center_window_on_window(dlg,self.parent.root)
            self.parent.tk.wait_window(dlg)
            return True
        return False # don't block any exceptions

modes = ["abstract","concrete","bounded","induction"]
default_mode = iu.Parameter("mode","abstract",lambda s: s in modes)

class AnalysisGraphWidget(Canvas):
    def __init__(self,tk,g,root=None,toplevel=None):
        if root == None:
            root = tk
        if toplevel==None:
            toplevel=root
#        menubar = Menu(toplevel)
        menubar = uu.MenuBar(root)
        menubar.pack(side=TOP,fill=X)
#        filemenu = Menu(menubar, tearoff=0)
        filemenu = menubar.add("File")
        filemenu.add_command(label="Save",command=self.save)
        filemenu.add_command(label="Save abstraction",command=self.save_abstraction)
        filemenu.add_separator()
        filemenu.add_command(label="Remove tab", command=lambda self=self: self.ui_parent.remove(self))
        filemenu.add_command(label="Exit", command=tk.quit)
#        menubar.add_cascade(label="File", menu=filemenu)
#        modemenu = Menu(menubar, tearoff=0)
        modemenu = menubar.add("Mode")
        self.mode = StringVar(root,default_mode.get())
        modemenu.add("radiobutton",label="Concrete",variable=self.mode,value="concrete")
        modemenu.add("radiobutton",label="Abstract",variable=self.mode,value="abstract")
        modemenu.add("radiobutton",label="Bounded",variable=self.mode,value="bounded")
        modemenu.add("radiobutton",label="Induction",variable=self.mode,value="induction")
#        menubar.add_cascade(label="Mode", menu=modemenu)
#        actionmenu = Menu(menubar, tearoff=0)
        actionmenu = menubar.add("Action")
        actionmenu.add_command(label="Recalculate all",command=self.recalculate_all)
        actionmenu.add_command(label="Show reachable states",command=self.show_reachable_states)
#        menubar.add_cascade(label="Action", menu=actionmenu)
#        toplevel.config(menu=menubar)

#        sw= Tix.ScrolledWindow(root, scrollbar=BOTH) # just the vertical scrollbar
#        sw.pack(fill=BOTH, expand=1)

        Canvas.__init__(self,root)
        self.g = g
        self.tk = tk
        self.root = root
        self.mark = None
        tk.eval('package require Tcldot')
        self.pack(fill=BOTH,expand=1)
        self.rebuild()
    def busy(self):
        self.tk.config(cursor="watch")
        self.tk.update()
        self.config(cursor="watch")
    def ready(self):
        self.tk.config(cursor="")
        self.tk.update()
        self.config(cursor="")
    def save(self):
        f = tkFileDialog.asksaveasfile(mode='w',filetypes = [('analysis files', '.a2g')],title='Save analysis state as...',parent=self)
        if f:
            pickle.dump(self.g,f, protocol=2)
            f.close()
    def save_abstraction(self):
        f = tkFileDialog.asksaveasfile(mode='w',filetypes = [('ivy files', '.ivy')],title='Save abstraction as...',parent=self)
        if f:
            for concept in self.g.domain.concept_spaces:
                f.write('concept ' + repr(concept[0]) + ' = ' + repr(concept[1]) + '\n')
            f.close()
    
    def node_color(self,node):
        return "green" if hasattr(node,'safe') and node.safe else "black"

    def rebuild(self):
        tk = self.tk
        g = self.g
        tk.eval('set graph [dotnew digraph forcelabels true]')
        handle_to_node = dict()
        self.node_to_handle = dict()
        for (s,i) in zip(g.states,range(len(g.states))):
                p = "%d" % i
                shape = "point" if (s.clauses != None and s.clauses.is_false()) else "circle"
                label = str(s.id) if s.clauses != None else '?'
                color = self.node_color(s) 
                handle = tk.eval('$graph addnode "' + p + '" label "' + label + '" shape ' + shape + ' color ' + color + ' fontsize 10 width 0.5 penwidth 2.0')
                handle = 'node' + str(i+1) if handle.startswith('node0x') else handle
                self.node_to_handle[i] = handle
                handle_to_node[handle] = s
        i = 0
        edge_handles = []
        for transition in g.transitions:
                x,op,label,y = transition
                # Curly braces don't survive tcldot (even if they balance). We work around this by replacing them with digraphs
                # and then fixing it below by modding the text of the canvas items. Also, we want our code labels to be left 
                # justified, so we end the lines with \l, which dot recognizes. Note the backslashes are escaped, since this
                # is *not* a special character, it is a two-character sequence.
                label = label.replace('}',']-').replace('{','-[')
                label = label.replace('\n','\\l')+'\\l'
                handle = tk.eval('$graph addedge "' + ("%d" % x.id) + '" "' + ("%d" % y.id) + '" label {' + label + '} fontsize 10 penwidth 2.0')
                handle = 'edge' + str(i+1)  if handle.startswith('edge0x') else handle
                edge_handles.append(handle)
                i += 1
                if isinstance(op,AnalysisSubgraph):
                    self.tag_bind("0" + handle, "<Button-1>", lambda y, op=op: op.display(tk))
                    self.tag_bind("1" + handle, "<Button-1>", lambda y, op=op: op.display(tk))
                self.tag_bind("0" + handle, "<Button-3>", lambda ev, transition=transition: self.right_click_edge(ev,transition))
                self.tag_bind("1" + handle, "<Button-3>", lambda ev, transition=transition: self.right_click_edge(ev,transition))
        for (x,y) in g.covering:
                handle = tk.eval('$graph addedge "' + ("%d" % x.id) + '" "' + ("%d" % y.id) + '" style dashed')
        self.delete(ALL)
#        print tk.eval('$graph render ' + self._w  + ' DOT')
        tk.eval('eval [$graph render ' + self._w  + ' DOT]')
        self.config(scrollregion=self.bbox(ALL))
        for x in handle_to_node:
            n = handle_to_node[x]
#            print "x = {}".format(x)
#            print "n = {}".format(n)
            self.tag_bind("0" + x, "<Button-1>", lambda y, n=n: self.left_click_node(y,n))
            self.tag_bind("1" + x, "<Button-1>", lambda y, n=n: self.left_click_node(y,n))
            self.tag_bind("0" + x, "<Button-3>", lambda y, n=n: self.right_click_node(y,n))
            self.tag_bind("1" + x, "<Button-3>", lambda y, n=n: self.right_click_node(y,n))
        for x in edge_handles:
            items = self.find_withtag("0" + x)
#            print 'items:{}'.format(items)
            for item in items:
                text = self.itemcget(item,'text')
                text = text.replace('-[','{').replace(']-','}')
                self.itemconfig(item,text=text)
        self.show_mark(True)

    def update_node_color(self,node):
        for item in self.find_withtag("1"+self.node_to_handle[node.id]):
            self.itemconfig(item,outline=self.node_color(node))

    def show_mark(self,on=True):
        if self.mark in self.node_to_handle:
            for item in self.find_withtag("1"+self.node_to_handle[self.mark]):
                self.itemconfig(item,fill=('red' if on else 'white'))
    def view_state(self,n,clauses):
        print "state: {}".format(clauses)
        if hasattr(self,'current_concept_graph') and self.current_concept_graph.winfo_exists():
            self.current_concept_graph.set_parent_state(n,clauses)
            return
        sg = self.g.concept_graph(n,clauses)
        self.current_concept_graph = ivy_graph_ui.show_graph(sg,self.tk,parent=self,frame=self.state_frame)
    def view_concrete_trace(self,n,conc):
        pass
#        ui_create(self.g.make_concrete_trace(n,conc))
    def left_click_node(self,event,n):
        if n.clauses != None:
            self.view_state(n,n.clauses)
    def right_click_node(self,event,n):
        tk = self.tk
        g = self.g
        self.popup = Menu(tk, tearoff=0)
        self.popup.add_command(label="Execute action:")
        self.popup.add_separator()
        state_equations = g.state_actions(n)
        for a in sorted(state_equations, key=state_equation_label):
            self.popup.add_command(label=state_equation_label(a),command = lambda n=n,a=a: self.do_state_action(a))
        self.popup.add_separator()
        self.popup.add_command(label='Check safety',command = lambda n=n: self.check_safety_node(n))
        self.popup.add_command(label='Extend',command = lambda n=n: self.find_extension(n))
        self.popup.add_command(label='Mark',command = lambda n=n: self.mark_node(n))
        self.popup.add_command(label='Cover by marked',command = lambda n=n: self.cover_node(n))
        self.popup.add_command(label='Join with marked',command = lambda n=n: self.join_node(n))
        self.popup.add_command(label='Try conjecture',command = lambda n=n: self.try_conjecture(n))
        self.popup.add_command(label='Try remembered goal',command = lambda n=n: self.try_remembered_graph(n))
        self.popup.add_command(label='Delete',command = lambda n=n: self.delete_node(n))
        self.popup.tk_popup(event.x_root, event.y_root, 0)
    def mark_node(self,n):
        self.show_mark(False)
        self.mark = n.id
        self.show_mark(True)
    def get_mark(self):
        return self.g.states[self.mark]
    def cover_node(self,covered_node):
        g = self.g
        try:
            covering_node = self.get_mark()
        except:
            return
        print "Trying to cover %s by %s" % (covered_node.id,covering_node.id)
        with RunContext(self):
            if not g.cover(covered_node,covering_node):
                raise IvyError(None,"Covering failed")
        self.rebuild()
    def join_node(self,node2):
        g = self.g
        try:
            node1 = self.get_mark()
        except:
            return
        with RunContext(self):
            g.join(node1,node2,self.get_alpha())
        self.rebuild()
    def delete_node(self,deleted_node):
        g = self.g
        g.delete(deleted_node)
        self.rebuild()
    def right_click_edge(self,event,transition):
        tk = self.tk
        g = self.g
        self.popup = Menu(tk, tearoff=0)
        self.popup.add_command(label="Dismiss")
        self.popup.add_command(label="Recalculate",command = lambda transition=transition: self.recalculate_edge(transition))
        self.popup.add_command(label="Decompose",command = lambda transition=transition: self.decompose_edge(transition))
        self.popup.add_command(label="View Source",command = lambda transition=transition: self.view_source_edge(transition))
        self.popup.tk_popup(event.x_root, event.y_root, 0)

    def set_state(self,state,clauses):
        state.clauses = clauses

    def get_alpha(self):
        return (None if self.mode.get() == "concrete"
                else ivy_alpha.alpha if (self.mode.get() == "abstract" or self.mode.get() == "induction")
                else top_alpha)

    def do_state_action(self,a):
        with RunContext(self):
            with EvalContext(check=False):
                print "action {"
                s = self.g.do_state_action(a,self.get_alpha())
                print "state = {}".format(s)
                print "} action %s" % a.args[0]
        self.rebuild()

    def execute_action(self,n,a):
        with RunContext(self):
            print "action %s {" % a
            s = self.g.execute_action(a,n,self.get_alpha())
            print "} action %s" % a
        self.rebuild()

    def show_reachable_states(self):
        ui_create(self.reachable_tree)

    def recalculate_all(self):
        done = set()
        for transition in self.g.transitions:
            if transition[-1].id not in done:
                self.recalculate_edge(transition)
                done.add(transition[-1].id)

    def recalculate_edge(self,transition):
        with RunContext(self):
            self.g.recalculate(transition,self.get_alpha())
        self.rebuild()

    def decompose_edge(self,transition):
        with RunContext(self):
            art = self.g.decompose_edge(transition)
            if art == None:
                raise IvyError(None,'Cannot decompose action')
            ui_create(art)

    def view_source_edge(self,transition):
        with RunContext(self):
            act = transition[1]
            assert isinstance(act,Action)
            if hasattr(act,'lineno'):
                filename,lineno = act.lineno
                self.ui_parent.browse(filename,lineno)

    def recalculate_state(self,state):
        with RunContext(self):
            self.g.recalculate_state(state,self.get_alpha())
        self.rebuild()
        
    @property
    def reachable_tree(self):
        if  not hasattr(self,'_reachable_tree'):
            self._reachable_tree = AnalysisGraph(self.g.domain,self.g.pvars)
            for s in self.g.domain.unders[0:1]:
                self._reachable_tree.add(s)
        return self._reachable_tree

    def one_step_reach(self,state,clauses):
        with RunContext(self):
            rs = reach_state_from_pred_no_abduction(state,clauses)
            if rs != None:
                self.reachable_tree.add(rs)
                t = self.g.transition_to(state)
                if t:
                    pre,action,label,post = t
                    self.reachable_tree.transitions.append((rs.pred,action,label,rs))
                f = filter_conjectures(state,rs.clauses)
                if f:
                    dlg = Toplevel(self)
                    Label(dlg, text="The following conjectures have been eliminated:").pack()
                    S = Scrollbar(dlg)
                    T = Listbox(dlg, height=8, width=50, selectmode=SINGLE)
                    S.pack(side=RIGHT, fill=Y)
                    T.pack(side=LEFT, fill=Y)
                    S.config(command=T.yview)
                    T.config(yscrollcommand=S.set)
                    for conj in f:
                        T.insert(END, repr(clauses_to_formula(conj)))
                    b = Button(dlg, text="OK", command=dlg.destroy)
                    b.pack(padx=5,side=TOP)
                    uu.center_window_on_window(dlg,self.root)
                    self.tk.wait_window(dlg)
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
            with RunContext(self):
                a = next(self.g.state_extensions(node))
                self.do_state_action(a)
        except StopIteration:
            uu.ok_dialog(self.tk,self.root,"State {} is closed.".format(node.id))
            

    def try_conjecture(self,node):
        dlg = Toplevel(self)
        lbl = "Choose a conjecture to prove:"
        Label(dlg, text=lbl).pack()
        S = Scrollbar(dlg)
        T = Listbox(dlg, height=8, width=50, selectmode=SINGLE)
        S.pack(side=RIGHT, fill=Y)
        T.pack(side=LEFT, fill=Y)
        S.config(command=T.yview)
        T.config(yscrollcommand=S.set)
        udc = undecided_conjectures(node)
        for conj in udc:
            T.insert(END, repr(clauses_to_formula(conj)))
        b = Button(dlg, text="Prove", command=functools.partial(self.do_try_conjecture,node,T,dlg,udc))
        b.pack(padx=5,side=TOP)
        b = Button(dlg, text="Cancel", command=dlg.destroy)
        b.pack(padx=5,side=TOP)
        uu.center_window_on_window(dlg,self.root)
        self.tk.wait_window(dlg)
        

    def do_try_conjecture(self,node,T,dlg,udc):
        sel = map(int, T.curselection())
        if sel:
            conj = udc[sel[0]]
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
                ivy_graph_ui.show_graph(sg,self.tk,parent=self,frame=self.state_frame)
        dlg.destroy()


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
        with RunContext(self):
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
        with RunContext(self):
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
        if tk == None:
            tk = Tix.Tk()
            tk.tk_setPalette(background='white')
            tk.wm_title("ivy")
            frame = tk
        elif frame == None:
            frame = Toplevel(tk)
        self.tk = tk
        self.frame = frame
        self.notebook = Tix.NoteBook(frame)
        self.notebook.pack(fill=BOTH,expand=1)
        self.tab_counter = 0
        self.tabs = 0
        
    def add(self,art,name=None,label=None):
        self.tab_counter += 1
        self.tabs += 1
        if name == None:
            name = "sheet_{}".format(self.tab_counter)
        if label == None:
            label = "Sheet {}".format(self.tab_counter)
        tk = self.tk
        nb = self.notebook
        if not hasattr(art,'state_graphs'):
            art.state_graphs = []
        tab = nb.add(name,label=label) 
        pw=Tix.PanedWindow(tab,orientation='horizontal')
        pw.pack(fill=BOTH,expand=1)
        frame=pw.add('f1')
        state_frame=pw.add('f2')
        hbar=Scrollbar(frame,orient=HORIZONTAL)
        hbar.pack(side=BOTTOM,fill=X)
        vbar=Scrollbar(frame,orient=VERTICAL)
        vbar.pack(side=RIGHT,fill=Y)
        gw = AnalysisGraphWidget(tk,art,frame)
        gw.state_frame=state_frame
        gw.ui_parent = self
        gw.ui_tab_name = name
        hbar.config(command=gw.xview)
        vbar.config(command=gw.yview)
        gw.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
        for sg in art.state_graphs:
            ivy_graph_ui.show_graph(sg,tk,parent=gw,frame=state_frame)
        nb.raise_page(name)

    def remove(self,art):
        self.notebook.delete(art.ui_tab_name)
        self.tabs -= 1
        if self.tabs == 0:
            self.tk.quit()

    def browse(self,filename,lineno):
        if not (hasattr(self,'browser') and self.browser.winfo_exists()):
            self.browser = uu.new_file_browser(self.tk)
        self.browser.set(filename,lineno)

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


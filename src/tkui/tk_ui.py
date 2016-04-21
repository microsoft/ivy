#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy_ui
import ivy_ui_util as uu
import ivy_utils as iu
import tk_graph_ui
from Tkinter import *
import Tkconstants, tkFileDialog
import Tix

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
        if exc_type == iu.IvyError:
            dlg = Toplevel(self.parent.frame)
            Label(dlg, text=repr(exc_val)).pack(side=TOP)
            b = Button(dlg, text="OK", command=dlg.destroy)
            b.pack(padx=5,side=TOP)
#            uu.center_window_on_window(dlg,self.parent.root)
            self.parent.tk.wait_window(dlg)
            return True
        return False # don't block any exceptions


# This user interface has one window with a set of tabs containing
# ARG's. There is a single window on the right hand side displaying a
# concept graph (usually the current proof goal or concrete state).

class TkUI(ivy_ui.IvyUI):

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
        
    # Add a new AnalysisGraph to the UI

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
        gw = TkAnalysisGraphWidget(tk,art,frame)
        gw.state_frame=state_frame
        gw.ui_parent = self
        gw.ui_tab_name = name
        hbar.config(command=gw.xview)
        vbar.config(command=gw.yview)
        gw.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
        for sg in art.state_graphs:
            tk_graph_ui.show_graph(sg,tk,parent=gw,frame=state_frame,ui_parent=this)
        nb.raise_page(name)

    def remove(self,art):
        self.notebook.delete(art.ui_tab_name)
        self.tabs -= 1
        if self.tabs == 0:
            self.tk.quit()

    # Browse a source file

    def browse(self,filename,lineno):
        if not (hasattr(self,'browser') and self.browser.winfo_exists()):
            self.browser = uu.new_file_browser(self.tk)
        self.browser.set(filename,lineno)


    # Show a message and get "OK"

    def ok_dialog(self,msg):
        uu.ok_dialog(self.tk,self.frame,msg)

    # Show a message and get "OK" or cancel

    def ok_cancel_dialog(self,msg,cmd):
        uu.ok_cancel_dialog(self.tk,self.frame,msg,cmd)

    # Create a dialog letting user choose from a list of string items.
    # The command is called with the chosen item index. If the user
    # selects "Cancel", on_cancel is called. If on_cancel is None
    # no "Cancel" button is provided.

    def listbox_dialog(self,msg,items,command=lambda:None,on_cancel=lambda:None):
        uu.listbox_dialog(self.tk,self.frame,msg,items,command,on_cancel)

    # Create a dialog showing a message and some text.  The command is
    # called when the user selects "OK". If the user selects "Cancel",
    # on_cancel is called. If on_cancel is None no "Cancel" button is
    # provided. Parameter command_label is alternative text for "OK".

    def text_dialog(self,msg,text,command=lambda:None,on_cancel=lambda:None,command_label=None):
        uu.text_dialog(self.tk,self.frame,msg,text,command,on_cancel,command_label)

    # Create a dialog showing a message and antry.  The command is
    # called with the entry contents when the user selects "OK". If
    # the user selects "Cancel", on_cancel is called. If on_cancel is
    # None no "Cancel" button is provided. Parameter command_label is
    # alternative text for "OK".

    def entry_dialog(self,msg,command=lambda:None,on_cancel=lambda:None,command_label=None):
        uu.entry_dialog(self.tk,self.frame,msg,command,on_cancel,command_label)

    # Create a dialog with a message and some action buttons. Each button_command
    # is a (label,function) pair.

    def buttons_dialog_cancel(self,msg,button_commands,on_cancel=lambda:None):
        uu.buttons_dialog_cancel(self.tk,self.frame,msg,button_commands,on_cancel=lambda:None)


    # Create a "save as" dialog with given message and file types. Parameter
    # filetypes is a list of pairs (extension, description).

    def saveas_dialog(self,msg,filetypes):
        return tkFileDialog.asksaveasfile(mode='w',filetypes=filetypes,title=msg,parent=self.frame)

    # Return a context object to use for a computation that might take
    # take or throw an error the needs reporting

    def run_context(self):
        return RunContext(self)

    # Show a busy cursor, or in some other way indicate we are busy

    def busy(self):
        self.tk.config(cursor="watch")
        self.tk.update()
        self.frame.config(cursor="watch")

    # Show a normal cursor, or in some other way indicate we are ready

    def ready(self):
        self.tk.config(cursor="")
        self.tk.update()
        self.frame.config(cursor="")

class TkAnalysisGraphWidget(ivy_ui.AnalysisGraphWidget,Canvas):

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
        self.mode = StringVar(root,ivy_ui.default_mode.get())
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

    # This is called to rebuild the graph display after any change

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
                if isinstance(op,ivy_ui.AnalysisSubgraph):
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

    # Display a concept graph

    def show_graph(self,sg):
        return tk_graph_ui.show_graph(sg,self.tk,parent=self,frame=self.state_frame,ui_parent=self.ui_parent)


    # Called if the status of a node changes to update display

    def update_node_color(self,node):
        for item in self.find_withtag("1"+self.node_to_handle[node.id]):
            self.itemconfig(item,outline=self.node_color(node))

    # Called if the marked node changes to update display

    def show_mark(self,on=True):
        if self.mark in self.node_to_handle:
            for item in self.find_withtag("1"+self.node_to_handle[self.mark]):
                self.itemconfig(item,fill=('red' if on else 'white'))

    # When left-clicking a node, we view it

    def left_click_node(self,event,n):
        if n.clauses != None:
            self.view_state(n,n.clauses)

    def right_click_node(self,event,n):
        tk = self.tk
        g = self.g
        self.popup = Menu(tk, tearoff=0)
        self.popup.add_command(label="Execute action:")
        self.popup.add_separator()
        for label,command in self.node_execute_commands(n):
            self.popup.add_command(label=label,command=command)
        self.popup.add_separator()
        for label,c in self.node_commands():
            self.popup.add_command(label=label,command=lambda c=c,n=n: c(n))
        self.popup.tk_popup(event.x_root, event.y_root, 0)

    def right_click_edge(self,event,transition):
        tk = self.tk
        g = self.g
        self.popup = Menu(tk, tearoff=0)
        self.popup.add_command(label="Dismiss")
        for label,c in self.edge_actions(transition):
            self.popup.add_command(label=label,command = lambda c=c,transition=transition: c(transition))
        self.popup.tk_popup(event.x_root, event.y_root, 0)


def ui_main_loop(art):
    ivy_ui.ui = TkUI()
    ivy_ui.ui.add(art)
    ivy_ui.ui.tk.mainloop()

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy_ui
import ivy_ui_util as uu
import ivy_utils as iu
import tk_graph_ui
import tk_cy
from cy_elements import *
from dot_layout import dot_layout
from Tkinter import *
import Tkconstants, tkFileDialog
import Tix

class RunContext(object):
    """ Context Manager that handles exceptions and reports errors. """
    def __init__(self,parent):
        """ parent should be a window """
        self.parent = parent
    def __enter__(self):
#        self.parent.busy()
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
#        self.parent.ready()
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

class TkUI(object):

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
        self.answers = []
        # pre-compile the default AnalysysGraphUI
        self.analysisGraphWidgetClass = self.wrap_art_ui(self.AGUI())

        
    # Wrap a subclass of  AnaysisGraphiUI class in a Tk interface.

    def wrap_art_ui(self,ag_ui):
        return type('AGWC',(TkAnalysisGraphWidget,ag_ui),{})

    # run the ui

    def mainloop(self):
        self.tk.mainloop()

    # stop the ui

    def exit(self):
        self.tk.quit()

    # Add a new AnalysisGraph to the UI

    def add(self,art,name=None,label=None,ui_class=None):
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
        frame=pw.add('f1',min=50)
        state_frame=pw.add('f2',min=200)
        hbar=Scrollbar(frame,orient=HORIZONTAL)
        hbar.pack(side=BOTTOM,fill=X)
        vbar=Scrollbar(frame,orient=VERTICAL)
        vbar.pack(side=RIGHT,fill=Y)
        tk_ag_ui = self.wrap_art_ui(ui_class) if ui_class else self.analysisGraphWidgetClass
        gw = tk_ag_ui(tk,art,frame)
        gw.state_frame=state_frame
        gw.ui_parent = self
        gw.ui_tab_name = name
        hbar.config(command=gw.xview)
        vbar.config(command=gw.yview)
        gw.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
        for sg in art.state_graphs:
            tk_graph_ui.show_graph(sg,tk,parent=gw,frame=state_frame,ui_parent=this)
        nb.raise_page(name)
        gw.start()
        return gw

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
        uu.ok_dialog(self.tk,self.frame,msg,ans=self.getans())

    # Show a message and get "OK" or cancel

    def ok_cancel_dialog(self,msg,cmd):
        uu.ok_cancel_dialog(self.tk,self.frame,msg,cmd,ans=self.getans())

    # Create a dialog letting user choose from a list of string items.
    # The command is called with the chosen item index. If the user
    # selects "Cancel", on_cancel is called. If on_cancel is None
    # no "Cancel" button is provided.

    def listbox_dialog(self,msg,items,command=lambda:None,on_cancel=lambda:None,multiple=False):
        uu.listbox_dialog(self.tk,self.frame,msg,items,command,on_cancel,multiple)

    # Create a dialog showing a message and some text.  The command is
    # called when the user selects "OK". If the user selects "Cancel",
    # on_cancel is called. If on_cancel is None no "Cancel" button is
    # provided. Parameter command_label is alternative text for "OK".

    def text_dialog(self,msg,text,**kwargs):
        uu.text_dialog(self.tk,self.frame,msg,text,ans=self.getans(),**kwargs)

    # Create a dialog showing a message and requesting an integer input. The command is
    # called when the user selects "OK". If the user selects "Cancel",
    # on_cancel is called. If on_cancel is None no "Cancel" button is
    # provided. Parameter command_label is alternative text for "OK".

    def int_dialog(self,msg,**kwargs):
        uu.int_dialog(self.tk,self.frame,msg,**kwargs)

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

    # Record a dialog answer for testing

    def answer(self,string):
        self.answers.append(string)

    def getans(self):
        return self.answers.pop() if self.answers else None
        

class TkAnalysisGraphWidget(tk_cy.TkCyCanvas,uu.WithMenuBar):

    def __init__(self,tk,g,root=None,toplevel=None):
        if root == None:
            root = tk
        if toplevel==None:
            toplevel=root

        uu.WithMenuBar.__init__(self,root)
        Canvas.__init__(self,root)
        self.g = g
        self.tk = tk
        self.root = root
        self.mark = None
#        tk.eval('package require Tcldot')
        self.pack(fill=BOTH,expand=1)
        self.graphWidgetClass = type('GWC',(tk_graph_ui.TkGraphWidget,self.CGUI()),{})
        self.rebuild()

    # Get styles for nodes

    def get_node_styles(self,elem):
        res = {'width' : 2}
        res['fill'] = 'black' if get_classes(elem) == 'bottom_state' else ''
        res['outline'] = 'black'
        return res
        
            
    # Get styles for edges

    def get_edge_styles(self,elem):
        res = {'width' : 2}
        res['arrowshape']="14 14 5"
        res['fill'] = 'black'
        if get_classes(elem) == "cover":
            res['dash'] = (5,5)
        return res

    # This is called to rebuild the graph display after any change

    def rebuild(self):

        self.delete(ALL)

        self.create_elements(self.g.as_cy_elements(dot_layout))

        # set the scroll region
        
        self.config(scrollregion=self.bbox(ALL))
        
        # fix the digraphs in edge labels

        items = self.find_withtag('edge_label')
        for item in items:
            text = self.itemcget(item,'text')
            text = text.replace('-[','{').replace(']-','}')
            self.itemconfig(item,text=text)

        # show the marked node, if any

        self.show_mark(True)

    # Display a concept graph

    def show_graph(self,sg):
        return tk_graph_ui.show_graph(sg,self.tk,parent=self,frame=self.state_frame,ui_parent=self.ui_parent)

    # Get tag of node

    def node_tag(self,node):
        return "n{}".format(node.id)

    # Called if the status of a node changes to update display

    def update_node_color(self,node):
        for item in self.find_withtag(self.node_tag(node)):
            if 'shape' in self.gettags(item):
                self.itemconfig(item,outline=self.node_color(node))

    # Called if the marked node changes to update display

    def show_mark(self,on=True):
        if self.mark is not None:
            for item in self.find_withtag(self.node_tag(self.mark)):
                if 'shape' in self.gettags(item):
                    self.itemconfig(item,fill=('red' if on else ''))

    def node_from_cy_elem(self,elem):
        return get_obj(elem)

    def edge_from_cy_elem(self,elem):
        return tuple(f(elem)
                     for f in (get_source_obj,get_obj,get_label,get_target_obj))


# Tricky. Rather that have seprate "ui" and "gui" objects that call
# eachother, we treat the gui objects as mixins. This function takes a
# ui class, mixes it with the gui and instantiates.

def new_ui(ui_class = None):
    ui_class = ui_class or ivy_ui.get_default_ui_class()
    tkui_class = type('TkUImixed',(TkUI,ui_class),{})
    ivy_ui.ui = tkui_class()
    return ivy_ui.ui
    
def ui_main_loop(art):
    new_ui()
    ivy_ui.ui.add(art)
    ivy_ui.ui.tk.mainloop()

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy_ui
import ivy_ui_util as uu
import ivy_utils as iu
import ivy_graph_ui
from Tkinter import *
import Tkconstants, tkFileDialog
import Tix
import functools

class TkGraphWidget(ivy_graph_ui.GraphWidget,Canvas):

    def __init__(self,tk,gs,root=None,ui_parent=None):
        if root == None:
            root = tk
        Canvas.__init__(self,root)
        self.graph_stack = gs
        self.tk = tk
        tk.eval('package require Tcldot')
        self.pack(fill=BOTH,expand=1)
        self.root = root
        self.rel_enabled = dict()
        self.update_callback = None
        self.ui_parent = ui_parent
        self.rebuild()

    # This is in case the widget is detroyed by the user. We inform
    # our parent of our demise.

    def destroy(self):
        Canvas.destroy(self)


    # Get the nth line color. This is toolkit-dependent.

    def line_color(self,idx):
        return line_colors[idx % len(line_colors)]

    # Get the enabled state for a concept "r"

    def get_enabled(self,r):
#        rel = repr(r.rel_lit.atom)
        rel = r.rel_lit.atom
        if rel in self.rel_enabled:
            return self.rel_enabled[rel]
        res = [IntVar(self,0),IntVar(self,0),IntVar(self,0),IntVar(self,0)]
        self.rel_enabled[rel] = res
        return res

    # Rebuild the display. This is called after any change to the
    # concept graph that might affect more that just line styles.
    # This calls tcldot to lay out the graph and render it in the Tk
    # canvas.

    def rebuild(self):
##        print "rebuild"
        with self.ui_parent.run_context():
            if hasattr(self,"state_label_widget"):
                sl = self.parent.state_label(self.g.parent_state)
                self.state_label_widget.configure(text="State: {}".format(sl))
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
            sort_colors = dict((sort,self.line_color(i)) for i,sort in enumerate(g.sorts))

            # make subgraphs for sorts
            sort_graph = {}
            for sort in g.sorts:
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
                    labels = self.make_node_label(n) + node_labels[n.name]
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
                            ge = '$graph addedge {' + x.name + '} {' + y.name + '} style ' + style+ ' color {' + self.line_color(idx) + '} penwidth 2.0 weight ' + weight
                            handle = tk.eval(ge)
                            handle = 'edge' + str(i+1) if handle.startswith('edge0x') else handle
                            i += 1
                            rl = ~r.rel_lit if status == 'false' else r.rel_lit
                            handle_to_edge[handle] = (rl,x.name,y.name)
            print(tk.eval('$graph render ' + self._w  + ' DOT'))
            tk.eval('eval [$graph render ' + self._w  + ' DOT]')
            if not g.constraints.is_true():
                bb = self.bbox(ALL)
    ##            print "bbox: {}".format(bb)
                if not bb or bb == None: # what does bbox return if canvas is empty?
                    bb = (3,3,3,3) # put text somewhere if empty canvas
                text = ['Constraints:\n' + '\n'.join(str(clause) for clause in g.constraints.conjuncts())]
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

    # Export the display in DOT format. This also depends on tcldot.

    def export(self):
            tk = self.tk
            f = tkFileDialog.asksaveasfilename(filetypes = [('dot files', '.dot')],title='Export graph as...',parent=self)
            tk.eval('set myfd [open {' + f + '} w]')
            tk.eval('$graph write $myfd dot')
            tk.eval('close $myfd')


    def make_popup(self,actions,arg):
        tk = self.tk
        g = self.g
        popup = Menu(tk, tearoff=0)
        for lbl,cmd in actions:
            if lbl == '---':
                popup.add_separator()
            else:
                if cmd == None:
                    popup.add_command(label=lbl)
                else:
                    popup.add_command(label=lbl,command=functools.partial(cmd,arg))
        return popup
        

    # Make the node pop-up menu for left-click

    def make_node_popup(self,node):
        return self.make_popup(self.get_node_actions(node),node)
    
    # Make the edge pop-up menu for left-click

    def make_edge_popup(self,edge):
        return self.make_popup(self.get_edge_actions(edge),edge)

    # Handle a left click on a node

    def left_click_node(self,event,n):
        # display the popup menu
        popup = self.make_node_popup(n)
        try:
            popup.tk_popup(event.x_root, event.y_root, 0)
        finally:
            # make sure to release the grab (Tk 8.0a1 only)
            popup.grab_release()

    # Handle a left click on an edge

    def left_click_edge(self,event,rel_lit,head,tail):
        # display the popup menu 
        edge = (rel_lit,head,tail)
        popup = self.make_edge_popup(edge)
        try:
            popup.tk_popup(event.x_root, event.y_root, 0)
        finally:
            # make sure to release the grab (Tk 8.0a1 only)
            popup.grab_release()

    # Call this when UI needs to be updated.

    def update(self):
        self.delete(ALL)
        self.rebuild()


# Wrap a concept graph object in a user interface

def show_graph(g,tk=None,frame=None,parent=None,ui_parent=None):
#    tk = Tix.Tk()
#    scrwin = Tix.ScrolledWindow(tk, scrollbar='both')
#    scrwin.pack(fill=BOTH,expand=1)
#    gw = GraphWidget(tk,g,scrwin.window)

    if iu.use_new_ui.get():
        import tk_graph_ui_new
        return tk_graph_ui_new.show_graph(g,tk,frame,parent,ui_parent)

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
    viewmenu.add_command(label="Add relation",command=gw.add_concept_from_string)
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

def update_relbuttons(gw,relbuttons):
    for child in relbuttons.winfo_children():
        child.destroy()
    lb = Label(relbuttons,text="State: {}".format(gw.parent.state_label(gw.g.parent_state)))
    gw.state_label_widget = lb
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
    line_color = gw.line_color
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
        

def onFrameConfigure(canvas):
   bbox = canvas.bbox("all")
   canvas.configure(scrollregion=bbox,width=bbox[2]-4)

line_colors = ["black","blue","red","green","VioletRed4","brown1",
"DarkSlateGray4","navy","DeepPink4","DarkOliveGreen4","purple4","RosyBrown4",
"SkyBlue4","tomato4",'DarkSeaGreen4','DarkOrchid2','DarkOrange3',
"DeepSkyBlue4", "IndianRed1", "maroon4", "DarkOrchid3", "chocolate1",
"RoyalBlue1", "OrangeRed4", "green2", "MediumPurple4", "brown4",
]

   


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

# Functions for destructuring cytoscape elements

def xform(coord):
    return (coord[0],-coord[1])

def get_coord(position):
    return xform(tuple(position[s] for s in ('x','y')))

def get_group(element):
    return element['group']

def get_classes(element):
    return element['classes']

def get_shape(element):
    return element['data']['shape']

def get_label(element):
    return element['data']['label']

def get_id(element):
    return element['data']['id']

def get_obj(element):
    # drop initial dot
    return element['data']['obj']

def get_arrowend(element):
    p1 = get_coord(element['data']['bspline'][-1])
    p2 = get_coord(element['data']['arrowend'])
    return p1 + p2

node_styles = {
    'at_least_one' : {'width' : 2, 'double' : 5},
    'at_most_one' : {'width' : 2},
    'exactly_one' : {'width' : 4},
    }

edge_styles = {
    'none_to_none' : {'width' : 2, 'dash' : (10,10)},
    'all_to_all' : {'width' : 2},
    'edge_unknown' : {'width' : 2, 'dash' : (2,2)},
    }

def octagon_points(x0,y0,x1,y1):
    cut = 1.0 - (1.0 / (2.4142135623730951))
    xcut = (x1 - x0) * cut / 2.0
    ycut = (y1 - y0) * cut / 2.0
    return (x0+xcut,y0,x1-xcut,y0,x1,y0+ycut,x1,y1-ycut,
            x1-xcut,y1,x0+xcut,y1,x0,y1-ycut,x0,y0+ycut)


# Return the dimension of an elenent as (x,y,w,h) where x and y are
# center coords.

def get_dimensions(element):
    data = element['data']
    position = element['position']
    return get_coord(position) + tuple(data[s] for s in ('width','height'))

# Return the bspline of an element as a list of coords
# (x0,y0,x1,y1,...)

def get_bspline(element):
    bspline = map(get_coord,element['data']['bspline'])
    coords = []
    for p in bspline:
        coords.append(p[0])
        coords.append(p[1])
    return coords
            

class TkGraphWidget(ivy_graph_ui.GraphWidget,Canvas):

    def __init__(self,tk,gs,root=None,ui_parent=None):
        if root == None:
            root = tk
        Canvas.__init__(self,root)
        self.graph_stack = gs
        self.tk = tk
        self.pack(fill=BOTH,expand=1)
        self.root = root
        self.rel_enabled = dict()
        self.update_callback = None
        self.ui_parent = ui_parent
        self.rebuild()

    # This is in case the widget is detroyed by the user. We could
    # inform our parent of our demise. TODO: not needed any more?

    def destroy(self):
        Canvas.destroy(self)


    # Get the nth line color. Colors are toolkit-dependent, so it's here.

    def line_color(self,idx):
        return line_colors[idx % len(line_colors)]

    # Get the enabled state for a concept "r". TODO: create a class
    # for this.

    def get_enabled(self,rel):
        if rel in self.rel_enabled:
            return self.rel_enabled[rel]
        res = [IntVar(self,0),IntVar(self,0),IntVar(self,0),IntVar(self,0)]
        self.rel_enabled[rel] = res
        return res

    # Copy checkbox state to the renderer

    def sync_checkboxes(self):
        for rel in self.g.relation_ids:
            boxes = self.get_enabled(rel)
            for idx,box in enumerate(boxes):
                self.g.widget.set_checkbox(rel,idx,box.get())

    # Get styles for nodes

    def get_node_styles(self,elem):
        res = node_styles[get_classes(elem)]
        res['fill'] = ''
        res['outline'] = self.colors[get_obj(elem)]
        return res
        
            
    # Get styles for edges

    def get_edge_styles(self,elem):
        res = edge_styles[get_classes(elem)]
        res['arrowshape']="14 14 5"
        res['fill'] = self.colors[get_obj(elem)]
        return res

    # Make an octagon

    def create_octagon(self,*box,**kwargs):
        pts = octagon_points(*box)
        return self.create_polygon(*pts,**kwargs)

    # Create a shape with given dimansions on canvas

    def create_shape(self,shape,dimensions,**kwargs):
        x,y,w,h = dimensions
        x0,y0,x1,y1 = x-w/2, y-h/2, x+w/2, y+h/2
        method = {'oval':self.create_oval, 'octagon':self.create_octagon}[shape]
        if 'double' in kwargs:
            gap = kwargs['double']
            del kwargs['double']
            method(x0+gap,y0+gap,x1-gap,y1-gap,**kwargs)
        return method(x0,y0,x1,y1,**kwargs)
 
    # Rebuild the display. This is called after any change to the
    # concept graph that affects the layout. Here, we assume layout
    # has already been done and we render to a Tk Canvas.

    def rebuild(self):
        with self.ui_parent.run_context():  # in case this is slow, but should not be

            # update the state label if needed (TODO: could be elsewhere)

            if hasattr(self,"state_label_widget"):
                sl = self.parent.state_label(self.g.parent_state)
                self.state_label_widget.configure(text="State: {}".format(sl))

            tk = self.tk
            g = self.g
            # g.recompute()  (we assume already computed and layed out)

            # choose colors for sorts and concepts

            self.colors = dict((sort,self.line_color(i)) for i,sort in enumerate(g.sort_ids))
            for idx,r in enumerate(g.relation_ids):
                self.colors[r] = self.line_color(idx)
            print "colors: {}".format(self.colors)

            # "mark" gives the name of the selected node. clear it

            if hasattr(self,'mark'):
                del self.mark

            cy_elements  = g.widget.cy_elements  # the graph with layout

            # create all the graph elements (TODO: factor out)

            for idx,elem in enumerate(cy_elements.elements):
                eid = get_id(elem)
                group = get_group(elem)
                if group == 'nodes':
                    dims = get_dimensions(elem)
                    styles = self.get_node_styles(elem)
                    shape = self.create_shape(get_shape(elem),dims,tags=eid,**styles)
                    label = self.create_text(dims[0],dims[1],text=get_label(elem),tags=eid)
                    self.tag_bind(eid, "<Button-1>", lambda y, elem=elem: self.left_click_node(y,elem))
                elif group == 'edges':
                    coords = get_bspline(elem)
                    styles = self.get_edge_styles(elem)
                    line = self.create_line(*coords,tags=eid,smooth="bezier",**styles)
                    arrow = self.create_line(*get_arrowend(elem),tags=eid,arrow=LAST,**styles)
                    self.tag_bind(eid, "<Button-1>", lambda y, elem=elem: self.left_click_edge(y,elem))

            # show the constraint if there is one

            if not g.constraints.is_true():
                bb = self.bbox(ALL)
                if not bb or bb == None: # what does bbox return if canvas is empty?
                    bb = (3,3,3,3) # put text somewhere if empty canvas
                text = ['Constraints:\n' + '\n'.join(str(clause) for clause in g.constraints.conjuncts())]
                self.create_text((bb[0],bb[3]),anchor=NW,text=text)

            # set the scroll region

            self.config(scrollregion=self.bbox(ALL))

            # TODO: isn't this the same as above???
            tk.eval(self._w + ' configure -scrollregion [' + self._w + ' bbox all]')


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

    def left_click_node(self,event,elem):
        n = self.g.concept_from_id(get_obj(elem))
        # display the popup menu
        popup = self.make_node_popup(n)
        try:
            popup.tk_popup(event.x_root, event.y_root, 0)
        finally:
            # make sure to release the grab (Tk 8.0a1 only)
            popup.grab_release()

    # Handle a left click on an edge

    def left_click_edge(self,event,elem):
        # display the popup menu 
        edge = tuple(self.g.concept_from_id(f(elem))
                     for x in (get_obj,get_source_obj,get_target_obj))
        popup = self.make_edge_popup(edge)
        try:
            popup.tk_popup(event.x_root, event.y_root, 0)
        finally:
            # make sure to release the grab (Tk 8.0a1 only)
            popup.grab_release()

    # Call this when UI needs to be updated.

    def update(self):
        self.delete(ALL)
        print "syncing..."
        self.sync_checkboxes()
        print "recomputing..."
        self.g.recompute()
        print "rebuilding"
        self.rebuild()


# Wrap a concept graph object in a user interface

def show_graph(g,tk=None,frame=None,parent=None,ui_parent=None):
#    tk = Tix.Tk()
#    scrwin = Tix.ScrolledWindow(tk, scrollbar='both')
#    scrwin.pack(fill=BOTH,expand=1)
#    gw = GraphWidget(tk,g,scrwin.window)
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
    gw = TkGraphWidget(tk,g,frame,ui_parent=ui_parent)
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
    rels = list(sorted(enumerate(gw.g.relation_ids),key=lambda r:r[1]))
    line_color = gw.line_color
    for idx,(num,rel) in enumerate(rels):
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[0],command=gw.update)
        foo.grid(row = idx+1, column = 0)
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[1],command=gw.update)
        foo.grid(row = idx+1, column = 1)
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[2],command=gw.update)
        foo.grid(row = idx+1, column = 2)
        foo = Label(btns,text=rel,fg=line_color(num),justify=LEFT,anchor="w")
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

   


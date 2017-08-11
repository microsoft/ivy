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
from cy_elements import *
from tk_cy import *

node_styles = {
    'at_least_one' : {'width' : 4, 'double' : 5},
    'at_most_one' : {'width' : 2},
    'exactly_one' : {'width' : 4},
    'node_unknown' :  {'width' : 2, 'double' : 5},
    }

edge_styles = {
    'none_to_none' : {'width' : 2, 'dash' : (10,10)},
    'all_to_all' : {'width' : 2},
    'edge_unknown' : {'width' : 2, 'dash' : (2,2)},
    }

class TkGraphWidget(TkCyCanvas,uu.WithMenuBar):

    def __init__(self,tk,gs,root=None,ui_parent=None):
        if root == None:
            root = tk
        uu.WithMenuBar.__init__(self,root)
        Canvas.__init__(self,root)
        self.graph_stack = gs
        self.tk = tk
        self.root = root
        self.rel_enabled = dict()
        self.update_callback = None
        self.ui_parent = ui_parent
        self.elem_ids = {}
        self.node_selection = set()
        self.edge_selection = set()
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
                self.g.set_checkbox(rel,idx,box.get())
        for rel in self.g.default_labels:
            for idx in range(4):
                self.g.set_checkbox(rel,idx,idx==0)

    # Copy checkbox state *from* the renderer

    def reverse_sync_checkboxes(self):
        for rel in self.g.relation_ids:
            boxes = self.get_enabled(rel)
            for idx,box in enumerate(boxes):
                box.set(self.g.get_checkbox(rel,idx))
    
    # Make a node label visible

    def show_node_label(self,concept):
        boxes = self.get_enabled(concept.name)
        boxes[0].set(True)

    # Make an edge relation visible

    def show_edge(self,concept,box='+',value=True):
        boxes = self.get_enabled(concept.name)
        idx = {'+':0,'?':1,'-':2,'T':3}[box]
        boxes[idx].set(value)

    # Clear all the relation checkboxes

    def clear_edges(self):
        for rel in self.g.relation_ids:
            boxes = self.get_enabled(rel)
            for box in boxes[:3]:
                box.set(False)

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

 
    # choose colors for concepts. nodes are colored by sort

    def choose_colors(self):
        g = self.g
        sort_colors = dict((sort,self.line_color(i)) for i,sort in enumerate(g.sort_names))
        self.colors = {}
        for n in g.nodes:
            self.colors[g.id_from_concept(n)] = sort_colors[g.node_sort(n).name]
        for idx,r in enumerate(g.relation_ids):
            self.colors[r] = self.line_color(idx)
#        print "colors: {}".format(self.colors)


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

            self.choose_colors()

            # "mark" gives the name of the selected node. clear it

            if hasattr(self,'mark'):
                del self.mark

            # clear the selection (TODO: keep it and redraw it)
            self.clear_elem_selection()

            self.create_elements(g.cy_elements)

            # show the constraint if there is one

            if not g.constraints.is_true():
                bb = self.bbox(ALL)
                if not bb or bb == None: # what does bbox return if canvas is empty?
                    bb = (3,3,3,3) # put text somewhere if empty canvas
                x,y = (bb[0],bb[3] + 5)
                item = self.create_text((x,y),anchor=NW,text='Constraints:')
                y = self.bbox(item)[3]
                self.selected_constraints = [True for idx in g.constraints.conjuncts()]
                for idx,clause in enumerate(g.constraints.conjuncts()):
                    tag = 'cnst{}'.format(idx)
                    item = self.create_text((x,y),anchor=NW,text=str(clause),tags=tag)
                    action = lambda y, idx=idx, item=item: self.left_click_constraint (idx,item)
                    self.tag_bind(tag, "<Button-1>", action)
                    y = self.bbox(item)[3]
                    
                # text = ['Constraints:\n' + '\n'.join(str(clause) for clause in g.constraints.conjuncts())]
                # item = self.create_text((x,y),anchor=NW,text=text)
                # iu.dbg('self.bbox(item)')

            # set the scroll region

            self.config(scrollregion=self.bbox(ALL))

            # TODO: isn't this the same as above???
            tk.eval(self._w + ' configure -scrollregion [' + self._w + ' bbox all]')


    def left_click_constraint(self,idx,item,val=None):
        self.selected_constraints[idx] = val if val is not None else not self.selected_constraints[idx]
        self.itemconfig(item,fill='black' if self.selected_constraints[idx] else 'grey')

    def get_active_facts(self):
        """
        Return a list of the selected facts
        """
        facts = self.g.constraints.conjuncts()
        if hasattr(self,'selected_constraints'):
            sc = self.selected_constraints
            if len(sc) == len(facts): # paranoia
                facts = [x for x,y in zip(facts,sc) if y]
        return facts

    def select_fact(self,fact,val=None):
        if hasattr(self,'selected_constraints'):
            for idx,f in enumerate(self.g.constraints.conjuncts()):
                if f == fact and idx < len(self.selected_constraints):
                    for item in self.find_withtag('cnst{}'.format(idx)):
                        self.left_click_constraint(idx,item,val)

    def show_mark(self,on=True):
        if hasattr(self,'mark'):
            tag = self.elem_ids[self.g.id_from_concept(self.mark)]
            for item in self.find_withtag(tag):
                if 'shape' in self.gettags(item):
                    self.itemconfig(item,fill=('red' if on else ''))

    def select_node(self,node,val=None):
        cid = self.g.id_from_concept(node)
        tag = self.elem_ids[cid]
        ns = self.node_selection
        newval = val if val is not None else cid not in ns
        ns.discard(cid)
        if newval:
            ns.add(cid)
        for item in self.find_withtag(tag):
            if 'shape' in self.gettags(item):
                self.itemconfig(item,fill=('grey' if newval else ''))

    def select_edge(self,edge,val=None):
        cid = tuple(self.g.id_from_concept(c) for c in edge)

        es = self.edge_selection
        newval = val if val is not None else cid not in es
        es.discard(cid)
        if newval:
            es.add(cid)
#        for item in self.find_withtag(tag):
#            self.itemconfig(item,fill=('grey' if newval else 'black'))
        try:
            tag = self.g.edge_cy_id(edge)
            self.highlight_edge(tag,newval)
        except KeyError:
            pass

    # Export the display in DOT format. This also depends on tcldot.

    def export(self):
            tk = self.tk
            f = tkFileDialog.asksaveasfilename(filetypes = [('dot files', '.dot')],title='Export graph as...',parent=self)
            tk.eval('set myfd [open {' + f + '} w]')
            tk.eval('$graph write $myfd dot')
            tk.eval('close $myfd')

    def node_from_cy_elem(self,elem):
        return self.g.concept_from_id(get_obj(elem))

    def edge_from_cy_elem(self,elem):
        return tuple(self.g.concept_from_id(f(elem))
                     for f in (get_obj,get_source_obj,get_target_obj))

    # Call this when UI needs to be updated.

    def update(self):
        self.delete(ALL)
        self.sync_checkboxes()
        self.g.recompute()
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
    

#    menubar = uu.MenuBar(frame)
#    menubar.pack(side=TOP,fill=X)
    gw = parent.graphWidgetClass(tk,g,frame,ui_parent=ui_parent)
    hbar=Scrollbar(frame,orient=HORIZONTAL)
    hbar.pack(side=BOTTOM,fill=X)
    vbar=Scrollbar(frame,orient=VERTICAL)
    vbar.pack(side=RIGHT,fill=Y)
    gw.pack(fill=BOTH,expand=1)

    gw.parent = parent
    hbar.config(command=gw.xview)
    vbar.config(command=gw.yview)
#    gw.config(width=300,height=300)
    gw.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
#    gw.pack(side=LEFT,expand=True,fill=BOTH)
#    relbuttonwin = Toplevel(tk)
#    relbuttons = Frame(relbuttonwin)
    relbuttons = Frame(legend)
    relbuttons.pack(side=RIGHT,fill=Y,expand=1)
    rb = create_relbuttons_window(gw,relbuttons)
    update_relbuttons(gw,rb)
    gw.set_update_callback(functools.partial(update_relbuttons,gw,rb))

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

def create_relbuttons_window(gw,relbuttons):
    lb = Label(relbuttons,text="State: {}".format(gw.parent.state_label(gw.g.parent_state)))
    gw.state_label_widget = lb
    lb.pack(side = TOP)
    sbtns = Tix.ScrolledHList(relbuttons,options='hlist.columns 5 hlist.background #ffffff',width=300)
    sbtns.pack(side="left", fill="both", expand=True)
    btns = sbtns.subwidget('hlist')
    return lb,btns
    
    

def update_relbuttons(gw,rb):
    lb,btns = rb
    
    lb.configure(text="State: {}".format(gw.parent.state_label(gw.g.parent_state)))


    # make the grid of buttons scrollable
    # canvas = Canvas(relbuttons, borderwidth=0, background="#ffffff")
    # btns = Frame(canvas, background="#ffffff")
    # vsb = Scrollbar(relbuttons, orient="vertical", command=canvas.yview)
    # canvas.configure(yscrollcommand=vsb.set)
    # vsb.pack(side="right", fill="y")
    # canvas.pack(side="left", fill="both", expand=True)
    # canvas.create_window((4,4), window=btns, anchor="nw")
    # btns.bind("<Configure>", lambda event, canvas=canvas: onFrameConfigure(canvas))

    btns.delete_all()

    btns.add(str(0))
    foo = Label(btns,text = '+')
    btns.item_create(str(0), 0, itemtype='window',window=foo)
    foo = Label(btns,text = '?')
    btns.item_create(str(0), 1, itemtype='window',window=foo)
    foo = Label(btns,text = '-')
    btns.item_create(str(0), 2, itemtype='window',window=foo)
    foo = Label(btns,text = 'T')
    btns.item_create(str(0), 4, itemtype='window',window=foo)
#    rels = list(sorted(enumerate(gw.g.relation_ids),key=lambda r:r[1]))
    rels = enumerate(list(gw.g.relation_ids))
    line_color = gw.line_color
    command = gw.update
    for idx,(num,rel) in enumerate(rels):
        label = gw.g.concept_label(gw.g.concept_from_id(rel))
        btns.add(str(idx+1))
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[0],command=command)
        btns.item_create(str(idx+1), 0, itemtype='window',window=foo)
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[1],command=command)
        btns.item_create(str(idx+1), 1, itemtype='window',window=foo)
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[2],command=command)
        btns.item_create(str(idx+1), 2, itemtype='window',window=foo)
        foo = Label(btns,text=label,fg=line_color(num),justify=LEFT,anchor="w")
        btns.item_create(str(idx+1), 3, itemtype='window',window=foo)
#        foo.bind("<Button-1>", lambda e: askcolor())
        foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[3],command=command)
        btns.item_create(str(idx+1), 4, itemtype='window',window=foo)
#     foo = Label(btns,text = '+')
#     foo.grid(row = 0, column = 0)
#     foo = Label(btns,text = '?')
#     foo.grid(row = 0, column = 1)
#     foo = Label(btns,text = '-')
#     foo.grid(row = 0, column = 2)
#     foo = Label(btns,text = 'T')
#     foo.grid(row = 0, column = 4)
# #    rels = list(sorted(enumerate(gw.g.relation_ids),key=lambda r:r[1]))
#     rels = enumerate(list(gw.g.relation_ids))
#     line_color = gw.line_color
#     command = gw.update
#     for idx,(num,rel) in enumerate(rels):
#         iu.dbg('rel')
#         label = gw.g.concept_label(gw.g.concept_from_id(rel))
#         foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[0],command=command)
#         foo.grid(row = idx+1, column = 0)
#         foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[1],command=command)
#         foo.grid(row = idx+1, column = 1)
#         foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[2],command=command)
#         foo.grid(row = idx+1, column = 2)
#         foo = Label(btns,text=label,fg=line_color(num),justify=LEFT,anchor="w")
#         foo.grid(sticky=W,row = idx+1, column = 3)
# #        foo.bind("<Button-1>", lambda e: askcolor())
#         foo = Checkbutton(btns,fg=line_color(num),variable=gw.get_enabled(rel)[3],command=command)
#         foo.grid(row = idx+1, column = 4)
        

def onFrameConfigure(canvas):
   bbox = canvas.bbox("all")
   canvas.configure(scrollregion=bbox,width=bbox[2]-4)

line_colors = ["black","blue","red","green","VioletRed4","brown1",
"DarkSlateGray4","navy","DeepPink4","DarkOliveGreen4","purple4","RosyBrown4",
"SkyBlue4","tomato4",'DarkSeaGreen4','DarkOrchid2','DarkOrange3',
"DeepSkyBlue4", "IndianRed1", "maroon4", "DarkOrchid3", "chocolate1",
"RoyalBlue1", "OrangeRed4", "green2", "MediumPurple4", "brown4",
]

   


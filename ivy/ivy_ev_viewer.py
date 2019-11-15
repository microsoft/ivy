
import Tix, os, tkFileDialog
import ivy_ev_parser as ev
import ivy_utils as iu
import ivy_ui_util as uu

import signal
signal.signal(signal.SIGINT,signal.SIG_DFL)

Event = ev.Event

class UI(object):
    def __init__(self,tk,root):
        self.tk,self.root = tk,root
                
    def busy(self):
        pass
                
    def ready(self):
        pass

def ask_pat(self,fun,command_label=None):
    global the_ui
    uu.entry_dialog(the_ui.tk,self,"Pattern:",command=lambda s: do_ask_pat(fun,s),command_label=command_label)

def do_ask_pat(fun,pattern):
    global the_ui
    with uu.RunContext(the_ui):
        try:
            pat_evs = ev.parse(pattern)
        except:
            raise iu.IvyError(None,'syntax error')
        fun(pat_evs) 

class EventTree(Tix.Tree,uu.WithMenuBar):
    def __init__(self,root,notebook,evs):
        uu.WithMenuBar.__init__(self,root)
        Tix.Tree.__init__(self,root,options='separator "/"')
        self.evs = evs
        self.notebook = notebook
        for idx,entry in enumerate(evs):
            adddir(self, str(idx) ,entry)

    def menus(self):
        return [("menu","Events",
                 [("button","Filter...",self.filter),
                  ("button","Find reverse...",self.find_reverse),
                 ],
                ),
               ]
                 
    def filter(self):
        ask_pat(self,self.do_filter,"Filter")

    def do_filter(self,pat_evs):
        result = list(ev.filter(ev.EventGen()(self.evs),pat_evs))
        self.notebook.new_sheet(list(result))

    def find_reverse(self):
        ask_pat(self,self.do_find_reverse,"Find")

    def do_find_reverse(self,pats):
        self.do_find(pats,ev.EventRevGen)
         
    def do_find_forward(self,pats):
        self.do_find(pats,ev.EventFwdGen)
         
    def do_find(self,pats,gen):
        sel = self.hlist.info_selection()
        anchor_addr = sel[0] if len(sel) else None
        anchor_ev = lookup(self.evs,anchor_addr) if anchor_addr else None
        res = ev.find(gen(anchor_addr)(self.evs),pats,anchor=anchor_ev)
        if res == None:
            uu.ok_dialog(the_ui.tk,self,'Pattern not found')
            return
        a,e = res
        self.hlist.selection_clear()
        self.uncover(a)
        self.hlist.selection_set(a)
        self.hlist.see(a)

    def uncover(self,addr):
        if '/' in addr:
            cs = addr.rsplit('/',1)
            self.uncover(cs[0])
            opendir(self,cs[0],self.evs)
        
        
class EventNoteBook(Tix.NoteBook):
    def __init__(self,root):
        Tix.NoteBook.__init__(self,root)
        self.num_sheets = 0
        self.root = root
        self.sheets = {}
    def new_sheet(self,evs):
        name = "sht{}".format(self.num_sheets)
        tab = self.add(name,label="Sheet {}".format(self.num_sheets)) 
        self.num_sheets += 1
        tree = EventTree(tab,self,evs)
        tree.pack(expand=1, fill=Tix.BOTH, padx=10, pady=10, side=Tix.LEFT)
        tree.hlist.configure(selectforeground='red')
        tree['opencmd'] = lambda dir=None, w=tree, t=evs: opendir(w, dir, t)
        tree['browsecmd'] = lambda dir=None, w=tree, t=evs: browsedir(w, dir, t)
        self.sheets[name] = tree
        self.raise_page(name)
    def busy(self):
        pass
    def ready(self):
        pass
    def current(self):
        return self.sheets[self.raised()]

class PatternList(Tix.Frame):
    def __init__(self,root,notebook):
        Tix.Frame.__init__(self,root)
        bbox = Tix.Frame(self)
        bts = [Tix.Button(bbox, text=t, command=c) for t,c in [
            ("<<",self.reverse),
            (">>",self.forward),
            ("+",self.plus),
            ("-",self.minus),]]
        bbox.pack(side=Tix.TOP, fill=Tix.X)
        for bt in bts:
            bt.pack(side=Tix.LEFT, fill=Tix.X)
        tlist = Tix.TList(self)
        tlist.pack(expand=1, fill=Tix.BOTH, pady=10, side=Tix.TOP)
        bbox = Tix.Frame(self)
        bts = [Tix.Button(bbox, text=t, command=c) for t,c in [
            ("Save",self.save),
            ("Load",self.load),
            ("Clear",self.clear),]]
        bbox.pack(side=Tix.TOP, fill=Tix.X)
        for bt in bts:
            bt.pack(side=Tix.LEFT, fill=Tix.X)
        self.tlist = tlist
        self.patlist = []
        self.notebook = notebook
        
    def reverse(self):
        sel = self.tlist.info_selection()
        if len(sel):
            item = int(sel[0])
            self.notebook.current().do_find_reverse(self.patlist[item])
    
    def forward(self):
        sel = self.tlist.info_selection()
        if len(sel):
            item = int(sel[0])
            self.notebook.current().do_find_forward(self.patlist[item])
    
    def plus(self):
        ask_pat(self,self.do_plus,command_label="Add")

    def do_plus(self,pats):
        self.tlist.insert("end",text=str(pats))
        self.patlist.append(pats)
        
    def minus(self):
        pass

    def save(self):
        f = tkFileDialog.asksaveasfile(mode='w',filetypes=[('event pattern files', '.pats')],title="Save patterns as...",parent=self)
        if f:
            for p in self.patlist:
                f.write('{}\n'.format(p))
            f.close()
                
    def load(self):
        f = tkFileDialog.askopenfile(mode='r',filetypes=[('event pattern files', '.pats')],title="Load patterns from...",parent=self)
        if f:
            for pat in f.readlines():
                do_ask_pat(self.do_plus,pat)
                
    def clear(self):
        pass

def RunSample(w,evs):
    top = Tix.Frame(w, relief=Tix.RAISED, bd=1)
    global the_ui
    the_ui = UI(w,top)
    notebook = EventNoteBook(top)
    notebook.pack(side=Tix.LEFT, fill=Tix.BOTH,expand=1)
    notebook.new_sheet(evs)
    pats = PatternList(top,notebook)
    pats.pack(expand=1, fill=Tix.BOTH, padx=10, side=Tix.LEFT)
    top.pack(side=Tix.LEFT, fill=Tix.BOTH, expand=1)
    


def adddir(tree, dir, thing):
    text = thing.text()
#    tree.hlist.add(dir, itemtype=Tix.IMAGETEXT, text=text,
#                   image=tree.tk.call('tix', 'getimage', 'folder'))
    tree.hlist.add(dir, text=text)
    if thing.subs:
        tree.setmode(dir, 'open')

def lookup(things,dir):
    cs = dir.split('/',1)
    thing = things[int(cs[0])]
    res = thing if len(cs) == 1 else lookup(thing.subs,cs[1])
    return res

# This function is called whenever the user presses the (+) indicator or
# double clicks on a directory whose mode is "open". It loads the files
# inside that directory into the Tree widget.
#
# Note we didn't specify the closecmd option for the Tree widget, so it
# performs the default action when the user presses the (-) indicator or
# double clicks on a directory whose mode is "close": hide all of its child
# entries
def opendir(tree, dir, evs):
    entries = tree.hlist.info_children(dir)
    if entries:
        # We have already loaded this directory. Let's just
        # show all the child entries
        #
        # Note: since we load the directory only once, it will not be
        #       refreshed if the you add or remove files from this
        #       directory.
        #
        for entry in entries:
            tree.hlist.show_entry(entry)
        return
    files = lookup(evs,dir).subs
    for idx,file in enumerate(files):
        adddir(tree, dir + '/' + str(idx),file)

def browsedir(tree, dir, evs):
    pass

def main():
    import sys
    def usage():
        print "usage: \n  {} <file>.iev ".format(sys.argv[0])
        sys.exit(1)
    if len(sys.argv) != 2:
        usage()
        exit(1)
    fn = sys.argv[1]
    import chardet # $ pip install chardet
    try:
        f = open(fn,'r')
    except:
        print "not found: %s" % fn
        sys.exit(1)

    with iu.ErrorPrinter():
        with iu.SourceFile(fn):
            s = f.read()
            evs = ev.parse(s)
    global tk
    tk = Tix.Tk()
    RunSample(tk,evs)
    tk.mainloop()

if __name__ == '__main__':
    main()


import Tix, os
import ivy_ev_parser as ev
import ivy_utils as iu
import ivy_ui_util as uu

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
        sel = self.hlist.info_selection()
        if len(sel):
            anchor = sel[0]
            ask_pat(self,lambda pats: self.do_find_reverse(anchor,pats),"Find")

    def do_find_reverse(self,anchor,pats):
        a,e = ev.find(ev.EventRevGen(anchor)(self.evs),pats,anchor=lookup(self.evs,anchor))
        print a + ':' + str(e)
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
    def new_sheet(self,evs):
        name = "sht{}".format(self.num_sheets)
        tab = self.add(name,label="Sheet {}".format(self.num_sheets)) 
        self.num_sheets += 1
        tree = EventTree(tab,self,evs)
        tree.pack(expand=1, fill=Tix.BOTH, padx=10, pady=10, side=Tix.LEFT)
        tree.hlist.configure(selectforeground='red')
        tree['opencmd'] = lambda dir=None, w=tree, t=evs: opendir(w, dir, t)
        tree['browsecmd'] = lambda dir=None, w=tree, t=evs: browsedir(w, dir, t)
        self.raise_page(name)
    def busy(self):
        pass
    def ready(self):
        pass
        
        

def RunSample(w,evs):
    top = Tix.Frame(w, relief=Tix.RAISED, bd=1)
    global the_ui
    the_ui = UI(w,top)
    notebook = EventNoteBook(top)
    notebook.pack(side=Tix.LEFT, fill=Tix.BOTH,expand=1)
    notebook.new_sheet(evs)
    tlist = Tix.TList(top)
    tlist.pack(expand=1, fill=Tix.BOTH, padx=10, pady=10, side=Tix.LEFT)
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

if __name__ == '__main__':
    
    import sys
    def usage():
        print "usage: \n  {} <file>.iev ".format(sys.argv[0])
        sys.exit(1)
    if len(sys.argv) != 2:
        usage()
        exit(1)
    fn = sys.argv[1]
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

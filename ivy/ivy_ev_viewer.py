
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
                 [("button","Filter",self.filter),
                 ],
                ),
               ]
                 
    def filter(self,pattern=None):
        global tk
        global the_thing
        if pattern == None:
            uu.entry_dialog(tk,self,"Pattern:",command=self.filter,command_label="Filter")
        else:
            global the_ui
            with uu.RunContext(the_ui):
                try:
                    pat_evs = ev.parse(pattern)
                except:
                    raise iu.IvyError(None,'syntax error')
                result = list(ev.filter(ev.EventGen()(self.evs),pat_evs))
                for r in result:
                    print r
                self.notebook.new_sheet(list(result))

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
        tree.hlist.configure(selectforeground='black')
        tree['opencmd'] = lambda dir=None, w=tree, t=evs: opendir(w, dir, t)
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
    notebook.pack(fill=Tix.BOTH,expand=1)
    notebook.new_sheet(evs)
    top.pack(side=Tix.TOP, fill=Tix.BOTH, expand=1)
    


def adddir(tree, dir, thing):
    text = thing.text()
#    tree.hlist.add(dir, itemtype=Tix.IMAGETEXT, text=text,
#                   image=tree.tk.call('tix', 'getimage', 'folder'))
    tree.hlist.add(dir, text=text)
    if thing.subs:
        tree.setmode(dir, 'open')

def lookup(things,dir):
    cs = dir.split('/',1)
    print "cs:{}".format(cs)
    thing = things[int(cs[0])]
    res = thing if len(cs) == 1 else lookup(thing.subs,cs[1])
    print 'dir: {}'.format(dir)
    print 'res: {}'.format(res)
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
    print "files: {}".format(files)
    for idx,file in enumerate(files):
        adddir(tree, dir + '/' + str(idx),file)


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
    print evs
    global tk
    tk = Tix.Tk()
    RunSample(tk,evs)
    tk.mainloop()

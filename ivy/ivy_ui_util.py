#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from Tkinter import *
import Tkconstants, tkFileDialog
import Tix
import ivy_utils as iu
import functools

class MenuBar(Frame):
    def __init__(self,root):
        Frame.__init__(self,root)
        foo = Frame(self)
        foo.pack(side=RIGHT,expand=1)
    def add(self,label):
        w = Menubutton(self,text=label)
        w.pack(side=LEFT)
        m = Menu(w, tearoff=0)
        w.config(menu=m)
        return m

class WithMenuBar(object):
    def __init__(self,root):

        self.radios = {}

        menubar = MenuBar(root)
        menubar.pack(side=TOP,fill=X)
        for mtype,mname,mcontents in self.menus():
            menu = menubar.add(mname)
            for mitem in mcontents:
                itype = mitem[0]
                if itype == "button":
                    menu.add_command(label=mitem[1],command=mitem[2])
                elif itype == "separator":
                    menu.add_separator()
                elif itype == "radiobuttons":
                    ivar = StringVar(root,mitem[2])
                    self.radios[mitem[1]] = ivar
                    for rblabel,rbvalue in mitem[3]:
                        menu.add("radiobutton",label=rblabel,variable=ivar,value=rbvalue)
                else:
                    assert False,itype

    def radiobutton(self,name):
        return self.radios[name]

class FileBrowser(Frame):
    def __init__(self,root):
        Frame.__init__(self,root)
        S = Scrollbar(self)
        T = Text(self, height=20, width=100)
        S.pack(side=RIGHT, fill=Y)
        T.pack(side=LEFT, fill=BOTH, expand=1)
        S.config(command=T.yview)
        T.config(yscrollcommand=S.set)
        self.text = T
        self.filename = None
        self.lineno = None
    def set(self,filename,lineno):
        if filename != self.filename:
            f = open(filename,'rU')
            if not f:
                raise IvyError(None,"file {} not found".format(filename))
            self.filename = filename
            self.text.delete("1.0","end")
            self.text.insert(END,f.read())
        self.text.tag_config('highlight', background='red')
        self.text.tag_remove('highlight', "1.0", "end")
        self.text.tag_add('highlight', "{}.0".format(lineno), "{}.0 lineend".format(lineno))
        self.text.see("{}.0".format(lineno))
        self.winfo_toplevel().lift()
#        self.text.iconify()
#        self.text.deiconify()

def new_file_browser(tk):
    tl = Toplevel(tk)
    fb = FileBrowser(tl)
    fb.pack(fill=BOTH,expand=1)
    return fb

def center_window(toplevel):
    toplevel.update_idletasks()
    w = toplevel.winfo_screenwidth()
    h = toplevel.winfo_screenheight()
    size = tuple(int(_) for _ in toplevel.geometry().split('+')[0].split('x'))
    x = w/2 - size[0]/2
    y = h/2 - size[1]/2
    toplevel.geometry("%dx%d+%d+%d" % (size + (x, y)))

def center_window_on_window(toplevel,win):
    win = win.winfo_toplevel()
    toplevel.update_idletasks()
    wg = win.geometry().split('+')
    wx,wy = map(int,wg[1:3])
    wxs,wys = map(int,wg[0].split('x'))
    xc = wx + wxs/2
    yc = wy + wys/2
    size = tuple(int(_) for _ in toplevel.geometry().split('+')[0].split('x'))
    x = xc - size[0]/2
    y = yc - size[1]/2
    toplevel.geometry("%dx%d+%d+%d" % (size + (x, y)))

def destroy_then_aux(dlg,command):
    command()
    dlg.destroy()

def destroy_then(dlg,command):
    return functools.partial(destroy_then_aux,dlg,command)

def destroy_then_command_on_selection_aux(dlg,lbox,command,mult):
    sel = map(int, lbox.curselection())
    dlg.destroy()
    if sel:
        command(sel if mult else sel[0])

def destroy_then_command_on_selection(dlg,lbox,command,mult):
    return functools.partial(destroy_then_command_on_selection_aux,dlg,lbox,command,mult)

def listbox_dialog(tk,root,msg,items,command=lambda:None,on_cancel=lambda:None,multiple=False):
    dlg = Toplevel(root)
    Label(dlg, text=msg).pack()
    S = Scrollbar(dlg)
    T = Listbox(dlg, height=8, width=50, selectmode=SINGLE)
    S.pack(side=RIGHT, fill=Y)
    T.pack(side=LEFT, fill=BOTH,expand=1)
    S.config(command=T.yview)
    T.config(yscrollcommand=S.set)
    for item in items:
        T.insert(END, item)
    b = Button(dlg, text="OK", command=destroy_then_command_on_selection(dlg,T,command,multiple))
    b.pack(padx=5,side=TOP)
    if on_cancel != None:
        b = Button(dlg, text="Cancel", command=destroy_then(dlg,on_cancel))
        b.pack(padx=5,side=TOP)
    center_window_on_window(dlg,root)
    tk.wait_window(dlg)


def text_dialog(tk,root,msg,text,command=lambda:None,on_cancel=lambda:None,command_label=None,ans=None):
    dlg = Toplevel(root)
    Label(dlg, text=msg).pack()
    S = Scrollbar(dlg)
    T = Text(dlg, height=4, width=100)
    S.pack(side=RIGHT, fill=Y)
    T.pack(side=LEFT, fill=Y)
    S.config(command=T.yview)
    T.config(yscrollcommand=S.set)
    T.insert(END, text)
    lbl = command_label or "OK"
    b = Button(dlg, text=lbl, command=destroy_then(dlg,command))
    b.pack(padx=5,side=TOP)
    buttons = {lbl:b}
    if on_cancel != None:
        b = Button(dlg, text="Cancel", command=destroy_then(dlg,on_cancel))
        b.pack(padx=5,side=TOP)
        buttons["Cancel"] = b
    center_window_on_window(dlg,root)
    if ans:
        buttons[ans].invoke()
        return
    tk.wait_window(dlg)

def entry_dialog(tk,root,msg,command=lambda:None,on_cancel=lambda:None,command_label=None,initval=None):
    dlg = Toplevel(root)
    Label(dlg, text=msg).pack()
    e = Entry(dlg)
    if initval is not None:
        e.insert(0,str(initval))
    e.focus()
    e.pack()
    action = destroy_then(dlg,lambda command=command, e=e: command(e.get()))
    e.bind('<Return>', lambda q,action=action: action())
    lbl = command_label or "OK"
    Button(dlg, text=lbl,command=action).pack(padx=5,side=TOP)
    if on_cancel != None:
        b = Button(dlg, text="Cancel", command=destroy_then(dlg,on_cancel)).pack(padx=5,side=TOP)
    center_window_on_window(dlg,root)
    tk.wait_window(dlg)

def _convert_to_int(s,minval,maxval):
    try:
        v = int(s)
    except:
        raise IvyError(None,'Entered value "{}" is not an integer'.format(s))
    if (minval and v < minval) or (maxval and v > maxval):
        raise IvyError(None,'Entered value "{}" is out of range'.format(v))
    return v

def int_dialog(tk,root,msg,minval=None,maxval=None,command=lambda:None,**kwargs):
    action = lambda s: command(_convert_to_int(s,minval,maxval))
    entry_dialog(tk,root,msg,command=action,**kwargs)

def ok_cancel_dialog(tk,root,msg,command=lambda:None,on_cancel=lambda:None,ans=None):
    dlg = Toplevel(root)
    Label(dlg, text=msg).pack()
    buttons = {}
    b = Button(dlg, text="OK", command=destroy_then(dlg,command))
    b.pack(padx=5,side=TOP)
    buttons["OK"] = b
    b = Button(dlg, text="Cancel", command=destroy_then(dlg,on_cancel))
    b.pack(padx=5,side=TOP)
    buttons["Cancel"] = b
    center_window_on_window(dlg,root)
    if ans:
        buttons[ans].invoke()
        return
    tk.wait_window(dlg)

def ok_dialog(tk,root,msg,ans=None):
    dlg = Toplevel(root)
    Label(dlg, text=msg).pack()
    b = Button(dlg, text="OK", command=dlg.destroy)
    b.pack(padx=5,side=TOP)
    center_window_on_window(dlg,root)
    if ans:
        b.invoke()
        return
    tk.wait_window(dlg)

def buttons_dialog_cancel(tk,root,msg,button_commands,on_cancel=lambda:None,ans=None):
    dlg = Toplevel(root)
    Label(dlg, text=msg).pack()
    buttons = {}
    for text,command in button_commands:
        b = Button(dlg, text=text, command=destroy_then(dlg,command))
        b.pack(padx=5,side=TOP)
        buttons[text] = b
    b = Button(dlg, text="Cancel", command=destroy_then(dlg,on_cancel))
    b.pack(padx=5,side=TOP)
    buttons["Cancel"]=b
    center_window_on_window(dlg,root)
    if ans:
        buttons[ans].invoke()
        return
    tk.wait_window(dlg)


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
        if isinstance(exc_val,iu.IvyError): # exc_type == iu.IvyError:
            dlg = Toplevel(self.parent.root)
            Label(dlg, text=repr(exc_val)).pack(side=TOP)
            b = Button(dlg, text="OK", command=dlg.destroy)
            b.pack(padx=5,side=TOP)
            center_window_on_window(dlg,self.parent.root)
            self.parent.tk.wait_window(dlg)
            return True
        return False # don't block any exceptions



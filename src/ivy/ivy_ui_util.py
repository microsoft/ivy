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

def center_window(toplevel):
    toplevel.update_idletasks()
    w = toplevel.winfo_screenwidth()
    h = toplevel.winfo_screenheight()
    size = tuple(int(_) for _ in toplevel.geometry().split('+')[0].split('x'))
    x = w/2 - size[0]/2
    y = h/2 - size[1]/2
    toplevel.geometry("%dx%d+%d+%d" % (size + (x, y)))

def center_window_on_window(toplevel,win):
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
    dlg.destroy()
    command()

def destroy_then(dlg,command):
    return functools.partial(destroy_then_aux,dlg,command)

def destroy_then_command_on_selection_aux(dlg,lbox,command):
    sel = map(int, lbox.curselection())
    dlg.destroy()
    if sel:
        command(sel[0])

def destroy_then_command_on_selection(dlg,lbox,command):
    return functools.partial(destroy_then_command_on_selection_aux,dlg,lbox,command)

def listbox_dialog(tk,root,msg,items,command=lambda:None,on_cancel=lambda:None):
    dlg = Toplevel(root)
    Label(dlg, text=msg).pack()
    S = Scrollbar(dlg)
    T = Listbox(dlg, height=8, width=50, selectmode=SINGLE)
    S.pack(side=RIGHT, fill=Y)
    T.pack(side=LEFT, fill=Y)
    S.config(command=T.yview)
    T.config(yscrollcommand=S.set)
    for item in items:
        T.insert(END, item)
    b = Button(dlg, text="OK", command=destroy_then_command_on_selection(dlg,T,command))
    b.pack(padx=5,side=TOP)
    b = Button(dlg, text="Cancel", command=destroy_then(dlg,on_cancel))
    b.pack(padx=5,side=TOP)
    center_window_on_window(dlg,root)
    tk.wait_window(dlg)

def ok_cancel_dialog(tk,root,msg,command=lambda:None,on_cancel=lambda:None):
    dlg = Toplevel(root)
    Label(dlg, text=msg).pack()
    b = Button(dlg, text="OK", command=destroy_then(dlg,command))
    b.pack(padx=5,side=TOP)
    b = Button(dlg, text="Cancel", command=destroy_then(dlg,on_cancel))
    b.pack(padx=5,side=TOP)
    center_window_on_window(dlg,root)
    tk.wait_window(dlg)

def ok_dialog(tk,root,msg):
    dlg = Toplevel(root)
    Label(dlg, text=msg).pack()
    b = Button(dlg, text="OK", command=dlg.destroy)
    b.pack(padx=5,side=TOP)
    center_window_on_window(dlg,root)
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
        if exc_type == iu.IvyError:
            dlg = Toplevel(self.parent)
            Label(dlg, text=repr(exc_val)).pack(side=TOP)
            b = Button(dlg, text="OK", command=dlg.destroy)
            b.pack(padx=5,side=TOP)
            center_window_on_window(dlg,self.parent.root)
            self.parent.tk.wait_window(dlg)
            return True
        return False # don't block any exceptions



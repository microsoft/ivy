
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu
from ivy import ivy_interp as itp
from ivy import ivy_isolate as ivy_isolate
from ivy import ivy_check as ick

prog = """#lang ivy1.6

type s
interpret s -> strlit

individual x:s
property [foo] ~(x = "0"  & x = "1")



"""

with im.Module():
    iu.set_parameters({'mode':'induction','show_compiled':'true'})
    ivy_from_string(prog,create_isolate=False)
    try:
        ick.check_module()
    except iu.IvyError as e:
        print str(e)
        assert False,"property should have been true"

    
    # with im.module.copy():
    #     ivy_isolate.create_isolate(None) # ,ext='ext'
    #     gui = new_ui()
    #     gui.tk.update_idletasks() # so that dialog is on top of main window
    #     gui.try_property()
    #     gui.mainloop()




from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu
from ivy import ivy_interp as itp
from ivy import ivy_isolate as ivy_isolate
from ivy import ivy_check as ick

prog = """#lang ivy1.6

type s

object foo = {
    property [p1] forall X:s. X = X
}

object bar = {
    property [p2] X:s = Y:s
}

isolate iso_foo = foo
isolate iso_bar = bar


"""

with im.Module():
    iu.set_parameters({'mode':'induction','show_compiled':'true'})
    ivy_from_string(prog,create_isolate=False)
    try:
        ick.check_module()
        assert False,"property should have been false"
    except iu.IvyError as e:
        print str(e)
        assert str(e) == 'error: failed checks: 1'

    
    # with im.module.copy():
    #     ivy_isolate.create_isolate(None) # ,ext='ext'
    #     gui = new_ui()
    #     gui.tk.update_idletasks() # so that dialog is on top of main window
    #     gui.try_property()
    #     gui.mainloop()



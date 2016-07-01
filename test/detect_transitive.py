
import ivy.ivy_module as ivy_module
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
import ivy.ivy_utils as iu

prog = """#lang ivy1.3

type t

relation le(X : t, Y : t)

axiom le(X,Y) & le(Y,Z) -> le(X,Z)
axiom le(X,X)

"""

with ivy_module.Module():
    iu.set_parameters({'ui':'cti','ext':'ext'})
    main_ui = new_ui()
    ui = main_ui.add(ivy_from_string(prog))
#    ui.mainloop()



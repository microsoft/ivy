
import ivy.ivy_module as ivy_module
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
import ivy.ivy_utils as iu

prog = """#lang ivy1.3

type t
type color = {red,green,blue}

individual c(X:t):color
relation p(X:t)

init p(X) -> c(X) = green

"""

with ivy_module.Module():
    main_ui = new_ui()
    ui = main_ui.add(ivy_from_string(prog))
    cg = ui.view_state(ui.g.states[0])
    t = cg.node('t')
    s = cg.relation('c')
    cg.split(s,t)
    g = cg.node('c=green')
    p = cg.relation('p')
    cg.split(p,g)
#    ui.mainloop()



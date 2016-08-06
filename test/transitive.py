
import ivy.ivy_module as ivy_module
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
import ivy.ivy_utils as iu

prog = """#lang ivy1.3

type t

relation (X:t < Y:t)

axiom X:t < Y:t & Y < Z -> X < Y

individual x:t, y:t, z:t

init x < y & y < z

"""

with ivy_module.Module():
    main_ui = new_ui()
    ui = main_ui.add(ivy_from_string(prog))
    cg = ui.view_state(ui.node(0))
    cg.show_relation(cg.relation('X:t < Y'),'+')
    cg.split(cg.relation('=x'),cg.node('t'))
    cg.show_relation(cg.relation('=x'),'-')
    cg.split(cg.relation('=y'),cg.node('~=x'))
    cg.show_relation(cg.relation('=y'),'-')
    cg.split(cg.relation('=z'),cg.node('~=x','~=y'))
#    ui.mainloop()



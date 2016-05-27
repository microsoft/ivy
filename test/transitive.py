
import ivy_module
from ivy_compiler import ivy_from_string
from tk_ui import new_ui

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
    cg.show_relation(cg.relation('X:t < Y:t'),'+')
    cg.split(cg.relation('=x'),cg.node('t'))
    cg.show_relation(cg.relation('=x'),'-')
    cg.split(cg.relation('=y'),cg.node('~=x'))
    cg.show_relation(cg.relation('=y'),'-')
    cg.split(cg.relation('=z'),cg.node('~=x','~=y'))
#    ui.mainloop()



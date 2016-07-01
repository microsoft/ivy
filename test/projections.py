
import ivy.ivy_module as ivy_module
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
import ivy.ivy_utils as iu

prog = """#lang ivy1.5

type t

relation r(X:t,Y:t,Z:t)

individual x:t,y:t,z:t

init ~r(X:t,Y:t,Z:t)

type q

function f(X:t,Y:t):q
init f(X,Y) = 0

action foo = {
    r(x,y,z) := true
}
"""

with ivy_module.Module():
    main_ui = new_ui()
    ui = main_ui.add(ivy_from_string(prog))
    ui.execute_action(ui.node(0),"foo")
    cg = ui.view_state(ui.g.states[1])
    cex = cg.path_reach()
    assert cex != None
    vs = cex.view_state(cex.g.states[1])
    vs.show_relation(vs.relation('=x'))
    acts = vs.get_node_projection_actions(vs.node('=x'))
    assert len(acts) > 2
    acts[2][1](None)
    vs.show_relation(vs.relation('f(0,Y) = Z'))
#    ui.mainloop()



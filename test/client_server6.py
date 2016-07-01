
import ivy.ivy_module as ivy_module
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
import ivy.ivy_utils as iu

prog = """#lang ivy1.5

type client
type server

relation link(X:client, Y:server)
relation semaphore(X:server)

init semaphore(W) & ~link(X,Y)

action connect(x:client,y:server) = {
  assume semaphore(y);
  link(x,y) := true;
  semaphore(y) := false
}

action disconnect(x:client,y:server) = {
  assume link(x,y);
  link(x,y) := false;
  semaphore(y) := true
}

action test = {
  assert ~(X ~= Z & link(X,Y) & link(Z,Y))
}

export connect
export disconnect
export test
"""

with ivy_module.Module():
    iu.set_parameters({'ui':'cti','ext':'ext'})
    main_ui = new_ui()
    ui = main_ui.add(ivy_from_string(prog))
    main_ui.answer("OK")
    ui.check_inductiveness()
#    ui = ui.cti
    cg = ui.current_concept_graph
    cg.show_relation(cg.relation('link(X,Y)'),'+')
    cg.gather()
    main_ui.answer("OK")
    cg.strengthen()
    main_ui.answer("OK")
    ui.check_inductiveness()
#    cg.show_relation(cg.relation('semaphore'),'+')
    cg.gather()
    main_ui.answer("View")
    cg.bmc_conjecture(bound=1)
#    main_ui.mainloop()



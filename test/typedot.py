
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu

prog = """#lang ivy1.5

object obj = {
    type t
}

relation r(X:obj.t)

action a(x:obj.t) = {
local y:obj.t {
  if some z:s. z = z {
    y := y
}
}
}

type s

axiom forall X:s. X = X

"""

with im.Module():
    iu.set_parameters({'ui':'cti','ext':'ext','show_compiled':'true'})
    main_ui = new_ui()
    ui = main_ui.add(ivy_from_string(prog))
#     main_ui.answer("OK")
#     ui.check_inductiveness()
# #    ui = ui.cti
#     cg = ui.current_concept_graph
#     cg.show_relation(cg.relation('link(X,Y)'),'+')
#     cg.gather()
#     main_ui.answer("OK")
#     cg.strengthen()
#     main_ui.answer("OK")
#     ui.check_inductiveness()
# #    cg.show_relation(cg.relation('semaphore'),'+')
#     cg.gather()
#     main_ui.answer("View")
#     cg.bmc_conjecture(bound=1)
# #    main_ui.mainloop()



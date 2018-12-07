
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu

prog = """#lang ivy1.5

type foo
type bar

module mod(me) = {
  relation r
  individual x:foo
  init x = me

  action thing(y:foo) = {
    x := me
  }

  action set_me(y:foo) = {
    r := true;
    call thing(y)
  }

  conjecture r -> x = me
}

instance inst(X:foo) : mod(X)

axiom inst(X).r & inst(X).x = X

isolate iso(me:foo) = inst(me)

export inst.set_me
"""

with im.Module():
    iu.set_parameters({'ui':'cti','ext':'ext','isolate':'iso','show_compiled':'true'})
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




from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu
from ivy import ivy_check as ick
prog = """#lang ivy1.5

type foo
type bar

module mod(me) = {
  relation r
  individual x:foo
  init x = me

  action set_me(y:foo) = {
    call baz.thing(y);
    r := true
  }

  object baz = {
     
    action thing(y:foo) = {
      x := me
    }
  }
  private baz

  conjecture r -> x = me
}

instance inst(X:foo) : mod(X)

isolate iso(me:foo) = inst(me) with inst(me).baz

export inst.set_me
"""

with im.Module():
    iu.set_parameters({'mode':'induction','diagnose':'true','show_compiled':'true'})
    ivy_from_string(prog,create_isolate=False)
    ick.check_module()

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



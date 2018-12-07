
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

  action thing(y:foo) = {
    x := me
  }

  action set_me(y:foo) = {
    x := y;
    r := true
  }

  conjecture r -> x = me
}

instance inst(X:foo) : mod(X)

isolate iso(me:foo) = inst(me)

export inst.set_me
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



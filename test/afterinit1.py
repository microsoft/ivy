
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu

prog = """#lang ivy1.6

type t

individual x(X:t) : t

object foo(me:t) = {
    after init {
        x(me) := me;
        assert false
    }
}

isolate iso_foo(me:t) = foo(me) with x(me)

"""

with im.Module():
    iu.set_parameters({'mode':'induction','isolate':'iso_foo','show_compiled':'true'})
    main_ui = new_ui()
    ui = main_ui.add(ivy_from_string(prog))
    main_ui.tk.update_idletasks()    
    main_ui.answer("OK")
    ui.check_safety_node(ui.node(0))
    assert not ui.node(0).safe
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
#    main_ui.mainloop()



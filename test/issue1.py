
import ivy.ivy_module as ivy_module
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
import ivy.ivy_utils as iu

prog = """#lang ivy1.5

type s
relation p(X:s)
individual v:s

relation error
init ~error
conjecture ~error

action f returns (u:s) = {
    assume p(u)
}

action action1 = {
    error := true;
    v := *;
    assume ~p(v);
    v := f
}

action action2 = {
    v := f;
    v := *
}

export action1
export action2
"""

with ivy_module.Module():
    iu.set_parameters({'ui':'cti','ext':'ext'})
    main_ui = new_ui()
    ui = main_ui.add(ivy_from_string(prog))
    main_ui.answer("OK")
    if ui.check_inductiveness():
        assert False,"should not have been inductive"
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



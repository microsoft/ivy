
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu
from ivy import ivy_check as ick
from ivy import ivy_logic as il

prog = """#lang ivy1.5

type t
type p

relation sent(X:p,Y:t)
function pid(X:t):p

axiom X:t = X
axiom X:t < Y & Y < Z -> X < Z
axiom X:t = Y + 0
axiom X:t = Y + Z
axiom X = (Y:t + 1) if (Y = Z) else 0
axiom forall X,Y,Z. X:t < Y & Y < Z -> X < Z
axiom forall NO0:t,NO1:t. ~(pid(NO0:t) < pid(NO1:t) & sent(pid(NO0:t),NO0:t))
"""

with im.Module():
    iu.set_parameters({'mode':'induction','show_compiled':'true'})
    ivy_from_string(prog,create_isolate=False)
    for adecl in im.module.labeled_axioms:
        f = adecl.args[1]
        print
        print str(f)
        print il.to_str_with_var_sorts(f)
        print il.fmla_to_str_ambiguous(f)

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



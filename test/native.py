
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu
#from ivy import ivy_check as ick
from ivy import ivy_logic as il
from ivy import ivy_to_cpp as i2c
from ivy import ivy_actions as ia
from ivy import ivy_solver as slv
from ivy import ivy_isolate as iso
from ivy import ivy_cpp

prog = """#lang ivy1.5

module bar = {

    object foo = {}

    <<<
        int `foo`;
    >>>

    action incr = {
        <<<
            `foo`++;
        >>>
    }

}

type t
interpret t -> {0..1} 
instance baz(X:t) : bar

"""

ia.set_determinize(True)
slv.set_use_native_enums(True)
iso.set_interpret_all_sorts(True)

with im.Module():
    iu.set_parameters({'mode':'induction','show_compiled':'true','target':'impl'})
    ivy_from_string(prog,create_isolate=True)

    classname = 'foo'
    with ivy_cpp.CppContext():
        header,impl = i2c.module_to_cpp_class(classname,classname)
    print header
    print impl

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



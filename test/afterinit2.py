
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu
from ivy import ivy_check as ick
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
    ivy_from_string(prog,create_isolate=False)
    try:
        ick.check_module()
        assert False,"safety should have failed"
    except iu.IvyError as e:
        print e
        assert str(e) == "error: failed checks: 1"

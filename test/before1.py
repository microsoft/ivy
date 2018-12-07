
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu
from ivy import ivy_check as ick
prog = """#lang ivy1.5

type foo
type bar

individual x : foo
# individual y : foo

action a(z:foo,y:foo) = {
  x := y
}

object m(me:foo) = {
    after a {
       assert x = y | x = me
    }
}


export a
"""

with im.Module():
    iu.set_parameters({'mode':'induction','show_compiled':'true'})
    ivy_from_string(prog,create_isolate=False)
    ick.check_module()





from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu
from ivy import ivy_check as ick

prog = """#lang ivy1.6

type t

relation (X:t < Y:t)

individual x:t,y:t

axiom x <= y

action a = {
  assert y > x | x = y
}

export a

"""

with im.Module():
    iu.set_parameters({'mode':'induction','show_compiled':'true'})
    ivy_from_string(prog,create_isolate=False)
    ick.check_module()



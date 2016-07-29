
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu
from ivy import ivy_check as ick

prog = """#lang ivy1.5

type foo
type bar

individual v : foo
individual w : foo
individual x : foo

object p = {
  action a = {
    call q.c
  }
}

object q = {
  action b = {
    call p.a;
    assert v = w
  }
  action c = {
    v := w
  }
}

object s = {
  action a = {
    assert v = w
  }
  execute a after p.a
}


isolate iso_q = q with s

export q.b
"""

with im.Module():
    iu.set_parameters({'mode':'induction'})
    ivy_from_string(prog,create_isolate=False)
    try:
        ick.check_module()
    except iu.IvyError as e:
        assert str(e) == "error: Some assertions are not checked","should have been an error"



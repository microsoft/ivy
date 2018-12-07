
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
    v := x
  }
}

object s = {
  action a = {
    v := w
  }
  execute a before p.a
}

isolate iso = q with s

export q.b
"""

with im.Module():
    iu.set_parameters({'mode':'induction','diagnose':'true','show_compiled':'true'})
    ivy_from_string(prog,create_isolate=False)
    try:
        ick.check_module()
        assert "should have raised error"
    except iu.IvyError as e:
        assert str(e) == 'line 18: error: Call to p.a may cause interfering callback to q.c'



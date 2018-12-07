
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy import ivy_utils as iu
prog = """#lang ivy1.6

type t

type s1 = struct {
    foo : t,
    bar : t
}

type s2 = struct {
    baz : s1,
    bif : t
} 

individual w : t
individual v : s2

action a = {
   v.baz.foo := w
}

export a
"""

with im.Module():
    iu.set_parameters({'show_compiled':'true'})
    ivy_from_string(prog,create_isolate=False)
    print im.module.actions["a"].update(im.module,{})


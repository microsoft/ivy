
from ivy import ivy_module as im
from ivy.ivy_compiler import ivy_from_string
from ivy.tk_ui import new_ui
from ivy import ivy_utils as iu
from ivy import ivy_check as ick
prog = """#lang ivy1.5
type packet

object intf = {
    action send(x:packet)
    action recv(x:packet)
}


object spec = {
    relation sent(X:packet)
    init ~sent(X)

    before intf.send {
	sent(x) := true
    }

    before intf.recv {
	assert sent(x)
    }
}


object protocol = {
    implement intf.send {
	call intf.recv(x)
    }
}

import intf.recv
export intf.send
"""

with im.Module():
    iu.set_parameters({'mode':'induction','show_compiled':'true'})
    ivy_from_string(prog,create_isolate=False)
    ick.check_module()




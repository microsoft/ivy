
import ivy_module
from ivy_compiler import ivy_from_string
from tk_ui import new_ui
import ivy_utils as iu

prog = """#lang ivy1

type client
type server

relation c(X : client,Y : server)
relation s(X : server)

init (s(W) & ~c(X,Y))
individual x : client,y : server,z : client

derived foo(X:client,Y:server) = c(X,Y) & ~s(Y)

action connect = {
  x := *;
  y := *;
  assume s(y) & ~c(x,Z);
  c(x,y) := true;
  s(y) := false
}

action disconnect = {
  x := *;
  y := *;
  assume c(x,y);
  c(x,y) := false;
  s(y) := true
}

action error = {
  x := *;
  y := *;
  z := *;
  assume x ~= z & c(x,y) & c(z,y)
}

# concept c1(X,Y,Z) = (c(X,Z) * ~X = Y * c(Y,Z))

conjecture (X = Z | ~c(X,Y) | ~c(Z,Y))
"""

with ivy_module.Module():
    iu.set_parameters({'ui':'cti','ext':'ext'})
    main_ui = new_ui()
    ui = main_ui.add(ivy_from_string(prog))
    ui.check_inductiveness()
#    ui = ui.cti
    cg = ui.current_concept_graph
    iu.dbg('type(cg)')
    cg.show_relation(cg.relation('s'),'+')
    cg.gather() 
#    cg.select_fact(cg.fact('1 ~= 0'),False)
#    cg.select_fact(cg.fact('0 ~= 1'),False)
#    cg.is_inductive()
#    cg.is_sufficient()
    cg.minimize_conjecture(bound=2)
    ui.mainloop()



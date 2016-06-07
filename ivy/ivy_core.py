#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
# TODO get rid of import *
from z3 import *

def get_id(x):
    return Z3_get_ast_id(x.ctx_ref(), x.as_ast())

def minimize_core_aux2(s, core):
    mus = []
    ids = {}
    while core != []:
	c = core[0]
	new_core = mus + core[1:]
	is_sat = s.check(new_core)
	if is_sat == sat:
	    mus = mus + [c]
	    ids[get_id(c)] = True
	    core = core[1:]
	else:
	    core = s.unsat_core()
	    core = [c for c in core if get_id(c) not in ids]
    return mus

def minimize_core(s):
    core = list(s.unsat_core())
#    print "minimize_core: core = {}".format(core)
    core = minimize_core_aux2(s, core)
#    print "minimize_core: core = {}".format(core)
    return core


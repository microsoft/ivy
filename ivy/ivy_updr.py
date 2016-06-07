#! /usr/bin/env python
#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import sys
import pickle
import string
from ivy_utils import set_parameters, gen_to_set
import ivy_logic_utils as lu
import ivy_logic
import ivy
import ivy_transrel as tr
from itertools import chain
import ivy_solver as sv
import z3
import mini_pdr as pd
import ivy_utils as iu

from pattern.debug.profile import Stopwatch

def num_clauses(formula):
    if z3.is_and(formula):
        return len(formula.children())
    elif formula == True or z3.is_true(formula) or \
         formula == False or z3.is_false(formula):
        return 0
    else:
        return 1

def num_univ_clauses(formula):
    if z3.is_and(formula):
        fs = formula.children()
        n = 0
        for f in fs:
            if z3.is_quantifier(f) and f.is_forall():
                n += 1
        return n
    elif z3.is_quantifier(formula) and formula.is_forall():
        return 1
    else:
        return 0

def forward_clauses(clauses,inflex):
    return lu.rename_clauses(clauses, dict((x,tr.new(x)) for x in lu.used_symbols_clauses(clauses)
        if x != '=' and x not in inflex))

if __name__ == "__main__":
    ag = ivy.ivy_init()
    state = ag.states[0]
    sig = ag.domain.sig
    ptc = lu.TseitinContext()

    actions = [ag.actions[lab] for lab in ag.actions if lab != "error"]

    # get error states by computing reverse image or error action

    err_act = ag.actions["error"].update(ag.domain,state.in_scope)
    axioms = state.domain.background_theory(state.in_scope)
    error = tr.reverse_image([],axioms,err_act)
    print "error = {}".format(error)

    # get actions as updates
    updates = [action.update(ag.domain,state.in_scope) for action in actions]

    # get all the flexible (updated) variables
    flex = set(sym for u in updates for sym in u[0])
    print "flex = {}".format(flex)

    # inflex is all non-skolem symbols in signature that are not updated
    all_syms = sig.symbols
    inflex = set(sym for sym in all_syms if sym not in flex and not tr.is_new(sym) and not tr.is_skolem(sym))
    print "inflex = {}".format(inflex)

    # get all the skolem symbols
    all_syms = sig.symbols
    skolems = set(sym for sym in all_syms if tr.is_skolem(sym))
    print "skolems = {}".format(skolems)

    # make frames explicit
    updates = [tr.frame_update(u,flex,sig) for u in updates]
    for u in updates:
        print u

    # locals are flexible and skolem symbols (next values unused for skolems)
    ns = sv.native_symbol
    #lsyms = [(ns(sym),ns(tr.new(sym))) for sym in chain(flex,skolems)]
    lsyms = [(ns(sym),ns(tr.new(sym))) for sym in chain(flex)]

    # globals are the inflexible symbols
    gsyms = [ns(sym) for sym in inflex]
    
    print "lsyms = {}".format(lsyms)
    print "gsyms = {}".format(gsyms)

    init = state.clauses
    init = forward_clauses(init,inflex)
    print "init = {}".format(init)

    error = forward_clauses(error,inflex)
    print "error = {}".format(error)

    axioms += forward_clauses(axioms,inflex)

    init_z3 = sv.clauses_to_z3(init)
    print "init_z3 = {}".format(init_z3)
    for a in updates:
        print lu.simplify_clauses(a[1])
    rho_z3 = z3.Or(*[sv.clauses_to_z3(lu.simplify_clauses(a[1])) for a in updates])
    print "rho_z3 = {}".format(rho_z3)
    bad_z3 = sv.clauses_to_z3(error)
    print "bad_z3 = {}".format(bad_z3)
    background_z3 = sv.clauses_to_z3(axioms)
    print "background_z3 = {}".format(background_z3)
    #relations_z3 = [ns(rel) for rel in sig.relations if tr.is_new(rel) or rel in inflex]
    relations_z3 =  [ x for x in gsyms if not z3.is_const(x) or (z3.is_const(x) and x.sort() == z3.BoolSort()) ]
    relations_z3 += [ x for _,x in lsyms if not z3.is_const(x) or (z3.is_const(x) and x.sort() == z3.BoolSort()) ]
    print "relations_z3 = {}".format(relations_z3)

    ### HACK: remove skolem predicates from the list of predicate symbols
    #relations_z3 = [ x for x in relations_z3 if not x in skolems ]

    pdr = pd.PDR(init_z3, rho_z3, bad_z3, background_z3, gsyms, lsyms, relations_z3, True)

    watch = Stopwatch()

    with watch:
        outcome = pdr.run()
    if outcome:
        status = "valid"
        if hasattr(pdr, 'verify') and not pdr.verify(outcome):
            print "incorrect!!"
            status = "incorrect"
    else:
        print "NOT VALID"
        #status = report_failure(pdr, z3g, vocab)

    if outcome:
        print "(%d clauses)" % num_clauses(outcome)
        print "(%d universal clauses)" % num_univ_clauses(outcome)
        #fol_outcome = z3g.formula_back(outcome)
        #fol_invariant = FolSubstitution(extra.defs)( fol_outcome )
        #print fol_invariant

    print "PDR: %.2fs" % watch.clock.elapsed
    print "N =", pdr.N
    print pdr.iteration_count, "iterations"
    print pdr.sat_query_count, "calls to SAT"
            

#    syms = set(s for (upd,tr,pre) in updates for s in lu.symbols_clauses(tr))
#    print syms

        



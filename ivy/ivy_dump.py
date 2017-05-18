#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from analysis2_graph import *
import pickle
import z3_find_cons
import analysis3 as analysis
from functools import partial
from concept_space import *
from ivy_parser import parse

from ivy_parser import Ivy,Decl,AxiomDecl,RelationDecl,ConstantDecl,DerivedDecl,ConceptDecl,ActionDecl,InitDecl,ActionDef
import ivy_actions

def ivy_dump_file(f,ag):
    f.write('#lang ivy1\n')
    ivy = Ivy()
    d = ag.domain
    for r,arity in d.relations.iteritems():
        ivy.declare(RelationDecl(rel_inst(r,arity)))
    for v in ag.pvars:
        ivy.declare(ConstantDecl(Constant(v)))
    for c,df in d.concepts:
        ivy.declare(DerivedDecl(Definition(c.atom,cube_to_formula(df))))
    for a in d.axioms:
        ivy.declare(AxiomDecl(clause_to_formula(a)))
    for s in ag.states:
        if s.pred == None:
            ivy.declare(InitDecl(clauses_to_formula(s.clauses)))
    for n,a in ag.actions.iteritems():
        ivy.declare(ActionDecl(ActionDef(n,a)))
    for c,df in d.concept_spaces:
        ivy.declare(ConceptDecl(Definition(c,df)))
    f.write(repr(ivy))

if len(sys.argv) != 3:
    print "usage: %s infile.a2g outfile.ivy" % sys.argv[0]
    exit(1)

if sys.argv[1].endswith('.a2g'):
    f = open(sys.argv[1],'rU')
    if not f:
        print "not found: %s" % sys.argv[1]
        exit(1)
    ag = pickle.load(f)
    f.close()
else:
    print "input file must be .a2g"
    exit(1)

if sys.argv[2].endswith('.ivy'):
    f = open(sys.argv[2],'w')
    if not f:
        print "cannot write to: %s" % sys.argv[2]
        exit(1)
    ivy_dump_file(f,ag)
    f.close()
else:
    print "output file must be .ivy"
    exit(1)

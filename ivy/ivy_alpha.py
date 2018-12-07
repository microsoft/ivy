#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import sys
import itertools
from collections import defaultdict
import z3

from ivy_logic_utils import to_literal, false_clauses, Clauses
from ivy_solver import *
from ivy_logic_utils import *
from ivy_concept_space import *
from ivy_utils import Parameter

test_bottom = True

def alpha(state):
#    print "prestate: {}".format(state.clauses)
    d = ProgressiveDomain(state.domain.concept_spaces,verbose = False)
    state.clauses = d.post(state.clauses,state.domain.background_theory(state.in_scope),{},[])
#    print "poststate: {}".format(state.clauses)
    
#log = Parameter("log.alpha")
log = False

class ProgressiveDomain(object):
    def __init__(self, cs = [], verbose = True):
        self.concept_spaces = cs
        self.verbose = verbose
    
    def add_concept_space(self, atom, space):
        self.concept_spaces.append((atom, space))

    #TODO: this breaks abstraction. need to be able to hash formulas
    def cube_id(self,cube):
        z3_cube = cube_to_z3(cube)
        self.z3_cubes.append(z3_cube) # just to bump reference count
        id = get_id(z3_cube)
#        print "id: %s: %s" % (cube,id)
        return id

    def inhabited_cube(self,cube,truth=True,witness=None):
        cube = canonize_clause(cube)
        id = self.cube_id(cube)
        if id not in self.inhabited_cubes:
            if log:
                print "inhabited: %s" % cube
#            print "witness: %s" % witness
            self.inhabited_cubes[id] = truth

    def model_check(self):
        return
        if log:
            print "model_check {"
#        print "  model: %s" % get_model(self.solver)
        ra = RelAlg3(self.solver,self.new_sym,self)
        memo = dict()
        for atom,cs in self.concept_spaces:
            print "model check concept space: %s" % atom
            insts = cs.eval(memo,ra)
            memo[atom.relname] = ([t.rep for t in atom.args],insts)
            for cube,tab in insts:
                self.inhabited_cube(cube)

        if log:
            print "} model_check"

    def inhabited_lit(self,lit):
        self.inhabited_cube([lit])


    def unfold_defs(self,cube):
        insts = definition_instances(cube_to_formula(cube))
        add_clauses(self.solver, insts)


    def test_cube(self,cube):
        canon_cube = canonize_clause(cube)
        if log:
            print "cube: {}".format([str(c) for c in canon_cube])
        my_id = self.cube_id(canon_cube)
        if my_id in self.inhabited_cubes:
            if log:
                print "cached: %s" % [str(c) for c in cube]
            return self.inhabited_cubes[my_id]
        if log:
            print "test: %s" % [str(c) for c in cube]
        cube = rename_clause(cube,self.new_sym)
        vs = used_variables_clause(cube)
        # TODO: these constants need to have right sorts
        subs = dict((v.rep,var_to_skolem('__c',v)) for v in vs)
        scube = substitute_clause(cube,subs)
        self.unfold_defs(scube)
        res = check_cube(self.solver,scube,self.cube_memo,memo_unsat_only = True)
        if res:
            if len(cube) <= 4:
                self.model_check()
        else:
            self.inferred.append([~lit for lit in cube])
            if log:
                print "uninhabited: %s" % [str(c) for c in canon_cube]
            self.inhabited_cubes[my_id] = False
        return res

    def post_init(self,theory,background_theory,new_sym,to_keep):
        self.new_sym = new_sym
        self.solver = new_solver()        
        self.cube_memo = dict()
        self.inhabited_cubes = dict()
        self.z3_cubes = []
        self.memo = dict()
        if log:
            print "concrete state: %s" % theory
            print "background: %s" % background_theory
        add_clauses(self.solver, and_clauses(theory,background_theory))
        self.unsat = test_bottom and self.solver.check() == z3.unsat
        if self.unsat:
            print "core: %s" % unsat_core(and_clauses(theory,background_theory),true_clauses())
        
    def post_step(self,concept_spaces):
        if self.unsat:
            return false_clauses()
        self.inferred = []
#        print "cs: {}".format(concept_spaces)
        for atom,cs in concept_spaces:
            if log:
                print "concept space: %s" % atom
            concepts = cs.enumerate(self.memo,self.test_cube)
            if log:
                print "result: {}".format([str(c) for c in concepts])
            self.memo[atom.relname] = ([t.rep for t in atom.args], concepts)
        res = self.inferred
        if log:
            print "inferred: {}".format([[str(c) for c in cls] for cls in res])
        del self.inferred
        return Clauses(res)

    def post_quit(self):
        del self.new_sym
        del self.cube_memo
        del self.inhabited_cubes
        del self.z3_cubes
        del self.solver
        del self.unsat
        del self.memo
        
    def post(self,theory,background_theory,new_sym,to_keep):
        self.post_init(theory,background_theory,new_sym,to_keep)
        res = self.post_step(self.concept_spaces)
        self.post_quit()
        return res

def var_corr(terms1,terms2):
    d = dict((t2.rep,i) for i,t2 in enumerate(terms2) if isinstance(t2,Variable))
    return [(j,d[t1.rep]) for j,t1 in enumerate(terms1) if t1.rep in d]

def first_seen(memo,elem):
    if elem in memo:
        return False
    memo.add(elem)
    return True

def cut_row(row,good_cols):
    return [row[i] for i in good_cols]

# remove redundant columns from a relation table
def compact_table(tab):
    v,rows = tab
    memo = set()
    good_cols = [i for i,t in enumerate(v) if isinstance(t,Variable) and first_seen(memo,t.rep)]
    return (cut_row(v,good_cols),[cut_row(row,good_cols) for row in rows])

class RelAlg1(object):
    def __init__(self,solver,parent = None):
        self.solver = solver
        self.model = get_model(solver)
        self.parent = parent
    def prim(self,lit):
        insts = get_model_instances(self.solver,self.model,lit)
        res = compact_table((lit.atom.args,[l.atom.args for l in insts]))
        if self.parent and not self.empty(res):
            self.parent.inhabited_lit(lit)
        return res
    def prod(self,x,y):
        corr = var_corr(x[0],y[0])
        if corr:
            xc,yc = corr[0]
            index = defaultdict(list)
            for ry in y[1]:
                index[ry[yc].rep].append(ry)
            rows = [xr + yr for xr in x[1] for yr in index[xr[xc].rep]
                    if all(term_eq(xr[i],yr[j]) for i,j in corr)]
        else:
            rows = [xr+yr for xr,yr in itertools.product(x[1],y[1])
                    if all(term_eq(xr[i],yr[j]) for i,j in corr)]
        return compact_table((x[0]+y[0],rows))
    def subst(self,tab,subst):
        vs,rows = tab
        return ([subst[v.rep] for v in vs],rows)
    def empty(self,tab):
        return not tab[1]


def is_sat(solver,f):
    solver.push()
    ctx = z3.main_ctx()
    z3.Z3_solver_assert(ctx.ref(), solver.solver, f.as_ast())
    #solver.add(f)
    res = solver.check() != z3.unsat
    solver.pop()
    return res

def my_and(*args):
    ctx = z3.main_ctx()
    _args, sz = z3._to_ast_array(args)
    return z3.BoolRef(z3.Z3_mk_and(ctx.ref(), sz, _args), ctx)

def my_eq(x,y):
    ctx = z3.main_ctx()
    return z3.BoolRef(z3.Z3_mk_eq(ctx.ref(), x.as_ast(), y.as_ast()), ctx)


class RelAlg2(object):
    def __init__(self,solver,new_sym,parent = None):
        self.solver = solver
        self.temp_solver = new_solver()
        self.model = get_model(solver)
        self.parent = parent
        self.numbering = dict()
        self.next_number = 0
        self.enum_func = z3.Function('___ef',S,z3.IntSort())
        self.prim_cache = dict()
        self.prim_list = []
        self.new_sym = new_sym
        self.hm = HerbrandModel(solver,self.model)
    def enum(self,t):
        res = term_to_z3(t)
        if isinstance(t,Constant) and t.rep not in self.numbering:
            num = z3.IntVal(self.next_number)
            self.next_number += 1
            self.numbering[t.rep] = num
            cnst = self.enum_func(res) == num
            self.temp_solver.add(cnst)
        return res
    def z3var(self,t):
        return z3
    def prim(self,lit):
#        print "prim: %s" % lit
        z3lit = literal_to_z3(lit)
#        print z3lit
        id = get_id(z3lit)
        if id in self.prim_cache:
            return self.prim_cache[id]
        if lit.atom.relname == '=':
            cube = my_and(z3lit,*[my_eq(term_to_z3(x),self.enum(get_model_constant(self.model,rename_term(x,self.new_sym))))
                                 for x in lit.atom.args
                                 if not isinstance(x,Variable)])
            cubes = [cube] if is_sat(self.temp_solver,cube) else []
            if not cubes:
                print "unsat: %s" % cube
                exit(0)
        else:
            new_lit = rename_lit(lit,self.new_sym)
            insts = self.hm.ground_instances(new_lit)
#            print "insts: %s %s %s" % (lit,new_lit,insts)
            cubes = [my_and(*[my_eq(term_to_z3(x),self.enum(y))
                              for x,y in zip(lit.atom.args,inst.atom.args)]) for inst in insts]
#        print "prim: %s, %s" % (lit,cubes)
        if self.parent and cubes:
            self.parent.inhabited_lit(lit)
        self.prim_cache[id] = cubes
        self.prim_list.append(z3lit) # so id not lost
        return cubes
    def top(self):
        return [cube_to_z3([])]
    def prod(self,x,y):
        cubes = [my_and(xr,yr) for xr,yr in itertools.product(x,y)
                if is_sat(self.temp_solver,my_and(xr,yr))]
#        print "prod: %s * %s = %s" % (x,y,cubes)
        return cubes
    def subst(self,tab,subst):
        subs = [(term_to_z3(Constant(x)),term_to_z3(y)) for x,y in subst.iteritems()]
#        print subs
 #       print all([isinstance(p, tuple) and z3.is_expr(p[0]) and z3.is_expr(p[1]) and p[0].sort().eq(p[1].sort()) for p in subs])
        res = [z3.substitute(x,*subs) for x in tab]
#        print "subst: %s -> %s" % (tab,res)
        return res
    def empty(self,tab):
        return not tab
                
class RelAlg3(RelAlg2):
    def prim(self,lit):
        print "prim: %s" % lit
        z3lit = literal_to_z3(lit)
#        print z3lit
        id = get_id(z3lit)
        if id in self.prim_cache:
            return self.prim_cache[id]
        new_lit = rename_lit(lit,self.new_sym)
        vs,insts = self.hm.check(new_lit)
#        print "insts: %s %s %s" % (lit,new_lit,insts)
        cubes = [my_and(*[my_eq(term_to_z3(x),self.enum(y))
                          for x,y in zip(vs,inst)]) for inst in insts]
#        print "prim: %s, %s" % (lit,cubes)
        if self.parent and cubes:
            self.parent.inhabited_lit(lit)
        self.prim_cache[id] = cubes
        self.prim_list.append(z3lit) # so id not lost
        return cubes
    
        
if __name__ == "__main__":
    d = ProgressiveDomain(None,None,None,False)
    d.add_concept_space(to_atom("s1(X,Y)"),to_concept_space("(p(X,Y) * ~p(Y,X))"))
    d.add_concept_space(to_atom("s2(X,Y)"),to_concept_space("(s1(X,Y) + ~p(X,X) + p(X,c))"))
    d.add_concept_space(to_atom("s3(X,Y)"),to_concept_space("(~p(X,c) * =(X,a))"))
    theory = to_clauses("[[p(a,b)],[~p(b,a)],[p(a,c)],[~p(a,a)]]")
    cons = d.post(theory,[],dict(),[])
    print cons
    # solver = new_solver()
    # add_clauses(solver,to_clauses("[[p(a,b)],[~p(b,a)],[p(a,c)],[~p(a,a)]]"))
    # res = check_cube(solver,[])
    # print res
    # ra = RelAlg(solver)
    # cs = to_concept_space("( + ~p(X,X) + p(X,c))")
    # memo = dict()
    # print cs.eval(memo,ra)




                

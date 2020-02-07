#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_logic import Variable,Constant,Atom,Literal,App,sig,Iff,And,Or,Not,Implies,EnumeratedSort,Ite,Definition, is_atom, equals, Equals, Symbol,ast_match_lists, is_in_logic, Exists, RelationSort, is_boolean, is_app, is_eq, pto, close_formula,symbol_is_polymorphic,is_interpreted_symbol 

from ivy_logic_utils import to_clauses, formula_to_clauses, substitute_constants_clause,\
    substitute_clause, substitute_ast, used_symbols_clauses, used_symbols_ast, rename_clauses, subst_both_clauses,\
    variables_distinct_ast, is_individual_ast, variables_distinct_list_ast, sym_placeholders, sym_inst, apps_ast,\
    eq_atom, eq_lit, eqs_ast, TseitinContext, formula_to_clauses_tseitin,\
    used_symbols_asts, symbols_asts, has_enumerated_sort, false_clauses, true_clauses, or_clauses, dual_formula, Clauses, and_clauses, substitute_constants_ast, rename_ast, bool_const, used_variables_ast, unfold_definitions_clauses, skolemize_formula
from ivy_transrel import state_to_action,new, compose_updates, condition_update_on_fmla, hide, join_action, ite_action, \
    subst_action, null_update, exist_quant, hide_state, hide_state_map, constrain_state, bind_olds_action, old
from ivy_utils import unzip_append, IvyError, IvyUndefined, distinct_obj_renaming, dbg
import ivy_ast
from ivy_ast import AST, compose_atoms, MixinAfterDef
import ivy_module
import ivy_utils as iu

def p_c_a(s):
    a = s.split(':')
    return iu.Location(a[0]+'.ivy',int(a[1]))

checked_assert = iu.Parameter("assert","",check=lambda s: len(s.split(':'))==2,
                              process=p_c_a)

class Schema(AST):
    def __init__(self,defn):
        self.defn,self.fresh = defn,[]
        self.args = [defn]
        self.instances = []
    def __str__(self):
        res = repr(self.defn)
        if self.fresh:
            res += ' fresh ' + ','.join(repr(x) for x in self.fresh)
        return res
    def defines(self):
        return self.defn.defines()
    def get_instance(self,params,to_clauses=True):
        defn = self.defn
        if len(params) != len(defn.args[0].args):
            raise IndexError
        subst = dict((x.rep,y.rep) for x,y in zip(defn.args[0].args,params))
        ast = ivy_ast.ast_rewrite(defn.args[1],ivy_ast.AstRewriteSubstPrefix(subst,None))
#        print "get_instance ast = {}".format(ast)
        fmla = ast.compile_with_sort_inference()
#        print "get_instance fmla = {}".format(fmla)
        return formula_to_clauses(fmla) if to_clauses else fmla
    def instantiate(self,params):
        self.instances.append(self.get_instance(params,False))

class ActionContext(object):
    """ Context Manager for evaluating states and actions. """
    def __init__(self,domain = None):
        self.domain = domain
    def __enter__(self):
        global context
        self.old_context = context
        context = self
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global context
        context = self.old_context
        return False # don't block any exceptions
    def get(self,symbol):
        return ivy_module.find_action(symbol)
    def new_state(self,clauses, exact = False, domain = None, expr = None):
        domain = self.domain if self.domain is not None else domain
        assert domain is not None
        return domain.new_state(clauses)

class UnrollContext(ActionContext):
    def __init__(self,card,domain = None):
        """ card is a function that returns a cardinarlity bound for a sort,
        to be used in bounding loop unrollings """
        self.card = card
        self.domain = domain

context = ActionContext()

class SymbolList(AST):
    def __init__(self,*symbols):
        assert all(isinstance(a,str) or isinstance(a,Symbol) for a in symbols)
        self.symbols = symbols
        self.args = symbols
    def __str__(self):
        return ','.join(str(x) for x in self.symbols)

class UpdatePattern(AST):
    """ Defines an update pattern. This consists of a set of
    placeholders, a pattern action containg the placeholders, a
    pre-condition and a transition constraint. A placeholder matches any ground
    term, unless it begins with a capital, in which case it matches a variable.
    TODO: we probably also need side conditions in some form.
    """
    def __init__(self,placeholders,pattern,precond,transrel):
#        assert isinstance(placeholders,ConstantDecl)
        self.args = [placeholders,pattern,precond,transrel]
        self.placeholders,self.pattern,self.precond,self.transrel = self.args = placeholders,pattern,precond,transrel
    sort_infer_root = True
    def __str__(self):
        return ('params ' + str(self.placeholders)
                + ' in ' + str(self.pattern) + ' -> \n    requires ' + str(self.precond)
                + '\n    ensures ' + str(self.transrel))
    def match(self,action):
        """ if action matches pattern, return the axioms, else None """
##        print "match: %s %s" % (self,action)
        subst = dict()
        if self.pattern.match(action,self.placeholders.args,subst):
#            print "match: {}".format(subst)
            axioms_as_clause_sets = (formula_to_clauses(x) for x in (Not(self.precond),self.transrel))
            return (subst_both_clauses(x,subst) for x in axioms_as_clause_sets)
        return None

class UpdatePatternList(AST):
    def __init__(self,*args):
        assert all(isinstance(a,UpdatePattern) for a in args)
        self.args = args
    def __str__(self):
        return ''.join('\n  ' + str(x) for x in self.args)

class PatternBasedUpdate(AST):
    """ Update based on pattern matching. Contains a sequence of actions containing placeholders.
    The first action that matches produces the corresponding pre-condition and transition constraint.
    If no match raises StopIteration.
    """
    def __init__(self,defines,dependencies,patterns):
        assert isinstance(defines,SymbolList)
        assert isinstance(dependencies,SymbolList)
        assert isinstance(patterns,UpdatePatternList)
        self.args = [defines,dependencies,patterns]
        self.defines, self.dependencies,self.patterns = defines,dependencies,patterns
    def __str__(self):
        return str(self.defines) + ' from ' + str(self.dependencies) + str(self.patterns)
    def get_update_axioms(self,updated,action):
#        print "get_update_axioms: {}, {}".format(map(str,updated),action)
        for x in updated:
            if x in self.dependencies.symbols:
                updated = updated + [y for y in self.defines.symbols if y not in updated]
                try:
                    precond,postcond = next(y for y in (p.match(action) for p in self.patterns.args) if y != None)
                except StopIteration:
                    raise IvyError(action,'No matching update axiom for ' + str(x))
                postcond = state_to_action((updated,postcond,precond))
#                print "update axioms: {}, {}, {}".format(map(str,postcond[0]),postcond[1],postcond[2])
                return (updated,postcond[1],precond)
        return (updated,true_clauses(),false_clauses())

class DerivedUpdate(object):
    def __init__(self,defn):
        self.defn = defn
        self.dependencies = used_symbols_ast(defn.args[1])
    def get_update_axioms(self,updated,action):
        defines = self.defn.args[0].rep
        if defines not in updated and any(x in self.dependencies for x in updated):
            updated.append(defines)
        return (updated,None,None)
    def __str__(self):
        return str(self.defn)

class Action(AST):
    def __init__(self,*args):
        self.args = list(args)
    def __str__(self):
        return self.name() + ' ' + ', '.join(str(x) for x in self.args)
    def __call__(self,interpreter):
        for op in self.args:
            interpreter.execute(self)
    def match(self,action,placeholders,subst):
        if type(action) is not type(self) or len(action.args) != len(self.args):
            return False
        return ast_match_lists(action.args,self.args,placeholders,subst)
    def int_update(self,domain,in_scope):
        (updated,clauses,pre) = self.action_update(domain,in_scope)
        # instantiate the update axioms
#        iu.dbg('[str(x) for x in domain.updates]')
        for u in domain.updates:
            updated,transrel,precond = u.get_update_axioms(updated,self)
           # TODO: do something with the precondition
#            if transrel:
##                print "updated: {}".format(updated)
##                print "update from axiom: %s" % transrel
            if transrel is not None:
                clauses = and_clauses(clauses,transrel)
            if precond is not None:
                pre = or_clauses(pre,precond)
##        print "update clauses: %s" % clauses
        res = (updated,clauses,pre)
        return res
    def update(self,domain,in_scope):
        return self.hide_formals(bind_olds_action(self.int_update(domain,in_scope)))
    def hide_formals(self,update):
        to_hide = []
        if hasattr(self,'formal_params'):
            to_hide += self.formal_params
        if hasattr(self,'formal_returns'):
            to_hide += self.formal_returns
        if to_hide:
             update = hide(to_hide,update)
        return update
    def copy_formals(self,res):
        if hasattr(self,'formal_params'):
            res.formal_params = self.formal_params
        if hasattr(self,'formal_returns'):
            res.formal_returns = self.formal_returns
        if hasattr(self,'labels'):
            res.labels = self.labels
        return res
    def add_label(self,label):
        res = self.clone(self.args)
        self.copy_formals(res)
        res.label = label
        return res
    def assert_to_assume(self,kinds):
        args = [a.assert_to_assume(kinds) if isinstance(a,Action) else a for a in self.args]
        res = self.clone(args)
        self.copy_formals(res)
        return res
    def drop_invariants(self):
        args = [a.drop_invariants() if isinstance(a,Action) else a for a in self.args]
        res = self.clone(args)
        self.copy_formals(res)
        return res
    def prefix_calls(self,pref):
        args = [a.prefix_calls(pref) if isinstance(a,Action) else a for a in self.args]
        res = self.clone(args)
        self.copy_formals(res)
        return res
    def unroll_loops(self,card):
        args = [a.unroll_loops(card) if isinstance(a,Action) else a for a in self.args]
        res = self.clone(args)
        self.copy_formals(res)
        return res
    def iter_calls(self):
        for a in self.args:
            if isinstance(a,Action):
                for c in a.iter_calls():
                    yield c
    def iter_subactions(self):
        yield self
        for a in self.args:
            if isinstance(a,Action):
                for c in a.iter_subactions():
                    yield c
    def iter_internal_defines(self):
        for a in self.args:
            if isinstance(a,Action):
                for c in a.iter_internal_defines():
                    yield c
    def decompose(self,pre,post,fail=False):
        return [(pre,[self],post)]
    def modifies(self):
        return []
    def set_lineno(self,lineno):
        self.lineno = lineno
        return self
        

class AssumeAction(Action):
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assume'
    def action_update(self,domain,pvars):
        type_check(domain,self.args[0])
        clauses = formula_to_clauses_tseitin(skolemize_formula(self.args[0]))
        clauses = unfold_definitions_clauses(clauses)
        clauses = Clauses(clauses.fmlas,clauses.defs,EmptyAnnotation())
        return ([],clauses,false_clauses(annot = EmptyAnnotation()))

class AssertAction(Action):
    def __init__(self,*args):
        assert len(args) <= 2
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assert'
    def action_update(self,domain,pvars):
        type_check(domain,self.args[0])
#        print type(self.args[0])
        ca = checked_assert.get()
        if ca:
            if ca != self.lineno:
                return ([],formula_to_clauses(self.args[0],annot = EmptyAnnotation()),false_clauses(annot = EmptyAnnotation()))
        cl = formula_to_clauses(dual_formula(self.args[0]))
#        return ([],formula_to_clauses_tseitin(self.args[0]),cl)
        cl = Clauses(cl.fmlas,cl.defs,EmptyAnnotation())
        return ([],true_clauses(annot = EmptyAnnotation()),cl)
    def assert_to_assume(self,kinds):
        mykind = self.kind if hasattr(self,'kind') else type(self)
        if mykind not in kinds:
            return Action.assert_to_assume(self,kinds)
        res = AssumeAction(*self.args)
        ivy_ast.copy_attributes_ast(self,res)
        self.copy_formals(res)
        return res
    
# Prior to version 1.7, Ensures is always verified

class EnsuresAction(AssertAction):
    def assert_to_assume(self,kinds):
        if (iu.get_numeric_version() <= [1,6]):
            return Action.assert_to_assume(self,kinds)
        return AssertAction.assert_to_assume(self,kinds)

class RequiresAction(AssertAction):
    pass

class SubgoalAction(AssertAction):
    def clone(self,args):
        res = AssertAction.clone(self,args)
        if hasattr(self,'kind'):
            res.kind = self.kind
        return res

def equiv_ast(ast1,ast2):
    if is_individual_ast(ast1): # ast2 had better be the same!
        return eq_atom(ast1,ast2)
    return And(Or(ast1,Not(ast2)),Or(Not(ast1),ast2))

def get_correct_arity(domain,atom):
    if atom.is_numeral():
        return 0
    return len(atom.rep.sort.dom)

def type_check(domain,ast):
    for atom in apps_ast(ast):
            arity = len(atom.args)
            correct_arity = get_correct_arity(domain,atom)
            if arity != correct_arity and not(atom.rep == '-' and arity == 1):
#                print "atom: {} : {}".format(atom,type(atom))
                raise IvyError(atom,
                               "wrong number of arguments to {}: got {}, expecting {}."
                               .format(atom.rep,arity,correct_arity))
#            for a in atom.args:
#                if isinstance(a.get_sort(),EnumeratedSort):
#                    raise IvyError(a,
#                                   "symbol {} of enumerated type can only appear under equality"
#                                   .format(a.rep))
    # for atom in eqs_ast(ast):
    #         t0,t1 = [x.get_sort() for x in atom.args]
    #         if t0 != t1:
    #             raise IvyError(atom,
    #                            "comparison of incompatible types")


def type_ast(domain,ast):
    if is_atom(ast) and ast.rep not in domain.relations and ast.rep != '=':
        return App(ast.rep,ast.args)
    if isinstance(ast,App) and ast.rep in domain.relations:
        return Atom(ast.rep,ast.args)
    return ast

def destr_asgn_val(lhs,fmlas):
    mut = lhs.args[0]
    rest = list(lhs.args[1:])
    mut_n = mut.rep
    if mut_n.name in ivy_module.module.destructor_sorts:
        lval,new_clauses,mutated = destr_asgn_val(mut,fmlas)
    else:
        nondet = mut_n.suffix("_nd").skolem()
        new_clauses = (mk_assign_clauses(mut_n,nondet(*sym_placeholders(mut_n))))
        lval = nondet(*mut.args)
        mutated = mut_n

    n = lhs.rep
    vs = sym_placeholders(n)
    dlhs = n(*([lval] + vs[1:]))
    drhs = n(*([mut] + vs[1:]))
    eqs = [eq_atom(v,a) for (v,a) in zip(vs,lhs.args)[1:] if not isinstance(a,Variable)]
    if eqs:
        fmlas.append(Or(And(*eqs),equiv_ast(dlhs,drhs)))
    for destr in ivy_module.module.sort_destructors[mut.sort.name]:
        if destr != n:
            phs = sym_placeholders(destr)
            a1 = [lval] + phs[1:]
            a2 = [mut] + phs[1:]
            fmlas.append(eq_atom(destr(*a1),destr(*a2)))

    return  lhs.rep(*([lval]+rest)), new_clauses, mutated


class AssignAction(Action):
    def __init__(self,*args):
        assert len(args) == 2
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assign'
    def __str__(self):
        return str(self.args[0]) + ' := ' + str(self.args[1])
    def modifies(self):
        n = self.args[0]
        while n.rep.name in ivy_module.module.destructor_sorts:
            n = n.args[0]
        return [n.rep]
    def action_update(self,domain,pvars):
        lhs,rhs = self.args
        n = lhs.rep

        # Handle the hierarchical case
        if n in domain.hierarchy:
            asgns = [postfix_atoms_ast(self,Atom(x,[])) for x in domain.hierarchy[n]]
            res = unzip_append([asgn.action_update(domain,pvars) for asgn in asgns])
            return res

        # If the lhs application is partial, make it total by adding parameters
        xtra = len(lhs.rep.sort.dom) - len(lhs.args)
        if xtra < 0:
            raise IvyError(self,"too many parameters in assignment to " + lhs.rep)
        if xtra > 0:
            extend = sym_placeholders(lhs.rep)[-xtra:]
            extend = variables_distinct_list_ast(extend,self)  # get unused variables
            lhs = add_parameters_ast(lhs,extend)
            # Assignment of individual to a boolean is a special case
            if is_individual_ast(rhs) and not is_individual_ast(lhs):
                rhs = eq_atom(extend[-1],add_parameters_ast(rhs,extend[0:-1]))
            else:
                rhs = add_parameters_ast(rhs,extend)

        lhs_vars = used_variables_ast(lhs)
        if any(v not in lhs_vars for v in used_variables_ast(rhs)):
            print self
            raise IvyError(self,"multiply assigned: {}".format(lhs.rep))

        type_check(domain,rhs)
        if is_individual_ast(lhs) != is_individual_ast(rhs):
#            print type(lhs.rep)
#            print str(lhs.rep)
#            print type(lhs.rep.sort)
#            print "lhs: %s: %s" % (lhs,type(lhs))
#            print "rhs: %s: %s" % (rhs,type(rhs))
            raise IvyError(self,"sort mismatch in assignment to {}".format(lhs.rep))

        # For a destructor assignment, we actually mutate the first argument

        if n.name in ivy_module.module.destructor_sorts:
            fmlas = []
            nondet_lhs,new_clauses,mut_n = destr_asgn_val(lhs,fmlas)
            fmlas.append(equiv_ast(nondet_lhs,rhs))
            new_clauses = and_clauses(new_clauses,Clauses(fmlas))
            return ([mut_n], new_clauses, false_clauses(annot=EmptyAnnotation()))

            # This is the old version that doesn't work for nested destructors

            mut = lhs.args[0]
            rest = list(lhs.args[1:])
            mut_n = mut.rep
            nondet = mut_n.suffix("_nd").skolem()
            new_clauses = mk_assign_clauses(mut_n,nondet(*sym_placeholders(mut_n)))
            fmlas = []
            nondet_lhs = lhs.rep(*([nondet(*mut.args)]+rest))
            fmlas.append(equiv_ast(nondet_lhs,rhs))
            vs = sym_placeholders(n)
            dlhs = n(*([nondet(*mut.args)] + vs[1:]))
            drhs = n(*([mut] + vs[1:]))
            eqs = [eq_atom(v,a) for (v,a) in zip(vs,lhs.args)[1:] if not isinstance(a,Variable)]
            if eqs:
                fmlas.append(Or(And(*eqs),equiv_ast(dlhs,drhs)))
            for destr in ivy_module.module.sort_destructors[mut.sort.name]:
                if destr != n:
                    phs = sym_placeholders(destr)
                    a1 = [nondet(*mut.args)] + phs[1:]
                    a2 = [mut] + phs[1:]
                    fmlas.append(eq_atom(destr(*a1),destr(*a2)))
            new_clauses = and_clauses(new_clauses,Clauses(fmlas))
            return ([mut_n], new_clauses, false_clauses(annot=EmptyAnnotation()))

        # For a variant assignment, we have to choose a new value that points to
        # the rhs, and to nothing else.

        if domain.is_variant(lhs.sort,rhs.sort):
            new_clauses = mk_variant_assign_clauses(lhs,rhs)
        else:
            new_clauses = mk_assign_clauses(lhs,rhs)
#        print "assign new_clauses = {}".format(new_clauses)
        return ([n], new_clauses, false_clauses(annot=EmptyAnnotation()))

class VarAction(AST):
    pass

def mk_assign_clauses(lhs,rhs):
    n = lhs.rep
    new_n = new(n)
    args = lhs.args
    dlhs = new_n(*sym_placeholders(n))
    vs = dlhs.args
    eqs = [eq_atom(v,a) for (v,a) in zip(vs,args) if not isinstance(a,Variable)]
    rn = dict((a.rep,v) for v,a in zip(vs,args) if isinstance(a,Variable))
    drhs = substitute_ast(rhs,rn)
    if eqs:
        drhs = Ite(And(*eqs),drhs,n(*dlhs.args))
    new_clauses = Clauses([],[Definition(dlhs,drhs)],EmptyAnnotation())
    return new_clauses


def mk_variant_assign_clauses(lhs,rhs):
    n = lhs.rep
    new_n = new(n)
    args = lhs.args
    dlhs = new_n(*sym_placeholders(n))
    vs = dlhs.args
    eqs = [eq_atom(v,a) for (v,a) in zip(vs,args) if not isinstance(a,Variable)]
    rn = dict((a.rep,v) for v,a in zip(vs,args) if isinstance(a,Variable))
    drhs = substitute_ast(rhs,rn)
    nondet = n.suffix("_nd").skolem()
    if eqs:
        nondet = Ite(And(*eqs),nondet,n(*dlhs.args))
    lsort,rsort = lhs.sort,rhs.sort
    fmlas = [Iff(pto(lsort,rsort)(dlhs,Variable('X',rsort)),Equals(Variable('X',rsort),drhs))]
    for s in ivy_module.module.variants[lsort.name]:
        if s != rsort:
            fmlas.append(Not(pto(lsort,s)(dlhs,Variable('X',s))))
    new_clauses = Clauses(fmlas,[Definition(dlhs,nondet)])
    return new_clauses


def sign(polarity,atom):
    return atom if polarity else Not(atom)

class SetAction(Action):
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'set'
    def action_update(self,domain,pvars):
        lit = self.args[0]
        n = lit.atom.relname
        new_n = new(n)
        args = lit.atom.args
        vs = sym_placeholders(n)
        eqs = [Atom(equals,[v,a]) for (v,a) in zip(vs,args) if not isinstance(a,Variable)]
        new_clauses = And(*([Or(sign(lit.polarity,Atom(new_n,vs)),sign(1-lit.polarity,Atom(n,vs))),
                             sign(lit.polarity,Atom(new_n,args))] +
                            [Or(*([sign(0,Atom(new_n,vs)),sign(1,Atom(n,vs))] + [eq])) for eq in eqs] +
                            [Or(*([sign(1,Atom(new_n,vs)),sign(0,Atom(n,vs))] + [eq])) for eq in eqs]))
        new_clauses = formula_to_clauses(new_clauses)
        return ([n], new_clauses, false_clauses())

class HavocAction(Action):
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'havoc'
    def __str__(self):
        return str(self.args[0]) + ' := *'
    def modifies(self):
        n = self.args[0]
        while n.rep.name in ivy_module.module.destructor_sorts:
            n = n.args[0]
        return [n.rep]
    def action_update(self,domain,pvars):
        lhs = self.args[0]
        n = lhs.rep
        new_n = new(n)
        args = lhs.args
        vs = [Variable("X%d" % i,s) for i,s in enumerate(n.sort.dom)]
        eqs = [eq_atom(v,a) for (v,a) in zip(vs,args) if not isinstance(a,Variable)]
        if is_atom(lhs):
            clauses = And(*([Or(Not(Atom(new_n,vs)),Atom(n,vs),eq) for eq in eqs] +
                            [Or(Atom(new_n,vs),Not(Atom(n,vs)),eq) for eq in eqs]))
        elif is_individual_ast(lhs.rep):
            clauses = And(*[Or(eq_atom(type(lhs)(new_n,*vs),type(lhs)(n,*vs)),eq) for eq in eqs])
        else: # TODO: ???
            clauses = And()
        clauses = formula_to_clauses(clauses)
        clauses = Clauses(clauses.fmlas,clauses.defs,EmptyAnnotation())
        return ([n], clauses, false_clauses(annot=EmptyAnnotation()))


def make_field_update(self,l,f,r,domain,pvars):
    if not f.is_relation() or len(f.sort.dom) != 2:
        raise IvyError(self, "field " + str(f) + " must be a binary relation")
    v = Variable('X',f.sort.dom[1])
    aa = AssignAction(f(l,v),r(v))
    return aa.action_update(domain,pvars)

class AssignFieldAction(Action):
    def __init__(self,*args):
        assert len(args) == 3
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assign_field'
    def __str__(self):
        return str(self.args[0]) + '.' + str(self.args[1]) + ' := ' + str(self.args[2])
    def action_update(self,domain,pvars):
        l,f,r = self.args
        return make_field_update(self,l,f,lambda v: Equals(v,r),domain,pvars)

class NullFieldAction(Action):
    def __init__(self,*args):
        assert len(args) == 2
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'null_field'
    def __str__(self):
        return str(self.args[0]) + '.' + str(self.args[1]) + ' := null'
    def action_update(self,domain,pvars):
        l,f = self.args
        return make_field_update(self,l,f,lambda v: Or(),domain,pvars)

class CopyFieldAction(Action):
    def __init__(self,*args):
        assert len(args) == 4
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assign_field'
    def __str__(self):
        return str(self.args[0]) + '.' + str(self.args[1]) + ' := ' + str(self.args[2]) + '.' + str(self.args[3])
    # TODO: here we ignore field name since we support only one field
    def action_update(self,domain,pvars):
        l,lf,r,rf = self.args
        return make_field_update(self,l,lf,lambda v: rf(r,v),domain,pvars)

def instantiate_macro(inst,defns):
    if inst.relname in defns:
        defn = defns[inst.relname]
        aparams = inst.args
        fparams = defn.args[0].args
        if len(aparams) != len(fparams):
            raise IvyError(inst,"wrong number of parameters");
        subst = dict((x.rep,y) for x,y in zip(fparams,aparams))
#        print "subst: {!r}".format(subst)
        psubst = dict((x.rep,y.rep) for x,y in zip(fparams,aparams)
                      if (isinstance(y,ivy_ast.App) or isinstance(y,ivy_ast.Atom)) and
                      len(y.args) == 0)
        return ivy_ast.ast_rewrite(defn.args[1],ivy_ast.AstRewriteSubstConstantsParams(subst,psubst))
    return None

class InstantiateAction(Action):
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    def name(self):
        return 'instantiate'
    def int_update(self,domain,pvars):
        inst = self.args[0]
        if hasattr(domain,'macros'):
            im = instantiate_macro(inst,domain.macros)
#            print "im: {}".format(im)
            if im:
#                print im
                res = im.compile().int_update(domain,pvars)
##                print "res: {}".format(res)
                return res
        if inst.relname in domain.schemata:
            clauses = domain.schemata[inst.relname].get_instance(inst.args)
            return ([],clauses, false_clauses())
        raise IvyError(inst,"instantiation of undefined: {}".format(inst.relname))
    def cmpl(self):
        return self
        mas = [a.cmpl() for a in self.args[0].args]
        n = self.args[0].rep
        return InstantiateAction(ivy_ast.Atom(n,mas))



class Sequence(Action):
    def name(self):
        return 'sequence'
    def __str__(self):
        return '{' + '; '.join(str(x) for x in self.args) + '}'
    def int_update(self,domain,pvars):
        update = ([],true_clauses(EmptyAnnotation()),false_clauses(EmptyAnnotation()))
        axioms = domain.background_theory(pvars)
        for op in self.args:
            thing = op.int_update(domain,pvars);
#            print "op: {}, thing[2].annot: {}".format(op,thing[2].annot)
            update = compose_updates(update,axioms,thing)
            if hasattr(op,'lineno') and update[1].annot is not None:
                update[1].annot.lineno = op.lineno
        return update
    def __call__(self,interpreter):
        for op in self.args:
            interpreter.execute(op)
    def decompose(self,pre,post,fail=False):
        return [(pre,self.args,post)]
        
determinize = False

def set_determinize(t):
    global determinize
    determinize = t

choice_action_ctr = 0

class ChoiceAction(Action):
    def __init__(self,*args):
        Action.__init__(self,*args)
        global choice_action_ctr
        self.unique_id = choice_action_ctr
        choice_action_ctr += 1
    def name(self):
        return 'choice'
    def __str__(self):
        return ''.join('if * ' + bracket_action(x) + '\nelse ' for x in self.args[0:-1]) + bracket_action(self.args[-1])
    def int_update(self,domain,pvars):
        if determinize and len(self.args) == 2:
            cond = bool_const('___branch:' + str(self.unique_id))
            ite = IfAction(Not(cond),self.args[0],self.args[1])
            return ite.int_update(domain,pvars)
        result = [], false_clauses(annot=EmptyAnnotation()), false_clauses(annot=EmptyAnnotation())
        for a in self.args:
            foo = a.int_update(domain, pvars)
            result = join_action(result, foo, domain.relations)
        return result
    def __repr__(self):
        if hasattr(self, 'label'):
            return self.label
        else:
            return super(ChoiceAction, self).__repr__()
    def decompose(self,pre,post,fail=False):
        return [(pre,[a],post) for a in self.args]

class EnvAction(ChoiceAction):
    """ This represents an action of the environment. It is
    similar to ChoiceAction above, but appears differently in the UI """

    # This is the same as in ChoiceAction, but the paramters
    # of the child actions are hidden.

    def int_update(self,domain,pvars):
        if determinize and len(self.args) == 2:
            cond = bool_const('___branch:' + str(self.unique_id))
            ite = IfAction(cond,self.args[0],self.args[1])
            return ite.update(domain,pvars)
        result = [], false_clauses(annot=EmptyAnnotation()), false_clauses(annot=EmptyAnnotation())
#        print 'env action:'
        for a in self.args:
            foo = a.update(domain, pvars)
#            print 'sub vars = {}'.format([str(x) for x in used_symbols_clauses(foo[1])])
            result = join_action(result, foo, domain.relations)
#            print 'join vars = {}'.format([str(x) for x in used_symbols_clauses(result[1])])
#            print 'annot = {}'.format(result[1].annot)
        return result
    def __str__(self):
        if all(hasattr(a,'label') for a in self.args):
            return '{' + ','.join(a.label for a in self.args) + '}'
        return super(ChoiceAction, self).__str__()

    @property
    def formal_params(self):
        return []
    @property
    def formal_returns(self):
        return []

def bracket_action(action):
    return ('{' + str(action) + '}') if not isinstance(action,Sequence) else str(action)

class IfAction(Action):
    def name(self):
        return 'if'
    def __str__(self):
        if_part  = 'if ' + str(self.args[0]) + ' ' + bracket_action(self.args[1])
        else_part = ('\nelse ' + bracket_action(self.args[2])) if len(self.args) >= 3 else ''
        return if_part + else_part
    def subactions(self) :
        if isinstance(self.args[0],ivy_ast.Some):
            ps = list(self.args[0].params())
            fmla = self.args[0].fmla()
            vs = [Variable('V{}'.format(idx),x.sort) for idx,x in enumerate(ps)]
            subst = dict((c,v) for c,v in zip(ps,vs))
            sfmla = substitute_constants_ast(fmla,subst)
            if isinstance(self.args[0],ivy_ast.SomeMinMax):
                idx = self.args[0].index()
                if idx not in ps:
                    ltsym = Symbol('<',RelationSort([idx.sort,idx.sort]))
                    operator = lambda x,y: Not(ltsym(x,y))
                    ivar = substitute_constants_ast(idx,subst)
                    comp = operator(ivar,idx) if isinstance(self.args[0],ivy_ast.SomeMin) else operator(idx,ivar)
                    fmla = And(fmla,Implies(sfmla,comp))
                else :
                    leqsym = Symbol('<=',RelationSort([idx.sort,idx.sort]))
                    operator = lambda x,y: And(leqsym(x,y),Not(Equals(x,y)))
                    ivar = next(v for p,v in zip(ps,vs) if p == idx)
                    comp = operator(ivar,idx) if isinstance(self.args[0],ivy_ast.SomeMin) else operator(idx,ivar)
                    fmla = And(fmla,Not(And(sfmla,comp)))
            if_part = LocalAction(*(ps+[Sequence(AssumeAction(fmla),self.args[1])]))
            else_action = self.args[2] if len(self.args) >= 3 else Sequence()
            else_part = Sequence(AssumeAction(Not(sfmla)),else_action)
#            iu.dbg('if_part')
#            iu.dbg('else_part')
        else:
            if not is_boolean(self.args[0]):
                raise IvyError(self,'condition must be boolean') 
            if_part = Sequence(AssumeAction(self.args[0]),self.args[1])
            else_action = self.args[2] if len(self.args) >= 3 else Sequence()
            else_part = Sequence(AssumeAction(dual_formula(self.args[0])),else_action)
        return if_part,else_part
    def int_update(self,domain,pvars):
#        update = self.args[1].int_update(domain,pvars)
#        return condition_update_on_fmla(update,self.args[0],domain.relations)
        if used_variables_ast(self.args[0]):
            raise IvyError(self,'variables in "if" conditions must be explicitly quantified')
        if not isinstance(self.args[0],ivy_ast.Some):
            if not is_boolean(self.args[0]):
                raise IvyError(self,'condition must be boolean') 
            branches = [self.args[1],self.args[2] if len(self.args) >= 3 else Sequence()]
            upds = [a.int_update(domain,pvars) for a in branches]
#            if hasattr(self,'lineno'):
#                print 'ite at {}'.format(self.lineno)
#            print 'if vars = {}'.format([str(x) for x in used_symbols_clauses(upds[0][1])])
#            print 'else vars = {}'.format([str(x) for x in used_symbols_clauses(upds[1][1])])
            res =  ite_action(self.args[0],upds[0],upds[1],domain.relations)
#            print 'join vars = {}'.format([str(x) for x in used_symbols_clauses(res[1])])
            return res
        if_part,else_part = (a.int_update(domain,pvars) for a in self.subactions())

        res = join_action(if_part,else_part,domain.relations)
        # Hack: the ite annotation comes out reversed. Fix it.
        for i in range(1,3):
            x = res[i].annot
            if isinstance(x,IteAnnotation):
                res[i].annot = IteAnnotation(Not(x.cond),x.elseb,x.thenb)

        # tricky: "else" branch is first in the join because the annotation
        # for join is of the form "if v then second arg else firs arg"
        #res = join_action(else_part,if_part,domain.relations)
        return res
    def decompose(self,pre,post,fail=False):
        return [(pre,[a],post) for a in self.subactions()]
    def get_cond(self):
        if isinstance(self.args[0],ivy_ast.Some):
            ps = list(self.args[0].params())
            fmla = self.args[0].fmla()
            vs = [Variable('V{}'.format(idx),x.sort) for idx,x in enumerate(ps)]
            subst = dict((c,v) for c,v in zip(ps,vs))
            sfmla = substitute_constants_ast(fmla,subst)
            return Exists(vs,sfmla)
        else:
            return self.args[0]

class Ranking(Action):
    def name(self):
        return 'decreases'

class WhileAction(Action):
    def name(self):
        return 'while'
    def __str__(self):
        res = 'while ' + str(self.args[0]) + '\n'
        for inv in self.args[2:]:
            res += 'invariant ' + str(inv.args[0]) + '\n'
        res += bracket_action(self.args[1])
        return res
    def expand(self,domain,pvars):
        modset,pre,post = self.args[1].int_update(domain,pvars)  # TODO:cheaper way to get modset
        if isinstance(self.args[-1],Ranking):
            asserts = self.args[2:-1]
            decreases = self.args[-1]
        else:
            asserts = self.args[2:]
            decreases = None
        assumes = [a.assert_to_assume([AssertAction]) for a in asserts]
        entry_asserts = []
        exit_asserts = []
        if decreases is not None:
            rank = decreases.args[0]
            aux = Symbol('$rank',rank.sort)
            assumes.append(AssumeAction(Equals(aux,rank)))
            assumes[-1].lineno = decreases.lineno
            ltsym = Symbol('<',RelationSort([rank.sort,rank.sort]))
            exit_asserts.append(AssertAction(ltsym(rank,aux)))
            exit_asserts[-1].lineno = decreases.lineno
            entry_asserts.append(AssertAction(Not(ltsym(rank,Symbol('0',rank.sort)))))
            entry_asserts[-1].lineno = decreases.lineno
        havocs = [HavocAction(sym) for sym in modset]
        for h in havocs:
            h.lineno = self.lineno
        res =  Sequence(*(
                asserts +
                havocs +
                assumes +
                [IfAction(self.args[0],Sequence(*(entry_asserts+
                                                     [self.args[1]]+exit_asserts+asserts+[AssumeAction(Or())])),
                          Sequence())]))
#                [ChoiceAction(Sequence(),Sequence(*([AssumeAction(self.args[0])]+entry_asserts+
#                                                     [self.args[1]]+exit_asserts+asserts+[AssumeAction(Or())]))),
#                AssumeAction(Not(self.args[0]))]))
        if decreases is not None:
            res = LocalAction(aux,res)
        return res
            
    def int_update(self,domain,pvars):
        global context
        if isinstance(context,UnrollContext):
            return self.unroll(context.card).int_update(domain,pvars)
        exp = self.expand(domain,pvars)
        res = exp.int_update(domain,pvars)
        return res
    def decompose(self,pre,post,fail=False):
        return self.expand(ivy_module.module,[]).decompose(pre,post,fail)
    def assert_to_assume(self,kinds):
        res = self.clone([self.args[0]]+[x.assert_to_assume(kinds) for x in self.args[1:]])
        self.copy_formals(res)
        return res
    def drop_invariants(self):
        res = self.clone(self.args[:2])
        self.copy_formals(res)
        return res
    def unroll_loops(self,card):
        body = self.args[1].unroll_loops(card)
        return self.unroll(card,body)
    def unroll(self,card,body=None):
        cond = self.args[0]
        while isinstance(cond,And) and len(cond.args) > 0:
            cond = cond.args[0]
        if is_app(cond) and cond.rep.name in ['<','>','<=','>=']:
            idx_sort = cond.args[0].sort
        elif isinstance(cond,Not) and is_eq(cond.args[0]):
            idx_sort = cond.args[0].args[0].sort
        else:
            raise IvyError(self,'cannot determine an index sort for loop')
        cardsort = card(idx_sort)
        if cardsort is None:
            raise IvyError(self,'cannot determine an iteration bound for loop over {}'.format(idx_sort))
        if cardsort > 100:
            assert False
            raise IvyError(self,'cowardly refusing to unroll loop over {} {} times'.format(idx_sort,cardsort))
        res = IfAction(self.args[0],AssumeAction(Or())) # AssumeAction(Not(self.args[0]))
        for idx in range(cardsort):
            res = IfAction(self.args[0],Sequence(body or self.args[1],res))
        self.copy_formals(res)
        return res
            


local_action_ctr = 0

class LocalAction(Action):
    """ Hide some symbols in an action """
    def __init__(self,*args):
        Action.__init__(self,*args)
        global local_action_ctr
        self.unique_id = local_action_ctr
        local_action_ctr += 1
    def name(self):
        return 'local'
    def __str__(self):
        return 'local ' + ','.join(str(a) for a in self.args[0:-1]) + ' ' + bracket_action(self.args[-1])
    def int_update(self,domain,pvars):
        update = self.args[-1].int_update(domain,pvars)
#        syms = used_symbols_asts(self.args[0:-1])
        syms = self.args[0:-1]
#        print "hiding locals : {}".format(syms)
        res =  hide(syms,update)
#        print "local res: {}".format(res)
        return res
    def decompose(self,pre,post,fail=False):
        syms = self.args[0:-1]
        pre,post = (hide_state(syms,p) for p in (pre,post))
        return self.args[-1].decompose(pre,post)

class LetAction(Action):
    """ Bind some symbols in an action """
    def name(self):
        return 'local'
    def __str__(self):
        return 'let ' + ','.join(str(a) for a in self.args[0:-1]) + ' ' + bracket_action(self.args[-1])
    def int_update(self,domain,pvars):
        update = self.args[-1].int_update(domain,pvars)
#        syms = used_symbols_asts(self.args[0:-1])
        subst = dict((a.args[0].rep,a.args[1].rep) for a in self.args[0:-1])
        res = subst_action(update,subst)
#        print "let res: {}".format(res)
        return res

# Havoc all of the non-specification mutable symbols

class CrashAction(Action):
    def name(self):
        return 'crash'
    def __str__(self):
        return 'crash {}'.format(self.args[0])
    def modifies(self,domain=None):
        if domain is None:
            domain = ivy_module.module
        lhs = self.args[0]
        n = lhs.rep
        dfnd = [ldf.formula.defines().name for ldf in domain.definitions]
        def recur(n,res):
            if n in domain.hierarchy:
                for child in domain.hierarchy[n]:
                    cname = iu.compose_names(n,child)
                    if child != "spec" and iu.compose_names(cname,"spec") not in domain.attributes:
                        recur(cname,res)
            else:
                if n in domain.sig.symbols and n not in dfnd:
                    for sym in domain.sig.all_symbols_named(n):
                        if not symbol_is_polymorphic(sym) and not is_interpreted_symbol(sym):
                            res.append(sym)
        syms = []
        recur(n,syms)
        return syms
    def action_update(self,domain,pvars):

        syms = self.modifies(domain)
        havocs = []
        for sym in syms:
            if len(sym.sort.dom) < len(self.args[0].args) or not all(a.sort == s for a,s in zip(self.args[0].args,sym.sort.dom)):
                raise iu.IvyError(self,'action "{}" cannot be applied to {} because of argument mismatch'.format(self,sym))
            args = self.args[0].args + [il.Variable('X{}'.format(idx),s) for idx,s in enumerate(sym.sort.dom[len(self.args[0].args):])]
            havocs.append(HavocAction(sym(*args)))

        seq = Sequence(*havocs)
        return seq.int_update(domain,pvars)
            
# Assign a thunk to a local variable. This action doesn't need an update method because it
# is desugared. 

class ThunkAction(Action):
    def name(self):
        return 'thunk'
    def __str__(self):
        return ('thunk [' + str(self.args[0]) + '] ' + str(self.args[1]) + ' : ' + str(self.args[2]) + ' := ' + str(self.args[3]) + 
                (' ; ' + str(self.args[4]) if len(self.args) > 4 else ''))
    def iter_internal_defines(self):
        lineno = self.lineno if hasattr(self,'lineno') else None
        yield (self.args[0].rep,lineno)
        yield (iu.compose_names(self.args[0].rep,'run'),lineno)

class NativeAction(Action):
    """ Quote native code in an action """
    def __init__(self,*args):
        self.args = list(args)
        self.impure = False
        if isinstance(args[0].code,str) and args[0].code.split('\n')[0].strip() == "impure":
            args[0].code = '\n'.join(args[0].code.split('\n')[1:])
            self.impure = True
    def clone(self,args):
        res = Action.clone(self,args)
        res.impure = self.impure
        return res
    def name(self):
        return 'native'
    def __str__(self):
        return ivy_ast.native_to_string(self.args)
    def int_update(self,domain,pvars):
        return ([], true_clauses(), false_clauses())
        
call_action_ctr = 0

class BindOldsAction(Action):
    def int_update(self,domain,pvars):
        return bind_olds_action(self.args[0].int_update(domain,pvars))
    def __str__(self):
        return 'bindolds {' + str(self.args[0]) + '}'

class CallAction(Action):
    """ Inlines a named state or action """
    def __init__(self,*args):
        Action.__init__(self,*args)
        global call_action_ctr
        self.unique_id = call_action_ctr
        call_action_ctr += 1
    def name(self):
        return 'call'
    def __str__(self):
        actual_returns = self.args[1:]
        return 'call ' + (','.join(str(a) for a in actual_returns) + ' := ' if actual_returns else '') + str(self.args[0])
    def get_callee(self):
        global context
        name = self.args[0].rep
        v = context.get(name)
#        print "v: {}".format(v)
        if not v:
            raise IvyError(self,"no value for {}".format(name))
        return v
    def int_update(self,domain,pvars):
#        print "got here!"
        v = self.get_callee()
        if not isinstance(v,tuple):
            if isinstance(v,Action):
                v = self.apply_actuals(domain,pvars,v)
#                print "called action: {}".format(v)
            else:
                v = state_to_action(v.value)
##                print "called state: {}".format(v)

        return v
    def apply_actuals(self,domain,pvars,v):
        assert hasattr(v,'formal_params'), v
        actual_params = self.args[0].args
        actual_returns = self.args[1:]
#        formal_params = [s.prefix('_') for s in v.formal_params] # rename to prevent capture
#        formal_returns = [s.prefix('_') for s in v.formal_returns] # rename to prevent capture
#        subst = dict(zip(v.formal_params+v.formal_returns, formal_params+formal_returns))
        vocab = list(symbols_asts(actual_params+actual_returns))
        subst = distinct_obj_renaming(v.formal_params+v.formal_returns,vocab)
        for s,t in list(subst.iteritems()):
            subst[old(s)] = old(t)
#        print "apply_actuals: subst: {}".format(subst)
        formal_params = [subst[s] for s in  v.formal_params] # rename to prevent capture
        formal_returns = [subst[s] for s in v.formal_returns] # rename to prevent capture
        v = substitute_constants_ast(v,subst)
#        print "formal_params: {}".format(formal_params)
#        print "formal_returns: {}".format(formal_returns)
#        print "substituted called action: {}".format(v)
        if len(formal_params) != len(actual_params):
            raise IvyError(self,"wrong number of input parameters");
        if len(formal_returns) != len(actual_returns):
            print self
            raise IvyError(self,"wrong number of output parameters");
        for x,y in zip(formal_params,actual_params):
            if x.sort != y.sort and not domain.is_variant(x.sort,y.sort):
                raise IvyError(self,"value for input parameter {} has wrong sort".format(x))
        for x,y in zip(formal_returns,actual_returns):
            if x.sort != y.sort and not domain.is_variant(y.sort,x.sort):
                print y
                print y.sort
                print x.sort
                print self
                raise IvyError(self,"value for output parameter {} has wrong sort".format(x))
        input_asgns = [AssignAction(x,y) for x,y in zip(formal_params,actual_params)]
        output_asgns = [AssignAction(y,x) for x,y in zip(formal_returns,actual_returns)]
        res = Sequence(Sequence(*input_asgns),BindOldsAction(v),Sequence(*output_asgns))
        res = res.int_update(domain,pvars)
#        print "call update: {}".format(res)
        res = hide(formal_params+formal_returns,res)
#        print "after hide: {}".format(res)
        return res
    def prefix_calls(self,pref):
        res = CallAction(*([self.args[0].prefix(pref)] + self.args[1:]))
        if hasattr(self,'lineno'):
            res.lineno = self.lineno
        else: 
            pass
#            print 'no lineno in prefix_calls: {}'.format(self)
        self.copy_formals(res)
        return res        
    def callee(self):
        return self.args[0].relname
    def iter_calls(self):
        yield self.args[0].relname
    def decompose(self,pre,post,fail=False):
        v = self.get_callee()
        if not isinstance(v,Action):
            return []
        actual_params = self.args[0].args
        actual_returns = self.args[1:]
        vocab = list(symbols_asts(actual_params+actual_returns))
        formals = v.formal_params+v.formal_returns
        premap,pre = hide_state_map(formals,pre)
        postmap,post = hide_state_map(formals,post)
        actual_params = [rename_ast(p,premap) for p in actual_params]
        actual_returns = [rename_ast(p,postmap) for p in actual_returns]
        pre = constrain_state(pre,And(*[Equals(x,y) for x,y in zip(actual_params,v.formal_params)]))
        if not fail:
            post = constrain_state(post,And(*[Equals(x,y) for x,y in zip(actual_returns,v.formal_returns)]))
        ren = dict((x,x.prefix('__hide:')) for x in actual_returns)
        post = (post[0],rename_clauses(post[1],ren),post[2])
        callee = v.clone(v.args) # drop the formals
        res = [(pre,[callee],post)]
        # print "decompose call:"
        # print "pre = {}".format(pre)
        # print "callee = {}".format(callee)
        # print "post = {}".format(post)
        return res
        

class RME(AST):
    """ A requires-modifies-ensures clause """
    def __init__(self,*args):
        self.args = args
    def __str__(self):
        args = self.args
        r = (('requires ' + str(args[0]) + ' ') if args[0]!=None else '')
        m = (('modifies ' + str(args[1]) + ' ') if args[1]!=None else '')
        e = 'ensures ' + str(args[2])
        return r + m + e

def entry(ensures = And()):
    return RME(And(),[],ensures)

class TypeCheckConext(ActionContext):
    # if we're just type-checking actions, replace a called action
    # with a null action having the same formals.
    def get(self,x):
        a = ActionContext.get(self,x)
        if a == None:
            return None
        res = Sequence()
        res.formal_params = a.formal_params
        res.formal_returns = a.formal_returns
        return res

def type_check_action(action,domain,pvars = []):
    return
    with TypeCheckConext(domain):
        action.int_update(domain,pvars)

def concat_actions(*actions):
    als = ((a.args if isinstance(a,Sequence) else [a]) for a in actions)
    return Sequence(*(a for al in als for a in al))

def apply_mixin(decl,action1,action2):
    if not hasattr(action1,'lineno'):
        print action1
        print type(action1)
    assert hasattr(action1,'lineno')
    if not hasattr(action2,'lineno'):
        print action2
    assert  hasattr(action2,'lineno')
    name1,name2 = (a.relname for a in decl.args)
    if len(action1.formal_params) != len(action2.formal_params):
        raise IvyError(decl,"mixin {} has wrong number of input parameters for {}".format(name1,name2))
    if len(action1.formal_returns) != len(action2.formal_returns):
        raise IvyError(decl,"mixin {} has wrong number of output parameters for {}".format(name1,name2))
    formals1,formals2 = (a.formal_params + a.formal_returns for a in (action1,action2)) 
    for x,y in zip(formals1,formals2):
        if x.sort != y.sort:
            raise IvyError(decl,"parameter {} of mixin {} has wrong sort".format(str(x),name1))
    subst = dict(zip(formals1,formals2))
    action1_renamed = substitute_constants_ast(action1,subst)
#    print "action1_renamed: {}".format(action1_renamed)
    if isinstance(decl,MixinAfterDef):
        res = concat_actions(action2,action1_renamed)
    else:
        res = concat_actions(action1_renamed,action2)
    res.lineno = action1.lineno
    res.formal_params = action2.formal_params
    res.formal_returns = action2.formal_returns
    if hasattr(action2,'labels'):
        res.labels = action2.labels
    return res

def params_to_str(params):
    params = [(s.drop_prefix('fml:') if s.name.startswith('fml:') else s) for s in params]
    return '(' + ','.join('{}:{}'.format(p.name,p.sort) for p in params) + ')'

def action_def_to_str(name,action):
    res = "action {}".format(name)
    if action.formal_params:
        res += params_to_str(action.formal_params)
    if action.formal_returns:
        res += ' returns' + params_to_str(action.formal_returns)
    res += ' = '
    subs = dict()
    for s in action.formal_params + action.formal_returns:
        if s.name.startswith('fml:'):
            subs[s] = s.drop_prefix('fml:')
    action = rename_ast(action,subs)
    if isinstance(action,Sequence):
        res += str(action)
    else:
        res += '{' + str(action) + '}'
    return res

def has_code(action):
    return any(not isinstance(a,Sequence) for a in action.iter_subactions())

def call_set_rec(action_name,env,res):
    if action_name in res:
        return
    res.add(action_name)
    if action_name in env:
        for c in env[action_name].iter_calls():
            call_set_rec(c,env,res)

def call_set(action_name,env):
    res = set()
    call_set_rec(action_name,env,res)
    return sorted(res)

# adds a list of statements at the beginning of an action.

def prefix_action(self,stmts):
    res = Sequence(*(stmts + [self]))
    self.copy_formals(res)
    res.lineno = self.lineno    
    return res
    
# adds a list of statements at the end of an action.

def postfix_action(self,stmts):
    if len(stmts) == 0:
        return self
    res = Sequence(*([self] + stmts))
    self.copy_formals(res)
    res.lineno = self.lineno    
    return res

# Annotations let us reconstruct an execution trace from a satisfying assignment.
# They contain two kinds of information:

# 1) for each symbol in the update formula corresponding to a program
# variable, original program symbol it corresponds to, and the
# execution point at which it was introduced.

# 2) for each symbol corresponding to a branch decision, the program
# execution point of the branch.

# A primitive execution point is a sequence of numbers. Each number corresponds
# to the child action of an IfAction, ChoiceAction or Sequence (or any future control
# construct that has multiple children). A compound execution point is an if-then-else
# with a condition, and true branch and a false branch.

# There are four basic operations on annotations:

# 1) conjunction -- this just merges the annotations and requires that their domains
# be disjoint

# 2) rename -- takes a map on symbols and simply renames the symbols in the domain

# 3) if-then-else -- takes a condition variable c and two annotations
# x and y, one for the true and one for the false case. It forms v ->
# ite(c,x(v),y(v)) for each domain element common to x and y, and adds
# the branch entry c -> []

# 4) prefix -- adds a numer to the beginning of every execution point

class Annotation(object):
    pass

class EmptyAnnotation(Annotation):
    def __str__(self):
        return '()'

class ConjAnnotation(Annotation):
    def __init__(self,*args):
        self.args = args
    def __str__(self):
        return 'And(' + ','.join(str(a) for a in self.args) + ')'
        
class ComposeAnnotation(Annotation):
    def __init__(self,*args):
        self.args = args
    def __str__(self):
        return (str(self.lineno) if hasattr(self,'lineno') else '') + 'Compose(' + ','.join(str(a) for a in self.args) + ')'

class RenameAnnotation(Annotation):
    def __init__(self,arg,map):
        self.map = map.copy()
        self.arg = arg
    def __str__(self):
        return 'Rename({},'.format(str(self.arg)) + '{' + ','.join('{}:{}'.format(x,y) for x,y in self.map.iteritems()) + '})'

class IteAnnotation(Annotation):
    def __init__(self,cond,thenb,elseb):
        self.cond = cond
        self.thenb = thenb
        self.elseb = elseb
    def __str__(self):
        return 'Ite({},{},{})'.format(self.cond,self.thenb,self.elseb)

def conj_annot(self,other):
    return ConjAnnotation(self,other)
Annotation.conj = conj_annot

def compose_annot(self,other):
    return ComposeAnnotation(self,other)
Annotation.compose = compose_annot

def rename_annot(self,map):
    return RenameAnnotation(self,map) if map else self
Annotation.rename = rename_annot

def ite_annot(self,cond,other):
    return IteAnnotation(cond,self,other)
Annotation.ite = ite_annot

def unite_annot(annot):
    if isinstance(annot,RenameAnnotation):
        return [(annot.map.get(x,x),RenameAnnotation(y,annot.map)) for (x,y) in unite_annot(annot.arg)]
    if not isinstance(annot,IteAnnotation):
        return []
    res = unite_annot(annot.elseb)
    res.append((annot.cond,annot.thenb))
    return res

class AnnotationError(Exception):
    pass

# There is no return action in Ivy. This is just a marker
# for the final state of an action in a counterexample.

class ReturnAction(object):
    def int_update(self,domain,pvars):
        return ([], true_clauses(EmptyAnnotation()), false_clauses(EmptyAnnotation()))
    def __str__(self):
        return 'return'


class IgnoreAction(object):
    pass

def match_annotation(action,annot,handler):
    def recur(action,annot,env,pos=None):
        def show_me():
            print 'lineno: {} annot: {} pos: {}'.format(action.lineno if hasattr(action,'lineno') else None,annot,pos)

        try:
            if isinstance(annot,RenameAnnotation):
                save = dict()
                for x,y in annot.map.iteritems():
                    if x in env:
                        save[x] = env[x]
                    env[x] = env.get(y,y)
                recur(action,annot.arg,env,pos)
                env.update(save)
                return
            if isinstance(action,Sequence):
                if pos is None:
                    pos = len(action.args)
                if pos == 0:
                    if not isinstance(annot,EmptyAnnotation):
                        raise AnnotationError()
                    return
                if isinstance(annot,IteAnnotation):
                    # This means a failure may occur here
                    rncond = env.get(annot.cond,annot.cond)
                    cond = handler.eval(rncond)
                    if cond:
#                        print 'entering then branch {}'.format(pos)
                        recur(action,annot.thenb,env,pos)
                        return
#                        annot = annot.thenb
                    else:
#                        print 'entering else branch {}'.format(pos)
                        recur(action,annot.elseb,env,pos=pos-1)
                        return
                if not isinstance(annot,ComposeAnnotation):
                        raise AnnotationError()
                recur(action,annot.args[0],env,pos-1)
                recur(action.args[pos-1],annot.args[1],env)
                return
            if isinstance(action,IfAction):
                assert isinstance(annot,IteAnnotation),annot
                is_some = isinstance(action.args[0],ivy_ast.Some)
                rncond = env.get(annot.cond,annot.cond)
                try:
                    cond = handler.eval(rncond)
                except KeyError:
                    print '{}skipping conditional'.format(action.lineno)
                    iu.dbg('str_map(env)')
                    iu.dbg('env.get(annot.cond,annot.cond)')
                    return
                if cond:
                    code = action.args[1]
                    if is_some:
                        code = Sequence(AssumeAction(And()),code)
                    recur(code,annot.thenb,env)
                else:
                    if len(action.args) > 2:
                        code = action.args[2]
                        if is_some:
                            code = Sequence(AssumeAction(And()),code)
                        recur(code,annot.elseb,env)
                return
            if isinstance(action,ChoiceAction):
                if isinstance(action,EnvAction) and hasattr(action,'label'):
                    handler.handle(action,env)
                assert isinstance(annot,IteAnnotation)
                annots = unite_annot(annot)
                assert len(annots) == len(action.args)
                for act,(cond,ann) in reversed(zip(action.args,annots)):
                    if handler.eval(cond):
                        if isinstance(action,EnvAction) and not hasattr(action,'label'):
                            callact = act
                            label = act.label if hasattr(act,'label') else 'unknown'
#                            callact = CallAction(ivy_ast.Atom(label,[]))
                            callact = EnvAction(act)
                            callact.label = 'call ' + label
                            handler.handle(callact,env)
                        recur(act,ann,env,None)
                        return
                assert False,'problem in match_annotation'
            if isinstance(action,CallAction):
                handler.handle(action,env)
                callee = ivy_module.module.actions[action.args[0].rep]
                seq = Sequence(IgnoreAction(),callee,ReturnAction())
                recur(seq,annot,env,None)
                return
            if isinstance(action,ReturnAction):
                handler.do_return(action,env)
                return
            if isinstance(action,IgnoreAction):
                return
            if isinstance(action,LocalAction):
                recur(action.args[-1],annot,env)
                return
            if isinstance(action,WhileAction):
                expanded = action.expand(ivy_module.module,[])
                recur(expanded,annot,env)
                return
            if hasattr(action,'failed_action'):
    #            iu.dbg('annot')
    #            iu.dbg('action.failed_action()')
                recur(action.failed_action(),annot,env)
                handler.fail()
                return
            handler.handle(action,env)
        except AnnotationError:
            show_me()
            raise AnnotationError()
    recur(action,annot,dict())
    
def env_action(actname,label=None):
    actnames = sorted(ivy_module.module.public_actions) if actname is None else [actname] 
    racts = []
    for a in actnames:
        act = ivy_module.module.actions[a] if isinstance(a,str) else actname
        ract = Sequence(act,ReturnAction())
        if hasattr(act,'formal_params'):
            ract.formal_params = act.formal_params
        if hasattr(act,'formal_returns'):
            ract.formal_returns = act.formal_returns
        if isinstance(a,str):
            ract.label = a[4:] if a.startswith('ext:') else a
        racts.append(ract)
    action = EnvAction(*racts)
    if label is not None:
        action.label = label
#        action.label = label if not isinstance(actname,str) else actname
    return action


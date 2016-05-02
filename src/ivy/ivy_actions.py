#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_logic import Variable,Constant,Atom,Literal,App,sig,And,Or,Not,EnumeratedSort,Ite,Definition, is_atom, equals, Equals, Symbol,ast_match_lists, is_in_logic

from ivy_logic_utils import to_clauses, formula_to_clauses, substitute_constants_clause,\
    substitute_clause, substitute_ast, used_symbols_clauses, used_symbols_ast, rename_clauses, subst_both_clauses,\
    variables_distinct_ast, is_individual_ast, variables_distinct_list_ast, sym_placeholders, sym_inst, apps_ast,\
    eq_atom, eq_lit, eqs_ast, TseitinContext, formula_to_clauses_tseitin,\
    used_symbols_asts, symbols_asts, has_enumerated_sort, false_clauses, true_clauses, or_clauses, dual_formula, Clauses, and_clauses, substitute_constants_ast, rename_ast, bool_const
from ivy_transrel import state_to_action,new, compose_updates, condition_update_on_fmla, hide, join_action,\
    subst_action, null_update, exist_quant, hide_state, hide_state_map, constrain_state
from ivy_utils import unzip_append, IvyError, IvyUndefined, distinct_obj_renaming
import ivy_ast
from ivy_ast import AST, compose_atoms, MixinAfterDef
import ivy_module

class Schema(AST):
    def __init__(self,defn,fresh):
        self.defn,self.fresh = defn,fresh
        self.args = [defn,fresh]
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
        return (updated,true_clauses(),false_clauses())

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
        for u in domain.updates:
            updated,transrel,precond = u.get_update_axioms(updated,self)
            # TODO: do something with the precondition
#            if transrel:
##                print "updated: {}".format(updated)
##                print "update from axiom: %s" % transrel
            clauses = and_clauses(clauses,transrel)
            pre = or_clauses(pre,precond)
##        print "update clauses: %s" % clauses
        res = (updated,clauses,pre)
        return res
    def update(self,domain,in_scope):
        return self.hide_formals(self.int_update(domain,in_scope))
    def hide_formals(self,update):
        to_hide = []
        if hasattr(self,'formal_params'):
            to_hide += self.formal_params
        if hasattr(self,'formal_returns'):
            to_hide += self.formal_returns
        if to_hide:
             update = hide(to_hide,update)
        return update
    def assert_to_assume(self):
        args = [a.assert_to_assume() if isinstance(a,Action) else a for a in self.args]
        res = self.clone(args)
        if hasattr(self,'formal_params'):
            res.formal_params = self.formal_params
        if hasattr(self,'formal_returns'):
            res.formal_returns = self.formal_returns
        return res
    def prefix_calls(self,pref):
        args = [a.prefix_calls(pref) if isinstance(a,Action) else a for a in self.args]
        res = self.clone(args)
        if hasattr(self,'formal_params'):
            res.formal_params = self.formal_params
        if hasattr(self,'formal_returns'):
            res.formal_returns = self.formal_returns
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
    def decompose(self,pre,post,fail=False):
        return [(pre,[self],post)]


class AssumeAction(Action):
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assume'
    def action_update(self,domain,pvars):
        type_check(domain,self.args[0])
        return ([],formula_to_clauses_tseitin(self.args[0]),false_clauses())

class AssertAction(Action):
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assert'
    def action_update(self,domain,pvars):
        type_check(domain,self.args[0])
#        print type(self.args[0])
        cl = formula_to_clauses(dual_formula(self.args[0]))
#        return ([],formula_to_clauses_tseitin(self.args[0]),cl)
        return ([],true_clauses(),cl)
    def assert_to_assume(self):
        res = AssumeAction(*self.args)
        ivy_ast.copy_attributes_ast(self,res)
        if hasattr(self,'formal_params'):
            res.formal_params = self.formal_params
        if hasattr(self,'formal_returns'):
            res.formal_returns = self.formal_returns
        return res
    
# Ensures is same as Assert except it never gets converted to Assume

class EnsuresAction(AssertAction):
    def assert_to_assume(self):
        return Action.assert_to_assume(self)
    
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
    for atom in eqs_ast(ast):
            t0,t1 = [x.get_sort() for x in atom.args]
            if t0 != t1:
                raise IvyError(atom,
                               "comparison of incompatible types")


def type_ast(domain,ast):
    if is_atom(ast) and ast.rep not in domain.relations and ast.rep != '=':
        return App(ast.rep,ast.args)
    if isinstance(ast,App) and ast.rep in domain.relations:
        return Atom(ast.rep,ast.args)
    return ast

class AssignAction(Action):
    def __init__(self,*args):
        assert len(args) == 2
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assign'
    def __str__(self):
        return str(self.args[0]) + ' := ' + str(self.args[1])
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

        type_check(domain,rhs)
        if is_individual_ast(lhs) != is_individual_ast(rhs):
#            print type(lhs.rep)
#            print str(lhs.rep)
#            print type(lhs.rep.sort)
#            print "lhs: %s: %s" % (lhs,type(lhs))
#            print "rhs: %s: %s" % (rhs,type(rhs))
            raise IvyError(self,"sort mismatch in assignment to {}".format(lhs.rep))

        new_n = new(n)
        args = lhs.args
        dlhs = new_n(*sym_placeholders(n))
        vs = dlhs.args
        eqs = [eq_atom(v,a) for (v,a) in zip(vs,args) if not isinstance(a,Variable)]
        rn = dict((a.rep,v) for v,a in zip(vs,args) if isinstance(a,Variable))
        drhs = substitute_ast(rhs,rn)
        if eqs:
            drhs = Ite(And(*eqs),drhs,n(*dlhs.args))
        new_clauses = Clauses([],[Definition(dlhs,drhs)])
#        print "assign new_clauses = {}".format(new_clauses)
        return ([n], new_clauses, false_clauses())


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
    def action_update(self,domain,pvars):
        lhs = type_ast(domain,self.args[0])
        n = lhs.rep
        new_n = new(n)
        args = lhs.args
        vs = [Variable("X%d" % i,s) for i,s in enumerate(n.sort.dom)]
        eqs = [eq_atom(v,a) for (v,a) in zip(vs,args) if not isinstance(a,Variable)]
        if is_atom(lhs):
            clauses = And(*([Or(Not(Atom(new_n,vs)),Atom(n,vs),eq) for eq in eqs] +
                            [Or(Atom(new_n,vs),Not(Atom(n,vs)),eq) for eq in eqs]))
        elif is_individual_ast(lhs.rep):
            clauses = And(*[Or(eq_atom(type(lhs)(new_n,vs),type(lhs)(n,vs)),eq) for eq in eqs])
        else: # TODO: ???
            clauses = And()
        clauses = formula_to_clauses(clauses)
        return ([n], clauses, false_clauses())


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
        return str(self.args[0]) + '.' + self.args[1] + ' := null'
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
        update = ([],true_clauses(),false_clauses())
        axioms = domain.background_theory(pvars)
        for op in self.args:
            thing = op.int_update(domain,pvars);
#            print "op: {}, thing: {}".format(op,thing)
            update = compose_updates(update,axioms,thing)
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
        return '{' + '| '.join(str(x) for x in self.args) + '}'
    def int_update(self,domain,pvars):
        if determinize and len(self.args) == 2:
            cond = bool_const('___branch:' + str(self.unique_id))
            ite = IfAction(cond,self.args[0],self.args[1])
            return ite.int_update(domain,pvars)
        result = [], false_clauses(), false_clauses()
        for a in self.args:
            result = join_action(result, a.int_update(domain, pvars), domain.relations)
        return result
    def __repr__(self):
        if hasattr(self, 'label'):
            return self.label
        else:
            return super(ChoiceAction, self).__repr__()
    def decompose(self,pre,post,fail=False):
        return [(pre,[a],post) for a in self.args]

class IfAction(Action):
    def name(self):
        return 'if'
    def __str__(self):
        if_part  = 'if ' + str(self.args[0]) + ' {' + str(self.args[1]) + '}'
        else_part = ('\nelse {' + str(self.args[2]) + '}') if len(self.args) >= 3 else ''
        return if_part + else_part
    def subactions(self) :
        if_part = Sequence(AssumeAction(self.args[0]),self.args[1])
        else_action = self.args[2] if len(self.args) >= 3 else Sequence()
        else_part = Sequence(AssumeAction(dual_formula(self.args[0])),else_action)
        return if_part,else_part
    def int_update(self,domain,pvars):
#        update = self.args[1].int_update(domain,pvars)
#        return condition_update_on_fmla(update,self.args[0],domain.relations)
        if_part,else_part = (a.int_update(domain,pvars) for a in self.subactions())
        return join_action(if_part,else_part,domain.relations)
    def decompose(self,pre,post,fail=False):
        return [(pre,[a],post) for a in self.subactions()]
    def cmpl(self):
        args = [self.args[0].compile_with_sort_inference()] + [a.compile() for a in self.args[1:]]
        return self.clone(args)


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
        return 'local ' + ','.join(str(a) for a in self.args[0:-1]) + ' {' + str(self.args[-1]) + '}'
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
        return 'let ' + ','.join(str(a) for a in self.args[0:-1]) + ' {' + str(self.args[-1]) + '}'
    def int_update(self,domain,pvars):
        update = self.args[-1].int_update(domain,pvars)
#        syms = used_symbols_asts(self.args[0:-1])
        subst = dict((a.args[0].rep,a.args[1].rep) for a in self.args[0:-1])
        res = subst_action(update,subst)
#        print "let res: {}".format(res)
        return res

call_action_ctr = 0

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
        return 'call ' + (','.join(str(a) for a in actual_returns) + ':= ' if actual_returns else '') + str(self.args[0])
    def get_callee(self):
        global context
        name = self.args[0].rep
        v = context.get(name)
#        print "v: {}".format(v)
        if not v:
            raise IvyError(self.args[0],"no value for {}".format(name))
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
            raise IvyError(self,"wrong number of output parameters");
        for x,y in zip(formal_params,actual_params):
            if x.sort != y.sort:
                raise IvyError(self,"value for input parameter {} has wrong sort".format(x))
        for x,y in zip(formal_returns,actual_returns):
            if x.sort != y.sort:
                raise IvyError(self,"value for output parameter {} has wrong sort".format(x))
        input_asgns = [AssignAction(x,y) for x,y in zip(formal_params,actual_params)]
        output_asgns = [AssignAction(y,x) for x,y in zip(formal_returns,actual_returns)]
        res = Sequence(*(input_asgns+[v]+output_asgns))
#        print "with parameter assigns: {}".format(res)
        res = res.int_update(domain,pvars)
#        print "call update: {}".format(res)
        res = hide(formal_params+formal_returns,res)
#        print "after hide: {}".format(res)
        return res
    def cmpl(self):
        mas = [a.cmpl() for a in self.args[0].args]
        n = self.args[0].rep
#        print self.args
        res = CallAction(*([ivy_ast.Atom(n,mas)] + [a.cmpl() for a in self.args[1:]]))
        res.lineno = self.lineno
#        print "compiled call action: {}".format(res)
        return res
    def prefix_calls(self,pref):
        res = CallAction(*([self.args[0].prefix(pref)] + self.args[1:]))
        res.lineno = self.lineno
        if hasattr(self,'formal_params'):
            res.formal_params = self.formal_params
        if hasattr(self,'formal_returns'):
            res.formal_returns = self.formal_returns
        return res        
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
        print "decompose call:"
        print "pre = {}".format(pre)
        print "callee = {}".format(callee)
        print "post = {}".format(post)
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
    def get(self,x):
        return null_update()

def type_check_action(action,domain,pvars = []):
    with TypeCheckConext(domain):
        action.int_update(domain,pvars)

def apply_mixin(decl,action1,action2):
    assert hasattr(action1,'lineno')
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
        res = Sequence(action2,action1_renamed)
    else:
        res = Sequence(action1_renamed,action2)
    res.lineno = action1.lineno
    res.formal_params = action2.formal_params
    res.formal_returns = action2.formal_returns
    return res

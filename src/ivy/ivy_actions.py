#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_logic import Variable,Constant,Atom,Literal,App,sig,And,Or,Not,EnumeratedSort,Ite,Definition, is_atom, equals, Equals, Symbol,ast_match_lists, is_in_logic

from ivy_logic_utils import to_clauses, formula_to_clauses, substitute_constants_clause,\
    substitute_clause, substitute_ast, used_symbols_clauses, used_symbols_ast, rename_clauses, subst_both_clauses,\
    variables_distinct_ast, is_individual_ast, variables_distinct_list_ast, sym_placeholders, sym_inst, apps_ast,\
    eq_atom, eq_lit, eqs_ast, TseitinContext, formula_to_clauses_tseitin,\
    used_symbols_asts, symbols_asts, has_enumerated_sort, false_clauses, true_clauses, or_clauses, dual_formula, \
    Clauses, and_clauses, substitute_constants_ast, rename_ast, bool_const, formula_for_clauses
from ivy_transrel import state_to_action,new, compose_updates, condition_update_on_fmla, hide, join_action,\
    subst_action, null_update, exist_quant, hide_state, hide_state_map, constrain_state
from ivy_utils import unzip_append, IvyError, IvyUndefined, distinct_obj_renaming
import ivy_ast
from ivy_ast import AST, compose_atoms
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
    """ Context Manager for symbolically executing actions. """
    def __init__(self):
        name_base = ""
        constraint = Clauses()
        renaming = {}          ## Symbol -> Symbol
        cfg = {}               ## Symbol -> Symbol list
        failures = []          ## fmla list
        control = And()        ## propositional fmla
        dominators = {}        ## Symbol -> Symbol
    def __enter__(self):
        global context
        self.old_context = context
        context = self
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global context
        context = self.old_context
        return False # don't block any exceptions
    def find_action(self,symbol):
        return ivy_module.find_action(symbol)
    def mk_node(self,name,preds):
        self.control = bool_const(name)
        assert self.control not in self.cfg
        self.cfg[self.control] = preds
    def save(self,syms):
        return dict((sym,self.renaming.get(sym,sym)) for sym in syms)
    def restore(self,saved):
        self.renaming.update(saved)
    def get_new(self,symbol):
        return post_subst.get(symbol,new(symbol))
    def rename_fmla(self,fmla):
        return rename_ast(fmla,self.renaming)
    def add_constraint(self,fmla):
        self.constraint.fmlas.append(Implies(self.control,self.rename_fmla(formula_for_clauses(fmla))))
    def add_failure(self,fmla):
        self.failures.append(And(self.control,self.rename_fmla(formula_for_clauses(fmla))))
    def add_definition(self,defn):
        defn = self.rename_fmla(defn)
        assert defn.defines() not in self.constraint.def_idx
        self.constraint.defs.append(defn)
        self.constraint.def_idx[defn.defines()] = defn
    def update_symbols(updated,action):
        syms2 = [self.get_new(sym1) for sym1 in updated]
        for u in im.module.updates:
            u.get_update_axioms(updated,action)
            clauses = and_clauses(clauses,transrel)
            pre = or_clauses(pre,precond)
        for sym1,sym2 in zip(updated,syms2):
            self.renaming[sym1] = sym2
            del self.renaming[new(sym1)]
        mid = [sym1 for (sym1,sym2) in zip(updated,syms2) if sym2.is_skolem()]
        mid_ax = clauses_using_symbols(mid,im.module.background_theory())
        self.constraint.fmlas.extend(mid_ax)

    def new_state(self,clauses, exact = False, domain = None, expr = None):
        domain = self.domain if self.domain is not None else domain
        assert domain is not None
        return domain.new_state(clauses)
    def type_checking(self):
        return False
    def precond(controls):
        ancs = get_ancestors(controls)
        cnstrs = [fmla for fmla in self.constraint.fmlas if fmla.args[0] in ancs]
        flow_cnstrs = [Implies(n,Or(cfg[n])) for n in ancs if n in self.cfg]
        res = Clauses(cnstrs+flow_cnstrs,self.constraint.defs)


context = ActionContext()

def ensures_to_transrel(ensures,updated):
    renaming = dict()
    for s in updated:
        renaming[s] = new(s)
    for s in used_symbols_ast(ensures):
        if is_old(s):
            renaming[s] = old_of(s)
    return rename_clauses(ensures,renaming)

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
    def match(self,action,updated):
        """ if action matches pattern, return the axioms, else None """
        subst = dict()
        if self.pattern.match(action,self.placeholders.args,subst):
            axioms_as_clause_sets = (formula_to_clauses(x) for x in )
            fail,cnstr = (subst_both_clauses(x,subst) for x in (dual_formula(self.precond),self.transrel))
            cnstr = old_to_new(cnstr,updated)
            context.add_failure(fail)
            context.add_constraint(cnstr)
            return true
        return false

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
                for p in self.patterns.args:
                    if p.match(action,updated):
                        return
                raise IvyError(action,'No matching update axiom for ' + str(x))

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
    def update(self,domain=None,in_scope=None):
        with ActionContext():
            self.execute()
            res = (self.modifies(),context.constraint,context.get_fail())
            return self.hide_formals(res)
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
    def decompose(self,pre,post,fail=False):
        return [(pre,[self],post)]


def check_can_assert(fmla,ast):
    check_can_assume(fmla,ast)
    logic = ivy_module.logic()
    if not is_in_logic(Not(fmla),logic):
        raise IvyError(ast,"This formula is not in logic {} when negated.".format(logic))

def check_can_assume(fmla,ast):
    logic = ivy_module.logic()
    if not is_in_logic(fmla,logic):
        raise IvyError(ast,"This formula is not in logic {}.".format(logic))

class AssumeAction(Action):
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assume'
    def execute(self):
        fmla = self.args[0]
        check_can_assume(fmla,self)
        context.add_constraint(fmla)

class AssertAction(Action):
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assert'
    def execute(self):
        fmla = self.args[0]
        check_can_assert(fmla,self)
        in_control = context.control
        context.mk_node(context.base + '_0',[in_control])
        context.add_constraint(dual_formula(fmla))
        context.failures.append(context.control)
        context.mk_node(context.base + '_1',[in_control])
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
    return Iff(ast1,ast2)

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
        return [self.args[0].rep]
    def execute(self):
        lhs,rhs = self.args
        n = lhs.rep

        # TODO: is this needed?
        if lhs.sort != rhs.sort:
            raise IvyError(self,"sort mismatch in assignment to {}".format(lhs.rep))

        new_n = new(n)
        args = lhs.args
        dlhs = new_n(*sym_placeholders(n))
        vs = dlhs.args
        eqs = [equiv_ast(v,a) for (v,a) in zip(vs,args) if not isinstance(a,Variable)]
        rn = dict((a.rep,v) for v,a in zip(vs,args) if isinstance(a,Variable))
        drhs = substitute_ast(rhs,rn)
        if eqs:
            drhs = Ite(And(*eqs),drhs,n(*dlhs.args))
        context.add_definition(Definition(dlhs,drhs))
        context.update_symbols([n],self)

class SetAction(Action):
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'set'
    def to_assign(self):
        lit = self.args[0]
        n = lit.atom.relname
        return AssignAction(n,And() if lit.polarity else Or())
    def modifies(self):
        return self.to_assign().modifies()
    def execute(self):
        return self.to_assign().execute()

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
        return [self.args[0].rep]
    def execute(self,domain,pvars):
        lhs = type_ast(domain,self.args[0])
        n = lhs.rep
        new_n = new(n)
        args = lhs.args
        vs = [Variable("X%d" % i,s) for i,s in enumerate(n.sort.dom)]
        eqs = [eq_atom(v,a) for (v,a) in zip(vs,args) if not isinstance(a,Variable)]
        if is_atom(lhs):
            fmla = And(*([Or(Not(Atom(new_n,vs)),Atom(n,vs),eq) for eq in eqs] +
                            [Or(Atom(new_n,vs),Not(Atom(n,vs)),eq) for eq in eqs]))
        elif is_individual_ast(lhs.rep):
            fmla = And(*[Or(eq_atom(type(lhs)(new_n,vs),type(lhs)(n,vs)),eq) for eq in eqs])
        else: # TODO: ???
            fmla = And()
        context.add_constraint(fmla)


def make_field_update(self,l,f,r):
    if not f.is_relation() or len(f.sort.dom) != 2:
        raise IvyError(self, "field " + str(f) + " must be a binary relation")
    v = Variable('X',f.sort.dom[1])
    aa = AssignAction(f(l,v),r(v))
    return aa.execute()

class AssignFieldAction(Action):
    def __init__(self,*args):
        assert len(args) == 3
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'assign_field'
    def __str__(self):
        return str(self.args[0]) + '.' + str(self.args[1]) + ' := ' + str(self.args[2])
    def modifies(self):
        return [self.args[1]]
    def execute(self):
        l,f,r = self.args
        make_field_update(self,l,f,lambda v: Equals(v,r))

class NullFieldAction(Action):
    def __init__(self,*args):
        assert len(args) == 2
        self.args = args
    sort_infer_root = True
    def name(self):
        return 'null_field'
    def __str__(self):
        return str(self.args[0]) + '.' + self.args[1] + ' := null'
    def modifies(self):
        return [self.args[1]]
    def execute(self):
        l,f = self.args
        make_field_update(self,l,f,lambda v: Or())

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
    def execute(self,domain,pvars):
        l,lf,r,rf = self.args
        return make_field_update(self,l,lf,lambda v: rf(r,v))

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
    def execute(self):
        inst = self.args[0]
        if hasattr(im.module,'macros'):
            act = instantiate_macro(inst,im.module.macros)
            if act:
                res = act.compile().execute()
                return
        if inst.relname in im.module.schemata:
            fmla = im.module.schemata[inst.relname].get_instance(inst.args)
            context.add_constraint(fmla)
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
    def execute(self):
        for i,op in enumerate(self.args):
            context.push(i)
            op.execute()
            context.pop()
    def __call__(self,interpreter):
        for op in self.args:
            interpreter.execute(op)
    def decompose(self,pre,post,fail=False):
        return [(pre,self.args,post)]
        
determinize = False

def set_determinize(t):
    global determinize
    determinize = t

def collect_mods(actions):
    return union_lists(*[a.modifies() for a in actions])

class ChoiceAction(Action):
    def __init__(self,*args):
        Action.__init__(self,*args)
        self.modifies_memo = collect_mods(self.args)
    def name(self):
        return 'choice'
    def __str__(self):
        return 'if * {' + '} else if * { '.join(str(x) for x in self.args[:-1]) + '} else {' + str(self.args[-1]) + '}'
    def modifies(self):
        return list(self.modifies_memo)
    def execute(self):
        controls = []
        ph = lambda sym: sym(*sym_placeholders(sym))
        phi_nodes = dict((sym,ph(sym)) for sym in self.modifies())
        in_control = context.control
        for i,arg in enumerate(self.args):
            mods = arg.modifies()
            save = context.save(mods)
            context.mk_node(context.base + '_' + str(i), [control])
            context.push(i)
            controls.append(context.control)
            for sym in mods:
                new_sym = sym.rename(context.base + '_' + str(i) + '_' + sym.name)
                context.renaming[new(sym)] = new_sym
                phi_nodes[sym] = Ite(control,ph(new_sym),phi_nodes[sym])
            arg.execute()
            context.pop()
            context.restore(save)
        context.mk_node(context.base,controls,dominator=in_control)
        for sym,phi in phi_nodes.iteritems():
            context.add_definition(Definition(ph(sym),phi))
        context.update_symbols(self.modifies(),self)
    def __repr__(self):
        if hasattr(self, 'label'):
            return self.label
        else:
            return super(ChoiceAction, self).__repr__()
    def decompose(self,pre,post,fail=False):
        return [(pre,[a],post) for a in self.args]

class IfAction(Action):
    def __init__(self,*args):
        Action.__init__(self,*args)
        self.choice_action = ChoiceAction(*self.subactions())
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
    def modifies(self):
        self.choice_action.modifies()
    def execute(self):
        check_can_assert(self.args[0],self)
        self.choice_action.execute()
    def decompose(self,pre,post,fail=False):
        return [(pre,[a],post) for a in self.subactions()]

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
    def modifies():
        loc_syms = set(self.args[0:-1])
        return [sym for sym in self.args[-1].modifies if sym not in loc_syms]
    def execute(self):
        save = context.save(self.args[0:-1])
        for sym in self.args[0:-1]:
            context.rename(sym,sym.prefix(context.base + '_'))
        self.args[-1].execute()
        context.restore(save)
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

# assign one symbol to another

def asgn(x,y):
    ph = lambda sym: sym(*sym_placeholders(sym))
    return Definition(ph(x),ph(y))

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
        v = context.find_action(name)
        if not v:
            raise IvyError(self.args[0],"no value for {}".format(name))
        return v
    def modifies(self):
        v = get_callee()
        assert hasattr(v,'formal_params'), v
        loc_syms = set(v.formal_params + v.formal_returns)
        return union_lists([sym for sym in self.args[0].modifies() if sym not in loc_syms],self.args[1:])
    def execute(self):
        v = get_callee()
        assert hasattr(v,'formal_params'), v
        actual_params = self.args[0].args
        actual_returns = self.args[1:]
        formal_params = v.formal_params
        formal_returns = v.formal_returns

        if len(formal_params) != len(actual_params):
            raise IvyError(self,"wrong number of input parameters");
        if len(formal_returns) != len(actual_returns):
            raise IvyError(self,"wrong number of output parameters");

        save = context.save(formal_params + formal_returns)
        context.push(0)

        for x,y in zip(formal_params,actual_params):
            if x.sort != y.sort:
                raise IvyError(self,"value for input parameter {} has wrong sort".format(x))
            # TRICKY: this prevents capture of actual param occurring in formal param
            context.add_definition(asgn(x.prefix(context.base),y))
            context.renaming[x] = x.prefix(context.base)

        v.execute()

        for x,y in zip(formal_returns,actual_returns):
            if x.sort != y.sort:
                raise IvyError(self,"value for output parameter {} has wrong sort".format(x))
            context.add_definition(asgn(new(y),x))

        context.pop()
        context.restore(save)
        context.update_symbols(self.modifies(),self)

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
    def type_checking(self):
        return True

def type_check_action(action,domain,pvars):
    with TypeCheckConext(domain):
        action.execute()

def mixin_before(decl,action1,action2):
    assert hasattr(action1,'lineno')
    assert  hasattr(action2,'lineno')
    name1,name2 = (a.relname for a in decl.args)
    if len(action1.formal_params) != len(action2.formal_params):
        raise IvyError(decl,"mixin {} has wrong number of input parameters for {}".format(name1,name2))
    if len(action1.formal_returns) != 0:
        raise IvyError(decl,"mixin {} must not have return parameters")
    for x,y in zip(action1.formal_params,action2.formal_params):
        if x.sort != y.sort:
            raise IvyError(decl,"parameter {} of mixin {} has wrong sort".format(str(x),name1))
    subst = dict(zip(action1.formal_params,action2.formal_params))
    action1_renamed = substitute_constants_ast(action1,subst)
#    print "action1_renamed: {}".format(action1_renamed)
    res = Sequence(action1_renamed,action2)
    res.lineno = action1.lineno
    res.formal_params = action2.formal_params
    res.formal_returns = action2.formal_returns
    return res

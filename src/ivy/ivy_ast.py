#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Ivy abstract syntax trees.
"""

from ivy_utils import flatten, gen_to_set, UniqueRenamer, compose_names, split_name, IvyError
import ivy_utils as iu
import ivy_logic
import re

class AST(object):
    """
    Base class for abstract syntax.
    """
    def __init__(self,*args):
        self.args = args
    def clone(self,args):
       res = type(self)(*args)
       if hasattr(self,'lineno'):
           res.lineno = self.lineno
       return res

class Symbol(AST):
    def __init__(self,rep,sort):
        assert isinstance(rep,str)
        self.rep = rep
        self.sort = sort
    def __repr__(self):
        return self.rep
    def __hash__(self):
        return hash(self.rep)
    def __eq__(self,other):
        return type(self) == type(other) and self.rep == other.rep

def nary_repr(op,args):
    res = (' ' + op + ' ').join([repr(a) for a in args])
    return ('(' + res + ')') if len(args) > 1 else res

class Formula(AST):
    """
    Base class for formulas.
    """
    def __init__(self,*args):
        self.args = list(args) # make args mutable
    
class And(Formula):
    """
    Conjunction of formulas.
    """
    def __repr__(self):
        if not self.args:
            return "true"
        return nary_repr('&',self.args)

class Or(Formula):
    """
    Disjunction of a formulas.
    """
    def __repr__(self):
        if not self.args:
            return "false"
        return nary_repr('|',self.args)

class Not(Formula):
    """
    Negation of a formula.
    """
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    def __repr__(self):
        if isinstance(self.args[0],Atom) and is_equals(self.args[0].rep):
            return ' ~= '.join(repr(x) for x in self.args[0].args)
        return '~' + repr(self.args[0])

class Let(Formula):
    """
    Formula of the form let p(X,...,Z) <-> fmla[X,...,Z], ... in fmla
    """
    def __init__(self,*args):
        assert len(args) >= 1
        self.args = args
    def __repr__(self):
        res = repr(self.args[-1])
        if len(self.args) > 1:
            res = 'let ' + ', '.join([repr(x) for x in self.args[0:-1]]) + ' in ' + res 
        return res
    def defines(self):
        return self.args[0].relname
    def to_constraint(self):
        return Iff(*self.args)
    

class Definition(Formula):
    """
    Formula of the form p(X,...,Z) <-> fmla[X,...,Z]
    """
    def __init__(self,*args):
        assert len(args) == 2
        self.args = args
    def __repr__(self):
        return ' = '.join([repr(x) for x in self.args])
    def defines(self):
        return self.args[0].rep
    def to_constraint(self):
        if isinstance(self.args[0],App):
            return Atom(equals,self.args)
        return Iff(*self.args)

class Implies(Formula):
    """
    Implication of formulas
    """
    def __init__(self,*args):
        assert len(args) == 2
        self.args = args
    def __repr__(self):
        return ' -> '.join([repr(x) for x in self.args])

class Iff(Formula):
    """
    Implication of formulas
    """
    def __init__(self,*args):
        assert len(args) == 2
        self.args = args
    def __repr__(self):
        return ' <-> '.join([repr(x) for x in self.args])

class Ite(AST):
    """
    If-the-else expression. 
    """
    def __init__(self,*args):
        assert len(args) == 3
        self.args = args
    def __repr__(self):
        return '(' + repr(self.args[1]) + ' if ' + repr(self.args[0]) + ' else ' + repr(self.args[2]) + ')'

class Quantifier(Formula):
    def __init__(self, bounds, body):
        self.bounds = bounds
        self.args = [body]

class Forall(Quantifier):
    pass

class Exists(Quantifier):
    pass

class Atom(Formula):
    """
    A n-ary relation symbol applied to n terms
    """
    def __init__(self, relsym, *terms):
        self.rep = relsym
        self.args = flatten(terms)
    def __repr__(self):
        if is_equals(self.rep) and len(self.args) == 2:
            return ' = '.join(repr(x) for x in self.args)
        if not self.args:
            return str(self.rep)
        return str(self.rep) + "(" + ', '.join(str(x) for x in self.args)  + ")"
    def clone(self,args):
       return type(self)(self.rep,list(args))
    def __eq__(self,other):
        return type(self) == type(other) and self.rep == other.rep and self.args == other.args
    def is_numeral(self):
        return False
    def prefix(self,s):
        return Atom(s+self.rep,*self.args)
    # following for backward compat
    @property
    def terms(self):
        return self.args
    @terms.setter
    def terms(self,value):
        self.args = value
    @property
    def relname(self):
        return self.rep
    @relname.setter
    def relname(self,value):
        self.rep = value


class Term(AST):
    def __eq__(self, other):
        return _eq_lit(self, other)

    def __ne__(self, other):
        return _neq_lit(self, other)


class Old(Term):
    def __init__(self, term):
        self.args = [term]
    def __repr__(self):
        return 'old ' + repr(self.args[0])

class App(Term):
    def __init__(self, funsym, *terms):
        self.rep = funsym
        self.args = flatten(terms)
    def __repr__(self):
        if self.args:
            res =  repr(self.rep) + "(" + ', '.join(repr(x) for x in self.args)  + ")"
        else:
            res = repr(self.rep)
        if hasattr(self,'sort'):
            res += ':' + repr(self.sort)
        return res
    def clone(self,args):
       return type(self)(self.rep,*args)
    def __eq__(self,other):
        return type(self) == type(other) and self.rep == other.rep and self.args == other.args
    def is_numeral(self):
        return self.rep.rep[0].isdigit()
    def prefix(self,s):
        res = App(s + self.rep)
        if hasattr(self,'sort'):
            res.sort = self.sort
        return res


Constant = App  # compat

class Variable(Term):
    def __init__(self, rep, sort):
        assert isinstance(rep,str)
#        assert isinstance(sort,Sort)
        self.rep = rep
        self.args = []
        self.sort = sort
    def __repr__(self):
        res =  self.rep
        res += ':' + str(self.sort)
        return res
    def clone(self,args):
        return self
    def __eq__(self,other):
        return type(self) == type(other) and self.rep == other.rep
    def __hash__(self):
        return hash(self.rep)
    def to_const(self,prefix):
        res = App(prefix + self.rep)
        if hasattr(self,'sort'):
            res.sort = self.sort
        return res


class Literal(AST):
    """
    Either a positive or negative atomic formula. Literals are not
    formulas! Use Not(Atom(...)) to get a formula.
    """
    def __init__(self, polarity, atom):
#        assert isinstance(atom,Atom) or isinstance(atom,And) and len(atom.args) == 0
        self.polarity = polarity
        self.atom = atom
    def __repr__(self):
        return ('~' if self.polarity == 0 else '') + repr(self.atom)
    def __invert__(self):
        """
        x.__invert__() <==> ~x
        Used to negate the a literal.
        """
        return Literal(1 - self.polarity, self.atom)
    def clone(self,args):
        return Literal(self.polarity,*args)
    def __eq__(self,other):
        return type(self) == type(other) and self.polarity == other.polarity and self.args == other.args
    @property
    def args(self):
        return [self.atom]
    @args.setter
    def args(self,value):
        assert len(value) == 1
        self.atom = value[0]

def _eq_lit(x, y):
    return Literal(1, Atom(equals, (x, y)))
def _neq_lit(x, y):
    return Literal(0, Atom(equals, (x, y)))


class Predicate(object):
    """
    A predicate is a literal factory. It's not an AST object.
    """
    def __init__(self, name, arity):
        self.name = name
        self.arity = arity
    def __call__(self, *terms):
        assert len(terms) == self.arity
        return Literal(1, Atom(self.name, terms))


class Sort(AST):
    pass

class EnumeratedSort(Sort):
    def __init__(self,extension):
        self.extension = extension
        self.dom = []
    def __repr__(self):
        return '{' + ','.join(self.extension) + '}'
    def defines(self):
        return self.extension
    def range(self):
        return self

class ConstantSort(Sort):
    def __init__(self,rep,prover_sort = None):
        self.rep,self.prover_sort = rep,prover_sort
        self.rng = self
        self.dom = []
    def __repr__(self):
        return self.rep
    def __str__(self):
        return self.rep
    def __eq__(self,other):
        return type(other) == type(self) and other.rep == self.rep
    def defines(self):
        return []
    def range(self):
        return self

UninterpretedSort = ConstantSort

class FunctionSort(Sort):
    def __init__(self,dom,rng):
        self.dom,self.rng = dom,rng
    def __repr__(self):
        return ' * '.join(repr(s) for s in self.dom) + ' -> ' + repr(self.rng)
    def defines(self):
        return []
    def range(self):
        return self.rng

class RelationSort(Sort):
    def __init__(self,dom):
        self.dom = dom
    def __repr__(self):
        return ' * '.join(repr(s) for s in self.dom) 
    def defines(self):
        return []
    
class Tuple(AST):
    def __repr__(self):
        return '(' + ','.join(repr(s) for s in self.args) + ')' 

def lineno(c):
    try:
        return c.lineno
    except:
        return None

class Decl(AST):
    def __init__(self,*args):
        self.args = args
    def __repr__(self):
        res = self.name() + ' ' + ','.join([repr(a) for a in self.args])
        return res
    def defines(self):
        return []

class ModuleDecl(Decl):
    def name(self):
        return 'module'
    def defines(self):
        return [(c.defines(),lineno(c)) for c in self.args]
    def __repr__(self):
        return 'module ' + ','.join(repr(d.args[0]) + ' = {\n' + repr(d.args[1]) + '\n}' for d in self.args)

class MacroDecl(Decl):
    def name(self):
        return 'macro'
    def defines(self):
        return [(c.defines(),lineno(c)) for c in self.args]
    def __repr__(self):
        return 'macro ' + ','.join(repr(d.args[0]) + ' = {\n' + repr(d.args[1]) + '\n}' for d in self.args)

class LabeledFormula(AST):
    @property
    def label(self):
        return self.args[0]
    @property
    def formula(self):
        return self.args[1]
    def __str__(self):
        return '[' + str(self.label) + '] ' + str(self.formula) if self.label else str(self.formula)

class AxiomDecl(Decl):
    def name(self):
        return 'axiom'

class ConjectureDecl(Decl):
    def name(self):
        return 'conjecture'

class SchemaDecl(Decl):
    def name(self):
        return 'schema'
    def defines(self):
        return [(c.defines(),lineno(c)) for c in self.args]

class Instantiation(AST):
    def __init__(self,*args):
        self.args = args
    def __repr__(self):
        return ' : '.join(repr(x) for x in self.args) if self.args[0] else repr(self.args[1])

class InstantiateDecl(Decl):
    def name(self):
        return 'instantiate'

class RelationDecl(Decl):
    def name(self):
        return 'relation'
    def defines(self):
        return [(c.relname,lineno(c)) for c in self.args if c.relname not in iu.polymorphic_symbols]

class ConstantDecl(Decl):
    def name(self):
        return 'individual'
    def defines(self):
        return [(c.rep,lineno(c)) for c in self.args if c.rep not in iu.polymorphic_symbols]

class DerivedDecl(Decl):
    def name(self):
        return 'derived'
    def defines(self):
        return [(c.defines(),lineno(c)) for c in self.args]

class ProgressDecl(Decl):
    def name(self):
        return 'progress'
    def defines(self):
        return [(c.defines(),lineno(c)) for c in self.args]

class RelyDecl(Decl):
    def name(self):
        return 'rely'
    def defines(self):
        return []

class MixOrdDecl(Decl):
    def name(self):
        return 'mixord'
    def defines(self):
        return []

class ConceptDecl(Decl):
    def name(self):
        return 'concept'
    def defines(self):
        return [(c.defines(),lineno(c)) for c in self.args]

class ActionDecl(Decl):
    def name(self):
        return 'action'
    def defines(self):
        return [(c.defines(),lineno(c)) for c in self.args]

class StateDecl(Decl):
    def name(self):
        return 'state'

class InitDecl(Decl):
    def name(self):
        return 'init'

class UpdateDecl(Decl):
    def name(self):
        return 'update'

class TypeDecl(Decl):
    def name(self):
        return 'type'
    def defines(self):
        return self.args[0].defines()

class AssertDecl(Decl):
    def name(self):
        return 'assert'
    def defines(self):
        return []

class InterpretDecl(Decl):
    def name(self):
        return 'interpret'
    def defines(self):
        return []

class MixinDecl(Decl):    
    def name(self):
        return 'mixin'
    def defines(self):
        return []
    
class MixinDef(AST):
    def mixer(self):
        return self.args[0].relname
    def mixee(self):
        return self.args[1].relname
    
class MixinBeforeDef(MixinDef):
    pass
    
class MixinAfterDef(MixinDef):
    pass

class IsolateDecl(Decl):    
    def name(self):
        return 'isolate'
    def defines(self):
        return [(c.name(),lineno(c)) for c in self.args]
    
class IsolateDef(AST):
    def name(self):
        return self.args[0].relname
    def verified(self):
        return self.args[1:len(self.args)-self.with_args]
    def present(self):
        return self.args[len(self.args)-self.with_args:]

    def __repr__(self):
        return (','.join(repr(a) for a in self.verified()) +
                  (('with ' + ','.join(repr(a) for a in self.present())) if self.present() else ''))
    
class ExportDecl(Decl):    
    def name(self):
        return 'export'
    def defines(self):
        return []
    
class ExportDef(AST):
    def exported(self):
        return self.args[0].relname
    def scope(self):
        return self.args[1].relname
    def __repr__(self):
        return self.exported() + (' from {}'.format(self.scope()) if self.scope() else '')

class DelegateDecl(Decl):    
    def name(self):
        return 'delegate'
    def defines(self):
        return []
    
class DelegateDef(AST):
    def delegated(self):
        return self.args[0].relname
    def delegee(self):
        if len(self.args) > 1:
            return self.args[1].relname
        return None
    def __repr__(self):
        s = self.delegated()
        if len(self.args) > 1:
            s += ' -> ' + self.delegee
        return s

class TypeDef(Definition):
    def __init__(self,name,sort):
        self.args = [name,sort]
    def __repr__(self):
        return self.args[0] + ' = ' + repr(self.args[1])
    def defines(self):
        syms =  [self.args[0]] + self.args[1].defines()
        return [(sym,lineno(self)) for sym in syms]

class ActionDef(Definition):
    def __init__(self,atom,action,formals=[],returns=[]):
        # we rename the formals to avoid name capture
        self.formal_params = [s.prefix('fml:') for s in formals]
        self.formal_returns = [s.prefix('fml:') for s in returns]
        if formals or returns:
            subst = dict((x.rep,y.rep) for x,y in zip(formals+returns,self.formal_params+self.formal_returns))
            action = subst_prefix_atoms_ast(action,subst,None,None)
        self.args = [atom,action]
    def __repr__(self):
        return self.args[0].relname + ' = ' + str(self.args[1])
    def defines(self):
        return self.args[0].relname
    def clone(self,args):
        res = ActionDef(args[0],args[1])
        res.formal_params = self.formal_params
        res.formal_returns = self.formal_returns
        return res
    def rewrite(self,rewrite):
        res = self.clone(ast_rewrite(self.args,rewrite))
        if hasattr(self,'formal_params'):
            res.formal_params = [rewrite_param(p,rewrite) for p in self.formal_params]
        if hasattr(self,'formal_returns'):
            res.formal_returns = [rewrite_param(p,rewrite) for p in self.formal_returns]
        return res

def rewrite_param(p,rewrite):
    res = App(p.rep)
    res.sort = ast_rewrite(p.sort,rewrite)
    return res

class StateDef(Definition):
    def __init__(self,name,state):
        self.args = [Atom(name,[]),state]
    def __repr__(self):
        return self.args[0].relname + ' = ' + repr(self.args[1])

# predefined things

universe = 'S'

equals = Symbol('=',RelationSort([None,None]))

def Equals(x,y):
    return Atom(equals,x,y)

def is_equals(symbol):
    return isinstance(symbol,Symbol) and symbol.rep == '='

def is_enumerated(term):
    return isinstance(term.get_sort(),EnumeratedSort)

def app_to_atom(app):
    if isinstance(app,Old) or isinstance(app,Quantifier):
        return app
    res = Atom(app.rep,app.args)
    if hasattr(app,'lineno'):
        res.lineno = app.lineno
    return res

def apps_to_atoms(apps):
    return [app_to_atom(app) for app in apps]

# AST rewriting

name_parser = re.compile(r'[^\[\]]+|\[[^\[\]]*\]')


def str_subst(s,subst):
    names = split_name(s)
    return compose_names(subst.get(names[0],names[0]),*names[1:])
#    return subst.get(s,s)

def subst_subscripts_comp(s,subst):
    assert s!=None
#    print 's: {} subst: {}'.format(s,subst)
    g = name_parser.findall(s)
#    print 'g: {}'.format(g)
    if not g:
        return s
    res =  str_subst(g[0],subst) + ''.join(('[' + str_subst(x[1:-1],subst) + ']' if x.startswith('[') else x) for x in g[1:])
#    print "res: {}".format(res)
    return res

def subst_subscripts(s,subst):
#    return compose_names(*[subst_subscripts_comp(t,subst) for t in split_name(s)])
    return subst_subscripts_comp(s,subst)


class AstRewriteSubstConstants(object):
    def __init__(self,subst):
        self.subst = subst
    def rewrite_name(self,name):
        return name
    def rewrite_atom(self,atom):
        subst = self.subst
        return subst[atom.rep] if not atom.args and atom.rep in subst else atom

class AstRewriteSubstConstantsParams(object):
    def __init__(self,subst,psubst):
        self.subst = subst
        self.psubst = psubst
    def rewrite_name(self,name):
        return subst_subscripts(name,self.psubst)
    def rewrite_atom(self,atom):
        subst = self.subst
        return subst[atom.rep] if not atom.args and atom.rep in subst else atom

class AstRewriteSubstPrefix(object):
    def __init__(self,subst,pref,to_pref = None):
        self.subst,self.pref,self.to_pref = subst,pref,to_pref
    def rewrite_name(self,name):
        return subst_subscripts(name,self.subst)
    def rewrite_atom(self,atom):
        return compose_atoms(self.pref,atom) if self.pref and (self.to_pref == None or atom.rep in self.to_pref) else atom

class AstRewritePostfix(object):
    def __init__(self,post):
        self.post = post
    def rewrite_name(self,name):
        return name
    def rewrite_atom(self,atom):
        return compose_atoms(atom,self.post)

class AstRewriteAddParams(object):
    def __init__(self,params):
        self.params = params
    def rewrite_name(self,name):
        return name
    def rewrite_atom(self,atom):
        return atom.clone(atom.args + self.params)

def ast_rewrite(x,rewrite):
    if isinstance(x,str):
        return rewrite.rewrite_name(x)
    if isinstance(x,list):
        return [ast_rewrite(e,rewrite) for e in x]
    if isinstance(x,tuple):
        return tuple(ast_rewrite(e,rewrite) for e in x)
    if isinstance(x,Variable):
        return Variable(x.rep,rewrite.rewrite_name(x.sort))
    if isinstance(x,Atom) or isinstance(x,App):
#        print "rewrite: x = {!r}, type(x.rep) = {!r}".format(x,type(x.rep))
        atom = type(x)(rewrite.rewrite_name(x.rep),ast_rewrite(x.args,rewrite))
        copy_attributes_ast(x,atom)
        if hasattr(x,'sort'):
            atom.sort = rewrite.rewrite_name(x.sort)
        return rewrite.rewrite_atom(atom)
    if isinstance(x,Literal):
        return Literal(x.polarity,ast_rewrite(x.atom,rewrite))
    if isinstance(x,Quantifier):
        return type(x)(ast_rewrite(x.bounds,rewrite),ast_rewrite(x.args[0],rewrite))
    if hasattr(x,'rewrite'):
        return x.rewrite(rewrite)
    if isinstance(x,LabeledFormula):
        arg0 = x.args[0]
        if x.args[0] == None:
            if isinstance(rewrite,AstRewriteSubstPrefix) and rewrite.pref != None:
                arg0 = Atom(rewrite.pref,[])
        else:
            arg0 = rewrite.rewrite_atom(x.args[0])
        res = x.clone([arg0,ast_rewrite(x.args[1],rewrite)])
        return res
    if hasattr(x,'args'):
        return x.clone(ast_rewrite(x.args,rewrite)) # yikes!
    print "wtf: {} {}".format(x,type(x))
    assert False

def subst_prefix_atoms_ast(ast,subst,pref,to_pref):
    po = variables_distinct_ast(pref,ast) if pref else pref
    return ast_rewrite(ast,AstRewriteSubstPrefix(subst,po,to_pref))

def postfix_atoms_ast(ast,post):
    po = variables_distinct_ast(post,ast)
    return ast_rewrite(ast,AstRewritePostfix(po))

def add_parameters_ast(ast,params):
    return ast_rewrite(ast,AstRewriteAddParams(params))

def copy_attributes_ast(x,y):
    if hasattr(x,'lineno'):
        y.lineno = x.lineno
    if hasattr(x,'sort'):
        y.sort = x.sort
    
def substitute_ast(ast,subs):
    """
    Substitute terms for variables in an ast. Here, subs is
    a dict from string names of variables to terms.
    """
    if isinstance(ast, Variable):
        return subs.get(ast.rep,ast)
    else:
        res = ast.clone([substitute_ast(x,subs) for x in ast.args])
        copy_attributes_ast(ast,res)
        return res

def variables_distinct_ast(ast1,ast2):
    """ rename variables in ast1 so they don't occur in ast2. 
    """
    map1 = distinct_variable_renaming(used_variables_ast(ast1),used_variables_ast(ast2))
    return substitute_ast(ast1,map1)

def distinct_variable_renaming(vars1,vars2):
    rn = UniqueRenamer('',(v.rep for v in vars2))
    return dict((v.rep,rename_variable(v,rn(v.rep))) for v in vars1)

def rename_variable(v,name):
    return type(v)(name,v.sort)


def variables_ast(ast):
    if isinstance(ast,Variable):
        yield ast
    elif ast != None and not isinstance(ast,str):
        for arg in ast.args:
            for x in variables_ast(arg):
                yield x

used_variables_ast = gen_to_set(variables_ast)

def compose_atoms(pr,atom):
    if atom == None:
        return pr
    hname = compose_names(pr.rep,atom.rep)
    args = pr.args + atom.args
    res = type(atom)(hname,args)
    copy_attributes_ast(atom,res)
    return res

def is_true(ast):
    return isinstance(ast,And) and len(ast.args) == 0

def is_false(ast):
    return isinstance(ast,Or) and len(ast.args) == 0

class Range(AST):
    def __init__(self,lo,hi):
        self.args = []
        self.lo, self.hi = lo,hi
    def __str__(self):
        return '{' + str(self.lo) + '..' + str(self.hi) + '}'
    @property
    def rep(self):
        return self
    @property
    def card(self):
        return int(self.hi) - int(self.lo) + 1

class ASTContext(object):
    """ ast compiling context, handles line numbers """
    def __init__(self,ast):
        self.ast = ast
    def __enter__(self):
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        if isinstance(exc_val,ivy_logic.Error):
#            assert False
            raise IvyError(self.ast,str(exc_val))
        if exc_type == IvyError and exc_val.lineno == None and hasattr(self.ast,'lineno'):
            if isinstance(self.ast.lineno,tuple):
                exc_val.filename, exc_val.lineno = self.ast.lineno
            else:
                exc_val.lineno = self.ast.lineno
        return False # don't block any exceptions

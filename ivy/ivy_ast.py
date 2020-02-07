#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Ivy abstract syntax trees.
"""

from ivy_utils import flatten, gen_to_set, UniqueRenamer, compose_names, split_name, IvyError, base_name
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

class NoneAST(AST):
    pass

def copy_attrs(ast1,ast2):
    if hasattr(ast1,'lineno'):
        ast2.lineno = ast1.lineno
    
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

class Globally(Formula):
    """
    Temporal globally of a formula.
    """
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    def __repr__(self):
        return '(globally ' + repr(self.args[0]) + ')'

class Eventually(Formula):
    """
    Temporal eventually of a formula.
    """
    def __init__(self,*args):
        assert len(args) == 1
        self.args = args
    def __repr__(self):
        return '(eventually ' + repr(self.args[0]) + ')'

def has_temporal(f):
    assert f is not None
    return (type(f) in [Globally, Eventually]) or any(has_temporal(x) for x in f.args)

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
    def lhs(self):
        return self.args[0]
    def rhs(self):
        return self.args[1]
    def to_constraint(self):
        if isinstance(self.args[0],App):
            return Atom(equals,self.args)
        return Iff(*self.args)

class DefinitionSchema(Definition):
    pass

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
    def clone(self,args):
        res = type(self)(self.bounds,*args)
        if hasattr(self,'lineno'):
            res.lineno = self.lineno
        return res

class Forall(Quantifier):
    pass

class Exists(Quantifier):
    pass

class Isa(Formula):
    pass

class NamedBinder(Formula):
    def __init__(self, name, bounds, body):
        self.name = name
        self.bounds = bounds
        self.args = [body]
    def clone(self,args):
        res = type(self)(self.name,self.bounds,*args)
        if hasattr(self,'lineno'):
            res.lineno = self.lineno
        return res

class This(AST):
    @property
    def rep(self):
        return 'this'
    @property
    def relname(self):
        return 'this'
    pass

class Atom(Formula):
    """
    A n-ary relation symbol applied to n terms
    """
    def __init__(self, relsym, *terms):
        assert not(isinstance(relsym,Atom)), relsym
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
    def suffix(self,s):
        res = self.clone(self.args)
        res.rep = res.rep + s
        if hasattr(self,'lineno'):
            res.lineno = self.lineno
        return res
    def rename(self,s):
        res = self.clone(self.args)
        res.rep = s
        if hasattr(self,'lineno'):
            res.lineno = self.lineno
        return res
        
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
        return self.rep.rep[0].isdigit() or self.rep.rep[0] == '"'
    def prefix(self,s):
        res = type(self)(s + self.rep)
        if hasattr(self,'sort'):
            res.sort = self.sort
        return res
    def drop_prefix(self,s):
        assert self.rep.startswith(s)
        res = type(self)(self.rep[len(s):],*self.args)
        if hasattr(self,'sort'):
            res.sort = self.sort
        return res
    def rename(self,s):
        res = self.clone(self.args)
        res.rep = s
        if hasattr(self,'lineno'):
            res.lineno = self.lineno
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
    def resort(self,sort):
        res = Variable(self.rep,sort)
        if hasattr(self,'lineno'):
            res.lineno = self.lineno
        return res


class MethodCall(Term):
    def __str__(self):
        return str(self.args[0]) + '.' + str(self.args[1])

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

class Some(AST):
    def __repr__(self):
        return 'some ' +  ','.join(str(a) for a in self.params()) + '. ' + str(self.fmla()) + self.extra()
    def params(self):
        return list(self.args[0:-1])
    def fmla(self):
        return self.args[-1]
    def extra(self):
        return ''
    
class SomeMinMax(Some):
    def params(self):
        return list(self.args[0:-2])
    def fmla(self):
        return self.args[-2]
    def index(self):
        return self.args[-1]

class SomeMin(SomeMinMax):
    def extra(self):
        return ' minimizing ' + str(self.index())

class SomeMax(SomeMinMax):
    def extra(self):
        return ' maximizing ' + str(self.index())
    
class SomeExpr(AST):
    def __init__(self,*args):
        assert len(args) >= 2
        self.args = args
    def __str__(self):
        res = 'some ' + str(self.args[0]) + '. ' + str(self.args[1])
        if len(self.args) >= 3:
            res += ' in ' + str(self.args[2])
        if len(self.args) >= 4:
            res += ' else ' + str(self.args[3])
        return res
    def params(self):
        return [self.args[0]]
    def fmla(self):
        return self.args[1]
    def if_value(self):
        return self.args[2] if len(self.args) == 4 else None
    def else_value(self):
        return self.args[3] if len(self.args) == 4 else None

class Sort(AST):
    pass

class EnumeratedSort(Sort):
    @property
    def extension(self):
        return [a.rep for a in self.args]
    @property
    def rng(self):
        return self
    def dom(self):
        return []
    def __str__(self):
        return '{' + ','.join(self.extension) + '}'
    def defines(self):
        return self.extension
    @property
    def rep(self):
        return self
        


class ConstantSort(Sort):
    def __str__(self):
        return 'uninterpreted'
    def defines(self):
        return []
    @property
    def rng(self):
        return self
    def dom(self):
        return []
        
class StructSort(Sort):
    def __str__(self):
        return 'struct {' + ','.join(map(str,self.args)) + '}'
    def defines(self):
        return [a.rep for a in self.args]

UninterpretedSort = ConstantSort

class FunctionSort(Sort):
    def __init__(self,dom,rng):
        self.dom,self.rng = dom,rng
    def __repr__(self):
        return ' * '.join(repr(s) for s in self.dom) + ' -> ' + repr(self.rng)
    def defines(self):
        return []

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
        self.attributes = ()
    def __repr__(self):
        res = self.name() + ' ' + ','.join([repr(a) for a in self.args])
        return res
    def defines(self):
        return []
    def static(self):
        return []
    def get_type_names(self,names):
        return


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

class ObjectDecl(Decl):
    def name(self):
        return 'object'
    def defines(self):
        return [(c.relname,lineno(c),ObjectDecl) for c in self.args]
#        return []

lf_counter = 0

class LabeledFormula(AST):
    def __init__(self,*args):
        global lf_counter
        self.args = args
        self.id = lf_counter
        self.temporal = None
        self.explicit = False
        lf_counter += 1
    @property
    def label(self):
        return self.args[0]
    @property
    def name(self):
        return self.args[0].relname
    @property
    def formula(self):
        return self.args[1]
    def __str__(self):
        return '[' + str(self.label) + '] ' + str(self.formula) if self.label else str(self.formula)
    def clone(self,args):
        global lf_counter
        res = AST.clone(self,args)
        lf_counter -= 1
        res.id = self.id
        res.temporal = self.temporal
        res.explicit = self.explicit
        return res

    def clone_with_fresh_id(self,args):
        global lf_counter
        res = AST.clone(self,args)
        res.temporal = self.temporal
        res.explicit = self.explicit
        return res

class LabeledDecl(Decl):
    def defines(self):
        if iu.get_numeric_version() <= [1,6]:
            return []
        return [(c.label.relname,lineno(c),type(self)) for c in self.args]
    

class AxiomDecl(LabeledDecl):
    def name(self):
        return 'axiom'

class PropertyDecl(AxiomDecl):
    def name(self):
        return 'property'

class ConjectureDecl(LabeledDecl):
    def name(self):
        return 'conjecture'

class ProofDecl(Decl):
    def name(self):
        return 'proof'

class NamedDecl(Decl):
    def name(self):
        return 'named'
    def defines(self):
        return [(c.rep,lineno(c)) for c in self.args]

class SchemaDecl(Decl):
    def name(self):
        return 'schema'
    def defines(self):
        return [(c.defines(),lineno(c)) for c in self.args]

    
class SchemaBody(AST):
    def __str__(self):
        lines = []
        def indent(ind,s):
            lines.append(ind * '    ' + s)
        def sub(thing,ind):
            indent(0,'{\n')
            for x in thing.prems():
                if isinstance(x,LabeledFormula):
                    fmla = x.formula
                    if isinstance(fmla,SchemaBody):
                        indent(ind+1,'property ' + ('[{}] '.format(x.label) if x.label is not None else ''))
                        sub(fmla,ind+1)
                    else:
                        indent(ind+1,'property ' + str(x) + '\n')
                elif isinstance(x,ivy_logic.UninterpretedSort):
                    indent(ind+1,'type ' + str(x) + '\n')
                else:
                    foob = ivy_logic.sym_decl_to_str(x.args[0]) if isinstance(x.args[0],ivy_logic.Symbol) else str(x.args[0])
                    indent(ind+1,foob + '\n')
            indent(ind+1,'property ' + str(thing.conc()) + '\n')
            indent(ind,'}\n')
        sub(self,0)
        return ''.join(lines)
        return indent * ' ' + '{\n' + '\n'.join(str(arg) for arg in self.args) + '}\n'
    def prems(self):
        return self.args[:-1]
    def conc(self):
        return self.args[-1]

class TheoremDecl(Decl):
    def name(self):
        return 'theorem'
    def defines(self):
        return [(c.defines(),lineno(c)) for c in self.args]

class Renaming(AST):
    def __str__(self):
        return '<' + ','.join('{}/{}'.format(x.rhs(),x.lhs()) for x in self.args) + '>'

class TacticWithMatch(AST):
    """ First arg is a schema name, second is a renaming, rest are matches """
    def __init__(self,*args):
        self.args = args
    def schemaname(self):
        return self.args[0].rep
    def renaming(self):
        return self.args[1]
    def match(self):
        return self.args[2:]
    def __str__(self):
        res = self.tactic_name() + ' ' + str(self.args[0]) 
        if len(self.args) > 1:
            res += ' ' + str(self.args[1])
        if len(self.args) > 2:
            res += ' with ' + ','.join(str(x) for x in self.args[2:])
        return res

class SchemaInstantiation(TacticWithMatch):
    def tactic_name(self):
        return 'apply'

class AssumeTactic(TacticWithMatch):
    def tactic_name(self):
        return 'assume'

class ShowGoalsTactic(AST):
    def tactic_name(self):
        return 'showgoals'
    def __str__(self):
        return 'showgoals'

class DeferGoalTactic(AST):
    def tactic_name(self):
        return 'defergoal'

class NullTactic(AST):
    def __init__(self,*args):
        self.args = []
    def __str__(self):
        return '{}'
    
class LetTactic(AST):
    def __init__(self,*args):
        self.args = args
    def __str__(self):
        return 'let ' + ','.join(str(x) for x in self.args)
    
class SpoilTactic(AST):
    def __init__(self,*args):
        self.args = args
    def __str__(self):
        return 'spoil ' + str(self.args[0])

class IfTactic(AST):
    def __init__(self,*args):
        self.args = args
    def __str__(self):
        return 'if ' + str(self.args[0]) + ' { ' + str(self.args[1]) + ' } else { ' + str(self.args[2]) + ' }'

class PropertyTactic(AST):
    def __init__(self,*args):
        self.args = args
    def __str__(self):
        p = self.args[0]
        n = self.args[1]
        pr = self.args[2]
        return (('temporal ' if p.temporal else '')
                + 'property ' + str(p)
                + ('' if isinstance(n,NoneAST) else ('named ' + str(n)))
                + ('' if isinstance(pr,NoneAST) else ('proof ' + str(pr))))
class TacticTactic(AST):
    @property
    def tactic_name(self):
        return self.args[0].rep
    @property
    def tactic_decls(self):
        return self.args[1].args
    def __str__(self):
        res = 'tactic ' + str(self.args[0]) + str(self.args[1])

class TacticWith(AST):
    def __str__(self):
        res = (' with ' + ' '.join(str(x) for x in self.args[1].args)) if self.args[1].args > 0 else ''

class ComposeTactics(AST):
    def __str__(self):
        return '; '.join(map(str,self.args))


class Instantiation(AST):
    def __init__(self,*args):
        self.args = args
    def __repr__(self):
        return ' : '.join(repr(x) for x in self.args) if self.args[0] else repr(self.args[1])

class InstantiateDecl(Decl):
    def name(self):
        return 'instantiate'

class AutoInstanceDecl(Decl):
    def name(self):
        return 'autoinstance'


class RelationDecl(Decl):
    def name(self):
        return 'relation'
    def defines(self):
        return [(c.relname,lineno(c)) for c in self.args if c.relname not in iu.polymorphic_symbols]

def tterm_type_names(c,names):
    if hasattr(c,'sort'):
        names.add(c.sort)
    for arg in c.args:
        if hasattr(arg,'sort'):
            names.add(arg.sort)


class ConstantDecl(Decl):
    def name(self):
        return 'individual'
    def defines(self):
        return [(c.rep,lineno(c)) for c in self.args if c.rep not in iu.polymorphic_symbols]
    def get_type_names(self,names):
        for c in self.args:
            tterm_type_names(c,names)
                

class ParameterDecl(ConstantDecl):
    def name(self):
        return 'parameter'
    def mysym(self):
        return self.args[0].args[0] if isinstance(self.args[0],Definition) else self.args[0]
    def defines(self):
        c = self.mysym()
        return [(c.rep,lineno(c))]
    def get_type_names(self,names):
        tterm_type_names(self.mysym(),names)

class FreshConstantDecl(ConstantDecl):
    pass

class DestructorDecl(ConstantDecl):
    def name(self):
        return 'destructor'

class ConstructorDecl(ConstantDecl):
    def name(self):
        return 'constructor'

class DerivedDecl(Decl):
    def name(self):
        return 'derived'
    def defines(self):
        return [(c.formula.defines(),lineno(c.formula)) for c in self.args]

class DefinitionDecl(LabeledDecl):
    def name(self):
        return 'definition'

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
        res =  [(c.defines(),lineno(c)) for c in self.args]
        for a in self.args:
            res.extend(a.iter_internal_defines())
        return res

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
        return [(n,l,TypeDecl) for n,l in self.args[0].defines()]
    def static(self):
        res = [a for a,b in self.args[0].defines()]
        return res
    def get_type_names(self,names):
        for c in self.args:
            t = c.args[1]
            if isinstance(t,StructSort):
                for s in t.args:
                    tterm_type_names(s,names)

class VariantDecl(Decl):
    def name(self):
        return 'variant'
    def defines(self):
        return []

class AssertDecl(Decl):
    def name(self):
        return 'assert'
    def defines(self):
        return []

class InterpretDecl(LabeledDecl):
    def name(self):
        return 'interpret'

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
    def __str__(self):
        return self.mixer() + " before " + self.mixee()
    pass
    
class MixinImplementDef(MixinBeforeDef):
    def __str__(self):
        return self.mixer() + " implement " + self.mixee()
    pass

class MixinAfterDef(MixinDef):
    def __str__(self):
        return self.mixer() + " after " + self.mixee()
    pass

class IsolateDecl(Decl):    
    def name(self):
        return 'isolate'
    def defines(self):
        return [(c.name(),lineno(c)) for c in self.args]
    
class IsolateObjectDecl(IsolateDecl):    
    def defines(self):
        return []

class IsolateDef(AST):
    def name(self):
        return self.args[0].relname
    def verified(self):
        return self.args[1:len(self.args)-self.with_args]
    def present(self):
        return self.args[len(self.args)-self.with_args:]
    def params(self):
        return self.args[0].args
        
    def __repr__(self):
        return (','.join(repr(a) for a in self.verified()) +
                  (('with ' + ','.join(repr(a) for a in self.present())) if self.present() else ''))
    def add_with(extra_with):
        res = self.clone(list(self.args))
        res.with_args += len(extra_with)
        res.args.extend(extra_with)
        return res
    def clone(self,args):
        res = AST.clone(self,args)
        res.with_args = self.with_args
        return res
        
class TrustedIsolateDef(IsolateDef):
    pass

class ExtractDef(IsolateDef):
    pass

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

class ImportDecl(Decl):    
    def name(self):
        return 'import_'
    def defines(self):
        return []
    
class ImportDef(AST):
    def imported(self):
        return self.args[0].relname
    def scope(self):
        return self.args[1].relname
    def __repr__(self):
        return self.imported() + (' from {}'.format(self.scope()) if self.scope() else '')

class PrivateDecl(Decl):    
    def name(self):
        return 'private'
    def defines(self):
        return []
    
class PrivateDef(AST):
    def privatized(self):
        return self.args[0].relname
    def __repr__(self):
        return 'private {}'.format(self.args[0])

class AliasDecl(Decl):
    def name(self):
        return 'alias'
    def defines(self):
        return [(c.defines(),lineno(c)) for c in self.args]
    

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


class ImplementTypeDecl(Decl):    
    def name(self):
        return 'implementtype'
    def defines(self):
        return []
    
class ImplementTypeDef(AST):
    def implemented(self):
        return self.args[0].relname
    def implementer(self):
        return self.args[1].relname
    def __repr__(self):
        s = self.implemented()
        s += ' with ' + self.implementer
        return s

class NativeCode(AST):
    def __init__(self,string):
        self.args = []
        self.code = string
    def __str__(self):
        return self.code
    def inst(self,fun,args):
        fields = self.code.split('`')
        fields = [(fun(args[int(s)]) if idx % 2 == 1 else s) for idx,s in enumerate(fields)]
        return ''.join(fields)
    def clone(self,args):
        return NativeCode(self.code)
    

class NativeType(AST):
    """ Quote native type """
    def __str__(self):
        return native_to_string(self.args)

class NativeExpr(AST):
    """ Quote native expr """
    def __str__(self):
        return native_to_string(self.args)
    def clone(self,args):
        clone_res = AST.clone(self,args)
        if hasattr(self,'sort'):
            clone_res.sort = self.sort
        return clone_res

def native_to_string(args):
    res = '<<<'
    fields = args[0].code.split('`')
    fields = [(str(args[int(s)+1]) if idx % 2 == 1 else s) for idx,s in enumerate(fields)]
    res += '`'.join(fields)
    res += '>>>'
    return res
    

class NativeDef(AST):
    def name(self):
        return 'native'
    def __str__(self):
        res = ('[' + str(self.args[0]) + '] ') if self.args[0] else ''
        res += native_to_string(self.args[1:])
        return res

class NativeDecl(Decl):
    def name(self):
        return 'native'
    def defines(self):
        return []
        
class AttributeDef(AST):
    def name(self):
        return 'attribute'
    def __str__(self):
        return 'attribute ' + str(self.args[0]) + ' = ' + str(self.args[1])
    def __repr__(self):
        return 'attribute ' + str(self.args[0]) + ' = ' + str(self.args[1])

class AttributeDecl(Decl):
    def name(self):
        return 'attribute'
    def defines(self):
        return []

class TypeDef(Definition):
    def __init__(self,name,sort):
        self.args = [name,sort]
        self.finite = False
    def clone(self,args):
        res = Definition.clone(self,args)
        res.finite = self.finite
        return res
    def __repr__(self):
        return ('finite ' if self.finite else '') + str(self.args[0]) + ' = ' + repr(self.args[1])
    def defines(self):
        syms =  [self.args[0].rep] + self.args[1].defines()
        return [(sym,lineno(self)) for sym in syms]
        
    @property
    def name(self):
        return self.args[0].rep
    @property
    def value(self):
        return self.args[1]

class GhostTypeDef(TypeDef):
    pass

class VariantDef(AST):
    def __init__(self,name,sort):
        self.args = [name,sort]
    def __repr__(self):
        return str(self.args[0]) + ' of ' + str(self.args[1])
    

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
        return str(self.args[0]) + '(' + ','.join(str(p) for p in self.formal_params) + ') = ' + str(self.args[1])
    def defines(self):
        return self.args[0].relname
    def iter_internal_defines(self):
        return self.args[1].iter_internal_defines()
    def clone(self,args):
        if not hasattr(self.args[1],'lineno'):
            print 'no lineno!!!!!: {}'.format(self)
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
        if hasattr(self,'labels'):
            res.labels = labels
        return res
    def formals(self):
        return ([s.drop_prefix('fml:') for s in self.formal_params],
                [s.drop_prefix('fml:') for s in self.formal_returns])

def rewrite_param(p,rewrite):
    res = type(p)(p.rep)
    res.sort = rewrite_sort(rewrite,p.sort)
    return res

class StateDef(Definition):
    def __init__(self,name,state):
        self.args = [Atom(name,[]),state]
    def __repr__(self):
        return self.args[0].relname + ' = ' + repr(self.args[1])

class ScenarioDecl(Decl):
    def name(self):
        return 'scenario'
    def defines(self):
        res = []
        for a in self.args:
            res.extend(a.defines())
        return res

class PlaceList(AST):
    def __repr__(self):
        return ','.join(repr(a) for a in self.args)
    
class ScenarioMixin(AST):
    def __repr__(self):
        return self.kind() + ' ' +repr(self.args[1])

class ScenarioBeforeMixin(ScenarioMixin):
    def kind(self):
        return 'before'

class ScenarioAfterMixin(ScenarioMixin):
    def kind(self):
        return 'before'

class ScenarioTransition(AST):
    def __repr__(self):
        return repr(self.args[0]) + '->' + repr(self.args[1]) + ' : ' + repr(self.args[2])

class ScenarioDef(AST):
    def __repr__(self):
        return 'scenario {->' + repr(self.args[0]) + ';' + ''.join(repr(a) for a in self.args[1:]) + '}'
    def places(self):
        done = set()
        places = list(self.args[0].args)
        for tr in self.args[1:]:
            places.extend(tr.args[0].args)
            places.extend(tr.args[1].args)
        res = []
        for pl in places:
            if pl.rep not in done:
                res.append((pl.rep,lineno(pl)))
                done.add(pl.rep)
        return res
    def defines(self):
        res = []
        done = set()
        for tr in self.args[1:]:
            mixer = tr.args[2].args[0].rep
            if mixer not in done:
                done.add(mixer)
                res.append((mixer,tr.args[2].args[0].lineno))
        res.extend(self.places())
        return res
    
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
    if not isinstance(app,App):
        return app
    if isinstance(app,Old) or isinstance(app,Quantifier) or isinstance(app,Ite) or isinstance(app,Variable):
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
    it = subst.get(names[0],names[0])
    if isinstance(it,This):
        if len(names) > 1:
            return compose_names(*names[1:])
        return it
    return compose_names(it,*names[1:])
#    return subst.get(s,s)

def subst_subscripts_comp(s,subst):
    if isinstance(s,This) or s.startswith('"') :
        return s
    assert s!=None
#    print 's: {} subst: {}'.format(s,subst)
    try:
        g = name_parser.findall(s)
    except:
        assert False, s
#    print 'g: {}'.format(g)
    if not g:
        return s
    pref = str_subst(g[0],subst)
    if isinstance(pref,This):
        if len(g) > 1:
            raise iu.IvyError(None,'cannot substitute "this" for {} in {}'.format(g[0],s))
        return pref
    try:
        res =  pref + ''.join(('[' + str_subst(x[1:-1],subst) + ']' if x.startswith('[') else x) for x in g[1:])
    except:
        print "s: {} subst : {}".format(s,subst)
#    print "res: {}".format(res)
    return res

def subst_subscripts(s,subst):
#    return compose_names(*[subst_subscripts_comp(t,subst) for t in split_name(s)])
    return subst_subscripts_comp(s,subst)

def my_base_name(x):
    return x if isinstance(x,This) else base_name(x)

def base_name_differs(x,y):
    return my_base_name(x) != my_base_name(y)

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
    def __init__(self,subst,pref,to_pref = None,static=None):
        self.subst,self.pref,self.to_pref,self.static = subst,pref,to_pref,static
    def rewrite_name(self,name):
        return subst_subscripts(name,self.subst)
    def prefix_str(self,name,always):
        if not (self.pref and (always or self.to_pref == None or split_name(name)[0] in self.to_pref)):
            return name
        return iu.compose_names(self.pref.rep,name)
    def rewrite_atom(self,atom,always=False):
        if not(isinstance(atom.rep,This) or atom.rep.startswith('"')):
            g = name_parser.findall(atom.rep)
            if len(g) > 1:
                n = g[0] + ''.join(('[' + self.prefix_str(x[1:-1],always) + ']' if x.startswith('[') else x) for x in g[1:])
                atom = atom.rename(n)
        if not (self.pref and (always or self.to_pref == None or isinstance(atom.rep,This) or 
                split_name(atom.rep)[0] in self.to_pref)):
            return atom
        the_pref = self.pref
        if self.static != None and atom.rep in self.static:
            the_pref = Atom(the_pref.rep)
        return compose_atoms(the_pref,atom)

class AstRewritePostfix(object):
    def __init__(self,post):
        self.post = post
    def rewrite_name(self,name):
        return name
    def rewrite_atom(self,atom,always=False):
        return compose_atoms(atom,self.post)

class AstRewriteAddParams(object):
    def __init__(self,params):
        self.params = params
    def rewrite_name(self,name):
        return name
    def rewrite_atom(self,atom,always=False):
        return atom.clone(atom.args + self.params)

def rewrite_sort(rewrite,orig_sort):
    sort = rewrite.rewrite_name(orig_sort)
    if base_name_differs(sort,orig_sort):
        return sort
    sort = rewrite.rewrite_atom(Atom(sort)).rep
    return sort

def ast_rewrite(x,rewrite):
    if isinstance(x,str):
        return rewrite.rewrite_name(x)
    if isinstance(x,list):
        return [ast_rewrite(e,rewrite) for e in x]
    if isinstance(x,tuple):
        return tuple(ast_rewrite(e,rewrite) for e in x)
    if isinstance(x,Variable):
        return x.resort(rewrite_sort(rewrite,x.sort))
    if isinstance(x,Atom) or isinstance(x,App):
#        print "rewrite: x = {!r}, type(x.rep) = {!r}".format(x,type(x.rep))
        if isinstance(x.rep, NamedBinder):
            atom = type(x)(ast_rewrite(x.rep,rewrite),ast_rewrite(x.args,rewrite))
        else:
            atom = type(x)(rewrite.rewrite_name(x.rep),ast_rewrite(x.args,rewrite))
        copy_attributes_ast(x,atom)
        if hasattr(x,'sort'):
            atom.sort = rewrite_sort(rewrite,x.sort)
        if isinstance(x.rep, NamedBinder) or base_name_differs(x.rep,atom.rep):
            return atom
        return rewrite.rewrite_atom(atom)
    if isinstance(x,Literal):
        return Literal(x.polarity,ast_rewrite(x.atom,rewrite))
    if isinstance(x, Quantifier):
        return type(x)(ast_rewrite(x.bounds,rewrite),ast_rewrite(x.args[0],rewrite))
    if isinstance(x, NamedBinder):
        return type(x)(x.name,ast_rewrite(x.bounds,rewrite),ast_rewrite(x.args[0],rewrite))
    if hasattr(x,'rewrite'):
        return x.rewrite(rewrite)
    if isinstance(x,LabeledFormula) or isinstance(x,NativeDef):
        arg0 = x.args[0]
        if x.args[0] == None:
            if isinstance(rewrite,AstRewriteSubstPrefix) and rewrite.pref != None:
                arg0 = rewrite.pref
        else:
            atom = arg0.clone(ast_rewrite(arg0.args,rewrite))
            arg0 = rewrite.rewrite_atom(atom,always=True)
        res = x.clone([arg0] + [ast_rewrite(y,rewrite) for y in x.args[1:]])
        return res
    if isinstance(x,TypeDef):
        res = x.clone(ast_rewrite(x.args,rewrite)) # yikes!
        if res.args[0].args:
            raise iu.IvyError(x,'Types cannot have parameters: {}'.format(x.name))
        return res
    if hasattr(x,'args'):
        return x.clone(ast_rewrite(x.args,rewrite)) # yikes!
    print "wtf: {} {}".format(x,type(x))
    assert False

def subst_prefix_atoms_ast(ast,subst,pref,to_pref,static=None):
    po = variables_distinct_ast(pref,ast) if pref else pref
    return ast_rewrite(ast,AstRewriteSubstPrefix(subst,po,to_pref,static=static))

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

def substitute_constants_ast(ast,subs):
    """
    Substitute terms for variables in an ast. Here, subs is
    a dict from string names of variables to terms.
    """
    if (isinstance(ast, Atom) or isinstance(ast,App)) and not ast.args:
        return subs.get(ast.rep,ast)
    else:
        if isinstance(ast,str):
            return ast
        new_args = [substitute_constants_ast(x,subs) for x in ast.args]
        res = ast.clone(new_args)
        copy_attributes_ast(ast,res)
        return res

def substitute_constants_ast2(ast,subs):
    """
    Substitute terms for variables in an ast. Here, subs is
    a dict from string names of variables to terms.
    """
    if (isinstance(ast, Atom) or isinstance(ast,App)) and not ast.args:
        if ast.rep in subs:
            return subs[ast.rep]
        names = split_name(ast.rep)
        if names[0] in subs:
            thing = type(ast)(compose_names(*names[1:]),ast.args)
            thing.lineno = ast.lineno
            res = MethodCall(subs[names[0]],thing)
            res.lineno = ast.lineno
            return res
        return ast
    else:
        if isinstance(ast,str):
            return ast
        new_args = [substitute_constants_ast2(x,subs) for x in ast.args]
        res = ast.clone(new_args)
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
#        if not hasattr(ast,'args'):
#            print ast
#            print type(ast)
#        if any(isinstance(c,list) for c in ast.args):
#            print "foo: " + repr(ast)
        for arg in ast.args:
            for x in variables_ast(arg):
                yield x

used_variables_ast = gen_to_set(variables_ast)

def compose_atoms(pr,atom):
    if atom == None:
        return pr
    hname = pr.rep if isinstance(atom.rep,This) else compose_names(pr.rep,atom.rep)
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
    def clone(self,args):
        return Range(self.lo,self.hi)
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
        if isinstance(exc_val,IvyError):
#        if exc_type == IvyError:
#            print "no lineno: {}".format(self.ast)
            needs_lineno = hasattr(exc_val,'lineno') and not exc_val.lineno.line
            if needs_lineno and hasattr(self.ast,'lineno'):
#                print "lineno: {}".format(self.ast.lineno)
                exc_val.lineno = self.ast.lineno
        return False # don't block any exceptions

class Labeler(object):
    def __init__(self):
        self.rn = iu.UniqueRenamer()
    def __call__(self):
        return Atom(self.rn(),[])

class KeyArg(App):
    def __repr__(self):
        return '^' + App.__repr__(self)

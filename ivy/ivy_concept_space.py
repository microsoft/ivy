#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import itertools
from ivy_logic import *
from ivy_logic_utils import substitute_clause, canonize_clause, used_variables_clauses

class NamedSpace(AST):
    def __init__(self, lit):
        self.lit = lit
        self.args = [lit]
    def __repr__(self):
        return repr(self.lit)
    def enumerate(self, memo,test):
        atom = self.lit.atom
        if self.lit.polarity == 1 and is_atom(atom) and atom.relname in memo:
            params,value = memo[atom.relname]
            assert len(params) == len(atom.args)
            subst = dict(zip(params,atom.args))
            res = [substitute_clause(cl,subst) for cl in value]
#            print "blif: {} {} {} {}".format(atom,params,value,res)
            return res
        return [[self.lit]] if test([self.lit]) else []
    def eval(self, memo, relalg):
        atom = self.lit.atom
        if self.lit.polarity == 1 and atom.relname in memo:
            params,value = memo[atom.relname]
            if len(params) != len(atom.args):
                print "{} {} {}".format(self,params,value)
            assert len(params) == len(atom.args)
            subst = dict(zip(params,atom.args))
            return [(substitute_clause(cl,subst),relalg.subst(r,subst)) for (cl,r) in value]
        v = relalg.prim(self.lit)
        return [([self.lit],v)] if not relalg.empty(v) else []

class SumSpace(AST):
    def __init__(self, spaces):
        self.spaces = spaces
        self.args = spaces
    def clone(self,args):
        return SumSpace(args)
    def __repr__(self):
        return '(' + ' + '.join([repr(s) for s in self.spaces]) + ')'
    def enumerate(self,memo,test):
#        print "enumerate: {}".format(self)
        return [cl for s in self.spaces for cl in s.enumerate(memo,test)]
    def eval(self,memo,relalg):
        return [cl for s in self.spaces for cl in s.eval(memo,relalg)]

class ProductSpace(AST):
    def __init__(self, spaces):
        self.spaces = spaces
        self.args = spaces
    def __repr__(self):
        return '(' + ' * '.join([repr(s) for s in self.spaces]) + ')'
    def clone(self,args):
        return ProductSpace(args)
    def enumerate(self,memo,test):
        if not self.spaces:
            return [[]]
        fs = self.spaces[0].enumerate(memo,test)
#        print "prod: {}".format(fs)
        for s in self.spaces[1:]:
            fs2 = s.enumerate(memo,test)
#            print "prod: {}".format(fs2)
            prod = [x + y for x,y in itertools.product(fs,fs2)]
            fs = [cl for cl in prod if test(cl)]
        return fs
    def eval(self,memo,relalg):
        if not self.spaces:
            return [([],relalg.top())]
        fs = self.spaces[0].eval(memo,relalg)
        for s in self.spaces[1:]:
            fs2 = s.eval(memo,relalg)
            prod = [(x + y,relalg.prod(xv,yv)) for (x,xv),(y,yv) in itertools.product(fs,fs2)]
            fs = [(cl,v) for cl,v in prod if not relalg.empty(v)]
            if relalg.parent:
                for cube,v in fs:
                    relalg.parent.inhabited_cube(cube,witness=v)
        return fs


import ply.lex as lex

tokens = (
   'SYMBOL',
   'COMMA',
   'LPAREN',
   'RPAREN',
   'LBR',
   'RBR',
   'PLUS',
   'TIMES',
   'TILDA'
)

t_TILDA    = r'\~'
t_COMMA    = r'\,'
t_PLUS    = r'\+'
t_TIMES   = r'\*'
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_LBR  = r'\['
t_RBR  = r'\]'

t_ignore  = ' \t\n'

def t_SYMBOL(t):
    r'[a-zA-Z_=][_a-zA-Z0-9]*'
    return t

def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

lexer = lex.lex()

# Yacc example

import ply.yacc as yacc

def p_expr_lit(p):
    'expr : lit'
    p[0] = NamedSpace(p[1])

def p_expr_prod(p):
    'expr : LPAREN prod RPAREN'
    p[0] = ProductSpace(p[2])
    
def p_expr_sum(p):
    'expr : LPAREN sum RPAREN'
    p[0] = SumSpace(p[2])

def p_term_symbol(p):
    'term : SYMBOL'
    p[0] = Variable(p[1]) if str.isupper(p[1][0]) else Constant(p[1])

def p_terms(p):
    'terms : '
    p[0] = []

def p_terms_term(p):
    'terms : term'
    p[0] = [p[1]]

def p_terms_terms_term(p):
    'terms : terms COMMA term'
    p[0] = p[1]
    p[0].append(p[3]) # is this side effect OK?

def p_atom_terms(p):
    'atom : SYMBOL LPAREN terms RPAREN'
    p[0] = Atom(p[1],p[3])

def p_lit_atom(p):
    'lit : atom'
    p[0] = Literal(1,p[1])

def p_lit_tilda_atom(p):
    'lit : TILDA atom'
    p[0] = Literal(0,p[2])

def p_prod_expr_expr(p):
    'prod : expr TIMES expr'
    p[0] = [p[1],p[3]]

def p_prod_prod_expr(p):
    'prod : prod TIMES expr'
    p[0] = p[1]
    p[0].append(p[3]) # is this side effect OK?

def p_sum_expr_expr(p):
    'sum : expr PLUS expr'
    p[0] = [p[1],p[3]]

def p_sum_sum_expr(p):
    'sum : sum PLUS expr'
    p[0] = p[1]
    p[0].append(p[3]) # is this side effect OK?

    
def p_error(p):
    print "Syntax error in input!"

# Build the parser
import os
tabdir = os.path.dirname(os.path.abspath(__file__))
parser = yacc.yacc(tabmodule='concept_space_parsetab',errorlog=yacc.NullLogger(),outputdir=tabdir)

def to_concept_space(s):
    return parser.parse(s)

if __name__ == '__main__':
    while True:
       try:
           s = raw_input('calc > ')
       except EOFError:
           break
       if not s: continue
       result = parser.parse(s)
       print result
       print "enum: %s" % result.enumerate(dict(),lambda x:True)

def clauses_to_concept(name,clauses):
    vars =  used_variables_clauses(clauses)
#    print "clauses_to_concept vars={}".format(vars)
    ps = [ProductSpace([NamedSpace(~lit) for lit in clause]) for clause in clauses.triv_clauses()]
    ss = ps[0] if len(ps) == 1 else SumSpace(ps)
    return (Atom(Symbol(name,RelationSort([v.sort for v in vars])),[v for v in vars]),ss)


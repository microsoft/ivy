#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import itertools

class Event(object):
    def __init__(self,rep,args,children):
        self.rep,self.args,self.children = rep,args,children
    def __str__(self):
        res = self.rep
        if self.args:
            res += '(' + ','.join(map(str,self.args)) + ')'
        if self.children:
            res += '{' + ';'.join(map(str,self.children)) + '}'
        return res

import ply.lex as lex

tokens = (
   'SYMBOL',
   'COMMA',
   'LPAREN',
   'RPAREN',
   'LBR',
   'RBR',
   'LCB',
   'RCB',
   'SEMI',
   'COLON',
)

t_COMMA    = r'\,'
t_SEMI    = r'\;'
t_COLON    = r'\:'
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_LBR  = r'\['
t_RBR  = r'\]'
t_LCB  = r'\{'
t_RCB  = r'\}'

t_ignore  = ' \t\n'

def t_SYMBOL(t):
    r'[_a-zA-Z0-9]+'
    return t

def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

lexer = lex.lex()

# Yacc example

import ply.yacc as yacc

def p_value_symbol(p):
    'value : SYMBOL'
    p[0] = p[1]

def p_list(p):
    'list : '
    p[0] = []

def p_list_list_comma_value(p):
    'list : list COMMA value'
    p[0] = p[1]
    p[0].append(p[3])

def p_value_lbr_list_rbr(p):
    'value : LBR list RBR'
    p[0] = p[2]

def p_dict(p):
    'dict : '
    p[0] = {}
    
def p_dict_dict_comma_key_colon_value(p):
    'dict : dict COMMA SYMBOL COLON value'
    p[0] = p[1]
    p[0][p[3]] = p[5]


    
def p_error(p):
    print "Syntax error in input!"

# Build the parser
import os
tabdir = os.path.dirname(os.path.abspath(__file__))
parser = yacc.yacc(tabmodule='ev_parsetab',errorlog=yacc.NullLogger(),outputdir=tabdir)

if __name__ == '__main__':
    pass


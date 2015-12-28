#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ply.lex as lex

tokens = (
   'COMMA',
   'LPAREN',
   'RPAREN',
   'PLUS',
   'MINUS',
   'TIMES',
   'TILDA',
   'AND',
   'OR',
   'EQ',
   'TILDAEQ',
   'SEMI',
   'ASSIGN',
   'DOT',
   'LCB',
   'RCB',
   'ARROW',
   'SYMBOL',
   'COLON',
   'EQEQ',
   'LE',
   'LT',
   'GE',
   'GT',
   'BANG',
   'BANGEQ',
   'IMPLIES',
   'IFF'
)

reserved = {
   'var' : 'VAR',
   'ensures' : 'ENSURES',
   'requires' : 'REQUIRES',
   'modifies' : 'MODIFIES',
   'method' : 'METHOD',
   'returns' : 'RETURNS',
   'decreases' : 'DECREASES',
   'assume' : 'ASSUME',
   'assert' : 'ASSERT',
   'while' : 'WHILE',
   'invariant' : 'INVARIANT',
   'if' : 'IF',
   'else' : 'ELSE',
   'return' : 'RETURN',
}

tokens += tuple(reserved.values())


t_TILDA    = r'\~'
t_BANG     = r'\!'
t_COMMA    = r'\,'
t_PLUS    = r'\+'
t_MINUS    = r'\-'
t_TIMES   = r'\*'
t_LT      = r'\<'
t_LE      = r'\<='
t_GT      = r'\>'
t_GE      = r'\>='
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_OR = r'\|\|'
t_AND = r'\&\&'
t_EQ = r'\='
t_TILDAEQ = r'\~='
t_BANGEQ = r'\!='
t_SEMI = r'\;'
t_ASSIGN = r'\:='
t_DOT = r'\.'
t_LCB  = r'\{'
t_RCB  = r'\}'
t_ARROW = r'\->'
t_COLON = r':'
t_EQEQ = r'=='
t_IMPLIES = r'\=\=\>'
t_IFF = r'\<\=\=\>'

t_ignore  = ' \t'
t_ignore_COMMENT = r'\/\/.*'

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_SYMBOL(t):
    r'[_a-zA-Z0-9]+'
    t.type = reserved.get(t.value,'SYMBOL')
    return t

def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

lexer = lex.lex()

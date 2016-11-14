#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import itertools
import ivy_utils as iu

class Events(list):
    def __init__(self,*args):
        list.__init__(self,args)
    def __str__(self):
        return ' '.join(map(str,self))
    
class Event(object):
    def __init__(self,rep,args,children):
        self.rep,self.args,self.children = rep,args,children
    def text(self):
        res = self.rep
        if self.args:
            res += '(' + ','.join(map(str,self.args)) + ')'
        return res
    @property
    def subs(self):
        return ([ArgList(self.args)] if self.args else []) + self.children
    def match(self,ev):
        return ((ev.rep == '*' or ev.rep == self.rep)
                and all(a.match(b) for a,b in zip(self.args,ev.args)))
    def __str__(self):
        res = self.text()
        if self.children:
            res += '{' + str(self.children) + '}'
        return res

class InEvent(Event):
    def __str__(self):
        return '> ' + Event.__str__(self)

class OutEvent(Event):
    def __str__(self):
        return '< ' + Event.__str__(self)

class ArgList(object):
    def __init__(self,args):
        self.args = args
    def text(self):
        return 'args'
    @property
    def subs(self):
        return self.args

class Symbol(object):
    def __init__(self,name):
        self.name = name
    def __str__(self):
        return self.name    
    def text(self):
        return self.name
    @property
    def subs(self):
        return []
    def match(self,s):
        return isinstance(s,Symbol) and (s.name == '*' or s.name == self.name)
    
class ListValue(list):
    def __init__(self,*args):
        list.__init__(self,args)
    def __str__(self):
        return '[' + ','.join(map(str,self)) + ']'
    def text(self):
        return str(self)
    @property
    def subs(self):
        res = list(self)
        print "list: {}".format(res)
        return res
    def match(self,l):
        return (isinstance(l,Symbol) and (l.name == '*')
                or (isinstance(l,ListValue)
                    and len(l) == len(self)
                    and all(a.match(b) for a,b in zip(self,l))))


class DictEntry(object):
    def __init__(self,entry):
        self.key,self.value = entry
    def text(self):
        return self.key + ':' + str(self.value)
    @property
    def subs(self):
        return self.value.subs
        

class DictValue(dict):
    def __init__(self,*args):
        dict.__init__(self,args)
    def text(self):
        return str(self)
    @property
    def subs(self):
        return [DictEntry(entry) for entry in self.iteritems()]
    def __str__(self):
        return '{' + ','.join(x + ':' + str(y) for x,y in self.iteritems()) + '}'
    def match(self,d):
        return (isinstance(d,Symbol) and (d.name == '*')
                or (isinstance(d,DictValue)
                    and all(k in self and self[k].match(v) for k,v in d.iteritems())))

class EventGen(object):
    def __call__(self,evs):
        for ev in evs:
            yield ev
            for ev1 in self(ev.children):
                yield ev1

def filter(evs,pats):
    for e in evs:
        if any(e.match(pat) for pat in pats):
            yield e

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
    'GT',
    'LT',
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
t_GT   = r'\>'
t_LT   = r'\<'

t_ignore  = ' \t'

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_SYMBOL(t):
    r'[_a-zA-Z0-9]+|\*'
    return t

def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

lexer = lex.lex()

# Yacc example

import ply.yacc as yacc

def p_events(p):
    'events : '
    p[0] = Events()

def p_events_events_event(p):
    'events : events event'
    p[0] = p[1]
    p[0].append(p[2])

def p_event_optdir_name_optargs_optsubs(p):
    'event : optdir SYMBOL optargs optsubs'
    p[0] = p[1](p[2],p[3],p[4])

def p_optdir(p):
    'optdir : '
    p[0] = Event

def p_optdir_gt(p):
    'optdir : GT'
    p[0] = InEvent

def p_optdir_lt(p):
    'optdir : LT'
    p[0] = OutEvent

def p_optsubs(p):
    'optsubs : '
    p[0] = Events()

def p_optsubs_semi(p):
    'optsubs : SEMI'
    p[0] = Events()

def p_optsubs_lcb_events_rcb(p):
    'optsubs : LCB events RCB'
    p[0] = p[2]

def p_value_symbol(p):
    'value : SYMBOL'
    p[0] = Symbol(p[1])

def p_list_value(p):
    'list : value'
    p[0] = ListValue(p[1])

def p_list_list_comma_value(p):
    'list : list COMMA value'
    p[0] = p[1]
    p[0].append(p[3])

def p_value_lbr_rbr(p):
    'value : LBR RBR'
    p[0] = ListValue()

def p_value_lbr_list_rbr(p):
    'value : LBR list RBR'
    p[0] = p[2]

def p_dict_symbol_colon_value(p):
    'dict : SYMBOL COLON value'
    p[0] = DictValue((p[1],p[3]))
    
def p_dict_dict_comma_key_colon_value(p):
    'dict : dict COMMA SYMBOL COLON value'
    p[0] = p[1]
    p[0][p[3]] = p[5]

def p_value_lcb_rcb(p):
    'value : LCB RCB'
    p[0] = {}

def p_value_lcb_dict_rcb(p):
    'value : LCB dict RCB'
    p[0] = p[2]

def p_optargs(p):
    'optargs : '
    p[0] = []

def p_optargs_lp_args_rp(p):
    'optargs : LPAREN list RPAREN'
    p[0] = p[2]

    
class ParseError(Exception):
    def __init__(self,lineno,token,message):
#        print "initializing"
        self.lineno, self.token,self.message = lineno,token,message
        if iu.filename:
            self.filename = iu.filename
    def __repr__(self):
        return ( ("{}: ".format(self.filename) if hasattr(self,'filename') else '')
                 + ("line {}: ".format(self.lineno) if self.lineno != None else '')
                 + ("token '{}': ".format(self.token) if self.token != None else '')
                 + self.message )

error_list = []

stack = []

def get_lineno(p,n):
    return iu.Location(iu.filename,p.lineno(n))

def report_error(error):
    error_list.append(error)

def p_error(token):
    if token is not None:
        report_error(ParseError(token.lineno,token.value,"syntax error"))
    else:
        report_error(ParseError(None,None,'unexpected end of input'));

def parse(s):
    global error_list
    error_list = []
    res = parser.parse(s)
    if error_list:
        print error_list
        raise iu.ErrorList(error_list)
    return res
    

# Build the parser
import os
tabdir = os.path.dirname(os.path.abspath(__file__))
#parser = yacc.yacc(tabmodule='ev_parsetab',errorlog=yacc.NullLogger(),outputdir=tabdir)
parser = yacc.yacc(tabmodule='ev_parsetab',outputdir=tabdir)

if __name__ == '__main__':
    while True:
       try:
           s = raw_input('calc > ')
       except EOFError:
           break
       if not s: continue
       result = parser.parse(s)
       print result



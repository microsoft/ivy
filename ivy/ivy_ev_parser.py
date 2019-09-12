#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import itertools
import ivy_utils as iu

def mymap(fun,obj):
    res = obj.map(fun)
    return res

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
    def match(self,ev,binding=None):
        return ((ev.rep == '*' or self.rep.startswith(ev.rep))
                and all(a.match(b,binding) for a,b in zip(self.args,ev.args)))
    def __str__(self):
        res = self.text()
        if self.children:
            res += '{' + str(self.children) + '}'
        return res
    def map(self,fun):
        return type(self)(self.rep,[a.map(fun) for a in self.args],self.children)

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
    def match(self,s,binding=None):
        if isinstance(s,Symbol) and (s.name == '*' or s.name == self.name):
            return True
        if s.name.startswith('$'):
            if s.name in binding:
                return binding[s.name] == self
            binding[s.name] = self
            return True
        return False
    def map(self,fun):
        return fun(self.name)
    
class App(object):
    def __init__(self,rep,args):
        self.rep,self.args = rep,args
    def text(self):
        res = self.rep
        if self.args:
            res += '(' + ','.join(map(str,self.args)) + ')'
        return res
    @property
    def subs(self):
        return self.args
    def match(self,ev,binding=None):
        return (isinstance(ev,Symbol) and (ev.name == '*')
                or isinstance(ev,App) and (ev.rep == '*' or ev.rep == self.rep)
                and all(a.match(b,binding) for a,b in zip(self.args,ev.args)))
    def map(self,fun):
        return type(self)(mymap(fun,self.args))
    def __str__(self):
        return self.text()

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
        return res
    def match(self,l,binding=None):
        return (isinstance(l,Symbol) and (l.name == '*')
                or (isinstance(l,ListValue)
                    and len(l) == len(self)
                    and all(a.match(b,binding) for a,b in zip(self,l))))
    def map(self,fun):
        return type(self)(*[mymap(fun,x) for x in self])


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
    def match(self,d,binding=None):
        return (isinstance(d,Symbol) and (d.name == '*')
                or (isinstance(d,DictValue)
                    and all(k in self and self[k].match(v,binding) for k,v in d.iteritems())))
    def map(self,fun):
        return type(self)(*[(x,mymap(fun,y)) for x,y in self.iteritems()])

class EventGen(object):
    def __call__(self,evs):
        for ev in evs:
            yield ev
            for ev1 in self(ev.children):
                yield ev1

class EventRevGen(object):
    def __init__(self,addr):
        self.addr = addr
    def rec(self,things,addr,start=0):
        if addr != None:
            cs = addr.split('/',1)
            num = int(cs[0])-start
            thing = things[num]
            if len(cs) == 2:
                for a,t in self.rec(thing.children,cs[1],start=1):
                    yield (cs[0]+'/'+a,t)
                yield cs[0],thing
        else:
            num = len(things)
        for idx in xrange(num-1,-1,-1):
            thing = things[idx]
            for a,t in self.rec(thing.children,None,start=1):
                yield str(idx+start)+'/'+a,t
            yield str(idx+start),thing
    def __call__(self,evs):
        for ev in self.rec(evs,self.addr):
            yield ev

class EventFwdGen(object):
    def __init__(self,addr):
        self.addr = addr
    def rec(self,things,addr,start=0):
        if addr != None:
            cs = addr.split('/',1)
            num = int(cs[0])-start
            thing = things[num]
            caddr = cs[1] if len(cs) == 2 else None
            for a,t in self.rec(thing.children,caddr,start=1):
                yield (cs[0]+'/'+a,t)
        else:
            num = -1
        for idx in range(num+1,len(things)):
            thing = things[idx]
            yield str(idx+start),thing
            for a,t in self.rec(thing.children,None,start=1):
                yield str(idx+start)+'/'+a,t
    def __call__(self,evs):
        for ev in self.rec(evs,self.addr):
            yield ev

class Anchor(object):
    def __init__(self,anchor):
        self.anchor = anchor
    def __call__(self,s):
        if s.startswith('$'):
            path = s[1:].split('.')
            num = int(path[0])-1
            if num < 0 or num >= len(self.anchor.args):
                raise iu.IvyError(None,'event has no argument {}'.format(s))
            res = self.anchor.args[num]
            for field in path[1:]:
                if not isinstance(res,DictValue) or field not in res:
                    raise iu.IvyError(None,'value has no field {}'.format(field))
                res = res[field]
            return res
        return Symbol(s)

def filter(evs,pats,anchor=None):
    if anchor != None:
        pats = [e.map(Anchor(anchor)) for e in pats]
    for e in evs:
        if any(e.match(pat) for pat in pats):
            yield e

def find(evs,pats,anchor=None):
    if anchor != None:
        pats = [e.map(Anchor(anchor)) for e in pats]
    for a,e in evs:
        if any(e.match(pat,None) for pat in pats):
            return a,e
    return None

# Match against patters with free variables. Yields a sequence
# of pairs e,b where e is an event and b is a binding of free variable
# names to expressions.

def bind(evs,pats,anchor=None):
    if anchor != None:
        pats = [e.map(Anchor(anchor)) for e in pats]
    for e in evs:
        binding = dict()
        if any(e.match(pat,binding) for pat in pats):
            yield e,binding

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

t_ignore  = ' \t\r'

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_SYMBOL(t):
    r'[_a-zA-Z0-9\.\$\-]+|\*|".*?"'
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

def p_value_symbol_lparen_list_rparen(p):
    'value : SYMBOL LPAREN list RPAREN'
    p[0] = App(p[1],p[3])

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
parser = yacc.yacc(tabmodule='ev_parsetab',errorlog=yacc.NullLogger(),outputdir=tabdir)
#parser = yacc.yacc(tabmodule='ev_parsetab',outputdir=tabdir)

if __name__ == '__main__':
    while True:
       try:
           s = raw_input('events > ')
       except EOFError:
           break
       if not s: continue
       result = parser.parse(s)
#       print result
#       for a,x in EventFwdGen("2/2")(result):
#           print a + ':' + x.text()
       try:
           patstring = raw_input('patterns > ')
       except EOFError:
           break
       if not s: continue
       pats = parser.parse(patstring)
       for e,b in bind(EventGen()(result),pats):
           print 'event: {} binding: {}'.format(e,list((n,str(v)) for n,v in b.iteritems()))
           
           


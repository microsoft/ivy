#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ply.lex as lex
import ivy_utils as iu

tokens = (
   'COMMA',
   'LPAREN',
   'RPAREN',
   'PLUS',
   'TIMES',
   'DIV',
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
   'IFF',
   'SYMBOL',
   'LABEL',
   'VARIABLE',
   'COLON',
   'LE',
   'LT',
   'GE',
   'GT',
   'MINUS',
   'DOTS',
   'DOTDOTDOT',
   'NATIVEQUOTE',
   'PTO',
   'DOLLAR',
   'CARET',
)

reserved = all_reserved = {
   'relation' : 'RELATION',
   'individual' : 'INDIV',
   'function' : 'FUNCTION',
   'axiom' : 'AXIOM',
   'conjecture' : 'CONJECTURE',
   'schema' : 'SCHEMA',
   'instantiate' : 'INSTANTIATE',
   'instance' : 'INSTANTIATE',
   'derived' : 'DERIVED',
   'concept' : 'CONCEPT',
   'init' : 'INIT',
   'action' : 'ACTION',
   'method' : 'ACTION',
   'state' : 'STATE',
   'assume' : 'ASSUME',
   'assert' : 'ASSERT',
   'set' : 'SET',
   'null' : 'NULL',
   'old' : 'OLD',
   'from' : 'FROM',
   'update' : 'UPDATE',
   'params' : 'PARAMS',
   'in' : 'IN',
   'match' : 'MATCH',
   'ensures' : 'ENSURES',
   'requires' : 'REQUIRES',
   'modifies' : 'MODIFIES',
   'true' : 'TRUE',
   'false' : 'FALSE',
   'fresh' : 'FRESH',
   'module' : 'MODULE',
   'object' : 'OBJECT',
   'class' : 'MODULE',
   'type' : 'TYPE',
   'if' : 'IF',
   'else' : 'ELSE',
   'local' : 'LOCAL',
   'let' : 'LET',
   'call' : 'CALL',
   'entry' : 'ENTRY',
   'macro' : 'MACRO',
   'interpret' : 'INTERPRET',
   'forall' : 'FORALL',
   'exists' : 'EXISTS',
   'returns' : 'RETURNS',
   'mixin' : 'MIXIN',
   'execute' : 'MIXIN',
   'before' : 'BEFORE',
   'after' : 'AFTER',
   'isolate' : 'ISOLATE',
   'with' : 'WITH',
   'export' : 'EXPORT',
   'delegate' : 'DELEGATE',
   'import' : 'IMPORT',
   'using' : 'USING',
   'include' : 'INCLUDE',
   'progress' : 'PROGRESS',
   'rely' : 'RELY',
   'mixord' : 'MIXORD',
   'extract' : 'EXTRACT',
   'destructor' : 'DESTRUCTOR',
   'some' : 'SOME',
   'maximizing' : 'MAXIMIZING',
   'minimizing' : 'MINIMIZING',
   'private' : 'PRIVATE',
   'implement' : 'IMPLEMENT',
   'property' : 'PROPERTY',
   'while' : 'WHILE',
   'invariant' : 'INVARIANT',
   'struct' : 'STRUCT',
   'definition' : 'DEFINITION',
   'ghost' : 'GHOST',
   'alias' : 'ALIAS',
   'trusted' : 'TRUSTED',
   'this' : 'THIS',
   'var' : 'VAR',
   'attribute' : 'ATTRIBUTE',
   'variant' : 'VARIANT',
   'of' : 'OF',
   'scenario' : 'SCENARIO',
   'proof' : 'PROOF',
   'named' : 'NAMED',
   'fresh' : 'FRESH',
   'temporal' : 'TEMPORAL',
   'globally' : 'GLOBALLY',
   'eventually' : 'EVENTUALLY',
   'decreases' : 'DECREASES',
   'specification' : 'SPECIFICATION',
   'implementation' : 'IMPLEMENTATION',
   'ensure' : 'ENSURE',
   'require' : 'REQUIRE',
   'around' : 'AROUND',
   'parameter' : 'PARAMETER',
   'apply' : 'APPLY',
   'theorem' : 'THEOREM',
   'showgoals' : 'SHOWGOALS',
   'defergoal' : 'DEFERGOAL',
   'spoil' : 'SPOIL',
   'explicit' : 'EXPLICIT',
   'thunk' : 'THUNK',
    'isa' : 'ISA',
   'autoinstance' : 'AUTOINSTANCE',
   'constructor' : 'CONSTRUCTOR',
   'finite' : 'FINITE',
   'tactic' : 'TACTIC',
}

tokens += tuple(all_reserved.values())


t_TILDA    = r'\~'
t_COMMA    = r'\,'
t_PLUS    = r'\+'
t_TIMES   = r'\*'
t_DIV   = r'\/'
t_MINUS   = r'\-'
t_LT      = r'\<'
t_LE      = r'\<='
t_GT      = r'\>'
t_GE      = r'\>='
t_PTO      = r'\*>'
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_OR = r'\|'
t_AND = r'\&'
t_EQ = r'\='
t_TILDAEQ = r'\~='
t_SEMI = r'\;'
t_ASSIGN = r'\:='
t_DOT = r'\.'
t_LCB  = r'\{'
t_RCB  = r'\}'
t_ARROW = r'\->'
t_IFF = r'\<->'
t_COLON = r':'
t_DOTS = r'\.\.'
t_DOTDOTDOT = r'\.\.\.'
t_DOLLAR = r'\$'
t_CARET = r'\^'

t_ignore  = ' \t\r'
t_ignore_COMMENT = r'\#.*'

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_SYMBOL(t):
    r'[_a-z0-9][_a-zA-Z0-9]*(\[[ab-zA-Z_0-9.]*\])*|".*?"'
    t.type = reserved.get(t.value,'SYMBOL')
    return t

def t_LABEL(t):
    r'\[[_a-zA-Z0-9\]\[]+\]'
    t.type = reserved.get(t.value,'LABEL')
    return t

def t_VARIABLE(t):
    r'[A-Z][_a-zA-Z0-9]*(\[[ab-zA-Z_0-9]*\])*'
    t.type = reserved.get(t.value,'VARIABLE')
    return t

def t_NATIVEQUOTE(t):
    r'<<<[\s\S]*?>>>'
    t.lexer.lineno += sum(1 for c in t.value if c == '\n')
    t.type = reserved.get(t.value,'NATIVEQUOTE')
    return t

class TokenErrorNode(object):
    def __init__(self,token):
        self.lineno = iu.Location(iu.filename,token.lineno)

def t_error(t):
    raise iu.IvyError(TokenErrorNode(t),"illegal character '{}'".format(t.value[0]))
    print "Illegal character '%s'" % t.value[0]

lexer = lex.lex(errorlog=lex.NullLogger())

class LexerVersion(object):
    """ Context Manager that sets the lexer based on the given language version
    """
    def __init__(self,version):
        self.version = version
    def __enter__(self):
        global reserved
        self.orig_reserved = reserved
        reserved = dict(all_reserved)
#        print "version {}".format(self.version)
        if self.version <= [1,0]:
            for s in ['state','local']:
#                print "deleting {}".format(s)
                del reserved[s]
        if self.version <= [1,1]:
            for s in ['returns','mixin','before','after','isolate','with','export','delegate','import','include']:
#                print "deleting {}".format(s)
                if s in reserved:
                    del reserved[s]
        else:
            for s in ['state','set','null','match']:
                if s in reserved:
                    del reserved[s]
        if self.version <= [1,4]:
            for s in ['function','class','object','method','execute','destructor',
                      'some','maximizing','maximizing','private','implement','using','property','while','invariant','struct','definition','ghost','alias','trusted','this','var','attribute','scenario','proof','named','fresh']:
#                print "deleting {}".format(s)
                if s in reserved:
                    del reserved[s]
        if self.version <= [1,5]:
            for s in ['variant','of', 'globally', 'eventually', 'temporal']:
#                print "deleting {}".format(s)
                if s in reserved:
                    del reserved[s]
        if self.version <= [1,6]:
            for s in ['decreases','specification','implementation','require','ensure','around','parameter','apply','theorem','showgoals','spoil','explicit','thunk','isa','autoinstance','constructor','tactic','finite']:
                if s in reserved:
                    del reserved[s]
        else:
            for s in ['requires','ensures','method']:
                if s in reserved:
                    del reserved[s]

        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global reserved
        reserved = self.orig_reserved
        return False # don't block any exceptions

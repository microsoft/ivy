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
}

tokens += tuple(all_reserved.values())


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
t_EQ = r'\='
t_SEMI = r'\;'
t_DOT = r'\.'
t_LCB  = r'\{'
t_RCB  = r'\}'
t_COLON = r':'
t_DOTS = r'\.\.'
t_DOTDOTDOT = r'\.\.\.'
t_DOLLAR = r'\$'

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
    r'\[[_a-zA-Z0-9]+\]'
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

# unicode characters are detected from `globals()`, where their name
# start with 't_' and their type is `unicode`. note that this is used 
# in all versions.

# unicode characters that overlap reserved words.
t_FORALL     = u'\u2200'
t_EXISTS     = u'\u2203'
t_GLOBALLY   = u'\u25a1'
t_EVENTUALLY = u'\u25c7'

# unicode characters that overlap regexes. the original regexes must be 
# commented out. we assume the pattern 'a|(b)' where any backslash in the 
# pattern should just be removed (i.e., we do not expect \n, etc.).
import re
unicode_regex_matcher = re.compile(r'^(.*)\|\((.*)\)').match
t_ARROW    = u'\u2192|(->)'
t_IFF      = u'\u2194|(<->)'
t_TILDA    = u'\u00AC|(~)'
t_AND      = u'\u2227|(\\&)'
t_OR       = u'\u2228|(\\|)'
t_TILDAEQ  = u'\u2260|(\\~=)'
t_ASSIGN   = u'\u2254|(\\:=)'


lexer_inner = lex.lex(errorlog=lex.NullLogger())
class IvyUnicodeLexer(object):
    unicode_tokens = dict(
        (
            # extract the first subpattern, assuming the said pattern.
            key if val else unicode_regex_matcher(key).group(1),
            # extract the second subpattern, assuming the said pattern.
            val or unicode_regex_matcher(key).group(2).replace('\\', '').encode('ascii')
        ) 
        for key, val in
        (
            (
                # variable value
                globals()[var_name],
                # variable from `all_reserved`, or none otherwise
                next((word for word, token in all_reserved.items() if token == var_name[len('t_'):]), None) 
            )
            # collect the appropriate global variables 
            for var_name in globals() if 
            var_name.startswith('t_') and
            isinstance(globals()[var_name], unicode)
        )
    )

    @staticmethod
    def input(val):
        return lexer_inner.input(unicode(val, "utf-8"))

    @staticmethod
    def token():
        t = lexer_inner.token()
        if t is not None and isinstance(t.value, unicode):
            if t.value in IvyUnicodeLexer.unicode_tokens:
                t.value = IvyUnicodeLexer.unicode_tokens[t.value]
            else:
                # a var name may not contain unicode characters. if so, an 
                # exception will be raised.
                t.value = t.value.encode('ascii')
        
        return t
lexer = IvyUnicodeLexer()

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
            for s in ['decreases','specification','implementation','require','ensure','around','parameter']:
                if s in reserved:
                    del reserved[s]
        else:
            for s in ['requires','ensures']:
                if s in reserved:
                    del reserved[s]

        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global reserved
        reserved = self.orig_reserved
        return False # don't block any exceptions

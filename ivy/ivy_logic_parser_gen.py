#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_lexer import *
import ply.yacc as yacc

# Parser for formulas

precedence = (
    ('left', 'SEMI'),
    ('left', 'GLOBALLY', 'EVENTUALLY'),
    ('left', 'IF'),
    ('left', 'ELSE'),
    ('left', 'OR'),
    ('left', 'AND'),
    ('left', 'TILDA'),
    ('left', 'EQ','LE','LT','GE','GT'),
    ('left', 'TILDAEQ'),
    ('left', 'COLON'),
    ('left', 'PLUS'),
    ('left', 'MINUS'),
    ('left', 'TIMES'),
    ('left', 'DIV'),
    ('left', 'DOLLAR'),
    ('left', 'OLD'),
    ('left', 'DOT'),
)

from ivy_logic_parser import *

def p_error(token):
    raise LogicParseError(token,"syntax error")

import os
tabdir = os.path.dirname(os.path.abspath(__file__))
formula_parser = yacc.yacc(start = 'fmla', tabmodule='ivy_formulatab',errorlog=yacc.NullLogger(),outputdir=tabdir,debug=None)
#formula_parser = yacc.yacc(start = 'fmla', tabmodule='ivy_formulatab')
term_parser = yacc.yacc(start = 'term', tabmodule='ivy_termtab',errorlog=yacc.NullLogger(),outputdir=tabdir,debug=None)


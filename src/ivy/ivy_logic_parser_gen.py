#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_lexer import *
import ply.yacc as yacc

# Parser for formulas

precedence = (
    ('left', 'OR'),
    ('left', 'AND'),
    ('left', 'TILDA'),
    ('left', 'EQ','LE','LT','GE','GT'),
    ('left', 'TILDAEQ'),
    ('left', 'COLON'),
    ('left', 'PLUS'),
    ('left', 'MINUS'),
    ('left', 'TIMES'),
)

from ivy_logic_parser import *

def p_error(token):
    raise LogicParseError(token,"syntax error")

formula_parser = yacc.yacc(start = 'fmla', tabmodule='ivy_formulatab',errorlog=yacc.NullLogger())
#formula_parser = yacc.yacc(start = 'fmla', tabmodule='ivy_formulatab')
term_parser = yacc.yacc(start = 'term', tabmodule='ivy_termtab',errorlog=yacc.NullLogger())


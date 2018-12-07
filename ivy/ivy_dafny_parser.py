#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_dafny_lexer import *
from ivy_dafny_grammar import *
from ivy_utils import p_error, parse_with

import ply.yacc as yacc

import os
tabdir = os.path.dirname(os.path.abspath(__file__))
parser = yacc.yacc(start='top',tabmodule='ivy_dafny_parsetab',errorlog=yacc.NullLogger(),outputdir=tabdir)

def parse(s):
    return parse_with(s,parser,lexer)

if __name__ == "__main__":
    print parser.parse('var x : y; method P(x:T) ensures x == y; {x := y;}')

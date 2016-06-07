#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy_dafny_ast as da

#### TODO: ghost, static, this, constructor

precedence = (
    ('left', 'IF'),
    ('left', 'ELSE'),
    ('left','IFF'),
    ('left','IMPLIES'),
    ('left', 'OR'),
    ('left', 'AND'),
    ('left', 'BANG'),
    ('left', 'EQEQ','BANGEQ','LE','LT','GE','GT'),
    ('left', 'PLUS','MINUS'),
    ('left', 'TIMES'),
)

def p_top(p):
    'top : '
    p[0] = da.Module()

def p_top_top_field(p):
    'top : top field'
    p[0] = p[1]
    p[0].declare(p[2])

def p_field_var_vardecl(p):
    'field : VAR vardecl SEMI'
    p[0] = da.VarDecl(p[2])

def p_vardecl_symbol_colon_type_semi(p):
    'vardecl : SYMBOL COLON type'
    p[0] = da.TypedSymbol(p[1],p[3])

def p_symbol_symbol(p):
    'symbol : SYMBOL'
    p[0] = da.Numeral(p[1]) if p[1][0].isdigit() else da.Symbol(p[1])

def p_type_symbol(p):
    'type : SYMBOL'
    p[0] = da.Type(p[1])

def p_args_lparen_rparen(p):
    'args : LPAREN RPAREN'
    p[0] = []

def p_args_lparen_vardecls_rparen(p):
    'args : LPAREN vardecls RPAREN'
    p[0] = p[2]

def p_vardecls_vardecl(p):
    'vardecls : vardecl'
    p[0] = [p[1]]

def p_vardecls_vardecls_comma_vardecl(p):
    'vardecls : vardecls COMMA vardecl'
    p[0] = p[1]
    p[0].append(p[3])

def p_opt_semi(p):
    'opt_semi : '

def p_opt_semi_semi(p):
    'opt_semi : SEMI'

def p_requires(p):
    'requires : '
    p[0] = None

def p_requires_requires_expr(p):
    'requires : REQUIRES expr opt_semi'
    p[0] = p[2]

def p_modifies(p):
    'modifies : '
    p[0] = None

def p_modifies_modifies_atoms(p):
    'modifies : MODIFIES modsets opt_semi'
    p[0] = p[2]

def p_ensures(p):
    'ensures : '
    p[0] = None

def p_ensures_ensures_expr(p):
    'ensures : ENSURES expr opt_semi'
    p[0] = p[2]

def p_returns(p):
    'returns : '
    p[0] = []

def p_returns_returns_args(p):
    'returns : RETURNS args'
    p[0] = p[2]

def p_decreases(p):
    'decreases : '
    p[0] = None

def p_decreases_decreases_expr(p):
    'decreases : DECREASES expr opt_semi'
    p[0] = p[2]

def p_field_method_symbol_args_returns_requires_modifies_ensures_decreases_lcb_stmts_rcb(p):
    'field : METHOD symbol args returns requires modifies ensures decreases LCB stmts RCB'
    p[0] = da.MethodDecl(*(p[2:9]+[p[10]]))
    p[0].lineno = p.lineno(1)

def p_modsets(p):
    'modsets : '
    p[0] = []

def p_modsets_modset(p):
    'modsets : modset'
    p[0] = p[1]

def p_modsets_modsets_comma_modset(p):
    'modsets : modsets COMMA modset'
    p[0] = p[1]
    p[0].extend(p[3])

def p_modset_symbol(p):
    'modset : symbol'
    p[0] = [p[1]]

def p_modset_lcb_rcb(p):
    'modset : LCB RCB'
    p[0] = []

def p_modset_lcb_symbols_rcb(p):
    'modset : LCB symbols RCB'
    p[0] = p[2]

def p_symbols_symbol(p):
    'symbols : symbol'
    p[0] = [p[1]]

def p_symbols_symbols_comma_symbols(p):
    'symbols : symbols COMMA symbol'
    p[0] = p[1]
    p[0].append(p[3])

def p_expr_lparen_expr_rparen(p):
    'expr : LPAREN expr RPAREN'
    p[0] = p[2]

def p_expr_symbol(p):
    'expr : symbol'
    p[0] = da.App(p[1])

def p_expr_symbol_lparen_rparen(p):
    'expr : symbol LPAREN RPAREN'
    p[0] = da.Call(p[1])

def p_expr_symbol_lparen_exprs_rparen(p):
    'expr : symbol LPAREN exprs RPAREN'
    p[0] = da.Call(*([p[1]] + p[3]))

def p_expr_expr_and_expr(p):
    'expr : expr AND expr'
    p[0] = da.App(da.And(),p[1],p[3])

def p_expr_expr_or_expr(p):
    'expr : expr OR expr'
    p[0] = da.App(da.Or(),p[1],p[3])

def p_expr_expr_implies_expr(p):
    'expr : expr IMPLIES expr'
    p[0] = da.App(da.Implies(),p[1],p[3])

def p_expr_expr_iff_expr(p):
    'expr : expr IFF expr'
    p[0] = da.App(da.Iff(),p[1],p[3])

def p_expr_expr_not_expr(p):
    'expr : BANG expr'
    p[0] = da.App(da.Not(),p[2])

def p_expr_expr_eqeq_expr(p):
    'expr : expr EQEQ expr'
    p[0] = da.App(da.Eq(),p[1],p[3])

def p_expr_expr_bangeq_expr(p):
    'expr : expr BANGEQ expr'
    p[0] = da.App(da.Not(),da.App(da.Eq(),p[1],p[3]))

def p_expr_expr_PLUS_expr(p):
    'expr : expr PLUS expr'
    p[0] = da.App(da.InfixSymbol(p[2]),p[1],p[3])
    p[0].lineno = p.lineno(2)
    
def p_expr_expr_MINUS_expr(p):
    'expr : expr MINUS expr'
    p[0] = da.App(da.InfixSymbol(p[2]),p[1],p[3])
    p[0].lineno = p.lineno(2)

def p_expr_MINUS_expr(p):
    'expr : MINUS expr'
    p[0] = da.App(da.Symbol(p[1]),p[2])
    p[0].lineno = p.lineno(2)

def p_expr_expr_TIMES_expr(p):
    'expr : expr TIMES expr'
    p[0] = da.App(da.InfixSymbol(p[2]),p[1],p[3])
    p[0].lineno = p.lineno(2)

def p_expr_expr_LE_expr(p):
    'expr : expr LE expr'
    p[0] = da.App(da.InfixRelation(p[2]),p[1],p[3])
    p[0].lineno = p.lineno(2)

def p_expr_expr_LT_expr(p):
    'expr : expr LT expr'
    p[0] = da.App(da.InfixRelation(p[2]),p[1],p[3])
    p[0].lineno = p.lineno(2)

def p_expr_expr_GE_expr(p):
    'expr : expr GE expr'
    p[0] = da.App(da.InfixRelation(p[2]),p[1],p[3])
    p[0].lineno = p.lineno(2)

def p_expr_expr_GT_expr(p):
    'expr : expr GT expr'
    p[0] = da.App(da.InfixRelation(p[2]),p[1],p[3])
    p[0].lineno = p.lineno(2)

def p_lvalue_symbol(p):
    'lvalue : symbol'
    p[0] = da.App(p[1])

def p_stmt_lvalues_assign_exprs_semi(p):
    'stmt : lvalues ASSIGN exprs SEMI'
    p[0] = da.AssignStmt(da.Tuple(*p[1]),da.Tuple(*p[3]))
    p[0].lineno = p.lineno(2);

def p_lvalues_lvalue(p):
    'lvalues : lvalue'
    p[0] = [p[1]]

def p_lvalues_lvalues_lvalue(p):
    'lvalues : lvalues COMMA lvalue'
    p[0] = p[1]
    p[0].append(p[3])

def p_exprs_expr(p):
    'exprs : expr'
    p[0] = [p[1]]

def p_exprs_exprs_expr(p):
    'exprs : exprs COMMA expr'
    p[0] = p[1]
    p[0].append(p[3])

def p_stmt_assume_expr_semi(p):
    'stmt : ASSUME expr SEMI'
    p[0] = da.AssumeStmt(p[2])
    p[0].lineno = p.lineno(1);

def p_stmt_assert_expr_semi(p):
    'stmt : ASSERT expr SEMI'
    p[0] = da.AssertStmt(p[2])
    p[0].lineno = p.lineno(1);

def p_stmts_stmt(p):
    'stmts : stmt'
    p[0] = [p[1]]
    
def p_stmts_stmts_stmt(p):
    'stmts : stmts stmt'
    p[0] = p[1]
    p[0].append(p[2])

def p_invariant_invariant_expr(p):
    'invariant : INVARIANT expr'
    p[0] = p[2]

def p_invariants(p):
    'invariants : '
    p[0] = []

def p_invariants_invariants_invariant(p):
    'invariants : invariants invariant'
    p[0] = p[1]
    p[1].append(p[2])

def p_stmt_while_expr_modifies_invariant_lcb_stmts_rcb(p):
    'stmt : WHILE expr modifies invariants LCB stmts RCB'
    p[0] = da.WhileStmt(p[2],p[3],da.App(da.And(),*p[4]),p[6])
    p[0].lineno = p.lineno(1)

def p_stmt_if_expr_lcb_stmt_rcb(p):
    'stmt : IF expr LCB stmts RCB'
    p[0] = da.IfStmt(p[2],p[4])
    p[0].lineno = p.lineno(1);

def p_stmt_if_expr_lcb_stmt_rcb_else_LCB_stmt_RCB(p):
    'stmt : IF expr LCB stmts RCB ELSE LCB stmts RCB'
    p[0] = da.IfStmt(p[2],p[4],p[8])
    p[0].lineno = p.lineno(1);

def p_stmt_var_vardecl(p):
    'stmt : VAR vardecl SEMI'
    p[0] = da.VarStmt(p[2])
    p[0].lineno = p.lineno(1);

def p_stmt_var_assign_expr_semi(p):
    'stmt : VAR symbols ASSIGN exprs SEMI'
    p[0] = da.VarStmt(da.AssignStmt(da.Tuple(*[da.App(x) for x in p[2]]),da.Tuple(*p[4])))
    p[0].lineno = p.lineno(1);
    
def p_stmt_return_semi(p):
    'stmt : RETURN SEMI';
    p[0] = da.ReturnStmt();
    p[0].lineno = p.lineno(1);

def p_stmt_return_exprs_semi(p):
    'stmt : RETURN exprs SEMI';
    p[0] = da.ReturnStmt(*p[2]);
    p[0].lineno = p.lineno(1);




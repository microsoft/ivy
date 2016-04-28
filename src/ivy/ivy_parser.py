#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_concept_space import NamedSpace, ProductSpace, SumSpace
from ivy_ast import *
from ivy_actions import AssumeAction, AssertAction, EnsuresAction, SetAction, AssignAction, HavocAction, IfAction, AssignFieldAction, NullFieldAction, CopyFieldAction, InstantiateAction, CallAction, LocalAction, LetAction, Sequence, UpdatePattern, PatternBasedUpdate, SymbolList, UpdatePatternList, Schema, ChoiceAction
from ivy_lexer import *
import ivy_utils as iu
import copy


import ply.yacc as yacc
import string

precedence = (
    ('left', 'SEMI'),
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
)


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
    
class Redefining(ParseError):
    def __init__(self,name,lineno,orig_lineno):
        msg = 'redefining ' + str(name)
        if orig_lineno != None:
            msg += " (from line {})".format(orig_lineno)
        super(Redefining, self).__init__(lineno,None,msg)

error_list = []

stack = []

def get_lineno(p,n):
    return (iu.filename,p.lineno(n))

def report_error(error):
    error_list.append(error)

def stack_lookup(name):
    for ivy in reversed(stack):
        if name in ivy.modules:
            return ivy.modules[name]
    return None

def do_insts(ivy,insts):
    others = []
    for instantiation in insts:
        pref, inst = instantiation.args
        defn = stack_lookup(inst.relname)
        if defn:
#            print "instantiating %s" % inst.relname
            aparams = inst.args
            fparams = defn.args[0].args
            if len(aparams) != len(fparams):
                raise iu.IvyError(instantiation,"wrong number of arguments to module {}".format(inst.relname))
            subst = dict((x.rep,y.rep) for x,y in zip(fparams,aparams))
            module = defn.args[1]
            for decl in module.decls:
#                print "before: %s" % (decl)
                idecl = subst_prefix_atoms_ast(decl,subst,pref,module.defined)
                if isinstance(idecl,ActionDecl):
                    for foo in idecl.args:
                        if not hasattr(foo.args[1],'lineno'):
                            print 'no lineno: {}'.format(foo)
#                print "after: %s" % (idecl)
                ivy.declare(idecl)
        else:
            others.append(inst)
    if others:
        ivy.declare(InstantiateDecl(*others))


class Ivy(object):
    def __init__(self):
        self.decls = []
        self.defined = dict()
        self.modules = dict()
        self.macros = dict()
    def __repr__(self):
        return '\n'.join([repr(x) for x in self.decls])
    def declare(self,decl):
        for df in decl.defines():
            self.define(df)
        self.decls.append(decl)
        if isinstance(decl,MacroDecl):
            for d in decl.args:
                self.macros[d.defines()] = d

    def define(self,df):
        name,lineno = df
        if name in self.defined:
            report_error(Redefining(name,lineno,self.defined[name]))
        self.defined[name] = lineno


def p_top(p):
    'top :'
    p[0] = Ivy()
    stack.append(p[0])

def p_top_import_symbol(p):
    'top : top IMPORT SYMBOL'
    p[0] = p[1]
    pref = Atom(p[3],[])
    module = importer(p[3])
    for decl in module.decls:
        idecl = subst_prefix_atoms_ast(decl,{},pref,module.defined)
        p[0].declare(idecl)

def p_top_include_symbol(p):
    'top : top INCLUDE SYMBOL'
    p[0] = p[1]
    pref = Atom(p[3],[])
    module = importer(p[3])
    for decl in module.decls:
        p[0].declare(decl)

def p_labeledfmla_fmla(p):
    'labeledfmla : fmla'
    p[0] = LabeledFormula(None,p[1])
    p[0].lineno = p[1].lineno
    
def p_labeledfmla_label_fmla(p):
    'labeledfmla : LABEL fmla'
    p[0] = LabeledFormula(Atom(p[1][1:-1],[]),p[2])
    p[0].lineno = get_lineno(p,1)

def p_top_axiom_labeledfmla(p):
    'top : top AXIOM labeledfmla'
    p[0] = p[1]
    d = AxiomDecl(p[3])
    d.lineno = get_lineno(p,2)
    p[0].declare(d)

def p_top_conjecture_labeledfmla(p):
    'top : top CONJECTURE labeledfmla'
    p[0] = p[1]
    d = ConjectureDecl(p[3])
    d.lineno = get_lineno(p,2)
    p[0].declare(d)

def p_top_module_atom_eq_lcb_top_rcb(p):
    'top : top MODULE atom EQ LCB top RCB'
    p[0] = p[1]
    d = Definition(app_to_atom(p[3]),p[6])
    p[0].declare(ModuleDecl(d))
    p[0].modules[d.defines()] = d
    stack.pop()

def p_top_macro_atom_eq_lcb_action_rcb(p):
    'top : top MACRO atom EQ LCB action RCB'
    p[0] = p[1]
    d = Definition(app_to_atom(p[3]),p[6])
    p[0].declare(MacroDecl(d))

def p_top_schema_defn(p):
    'top : top SCHEMA defn'
    p[0] = p[1]
    p[0].declare(SchemaDecl(Schema(p[3],[])))

def p_top_instantiate_insts(p):
    'top : top INSTANTIATE insts'
    p[0] = p[1]
    do_insts(p[0],p[3])

def p_insts_inst(p):
    'insts : inst'
    p[0] = [p[1]]

def p_insts_insts_comma_inst(p):
    'insts : insts COMMA inst'
    p[0] = p[1]
    p[0].append(p[3])

def p_pname_symbol(p):
    'pname : SYMBOL'
    p[0] = App(p[1])
    p[0].lineno = get_lineno(p,1)

def p_pname_var(p):
    'pname : var'
    p[0] = p[1]

def p_pname_infix(p):
    'pname : infix'
    p[0] = App(p[1])
    p[0].lineno = get_lineno(p,1)

def p_pname_relop(p):
    'pname : relop'
    p[0] = App(p[1])
    p[0].lineno = get_lineno(p,1)

def p_pnames(p):
    'pnames : '
    p[0] = []

def p_pnames_pname(p):
    'pnames : pname'
    p[0] = [p[1]]

def p_pnames_pnames_pname(p):
    'pnames : pnames COMMA pname'
    p[0] = p[1]
    p[0].append(p[3])

def p_modinst_symbol(p):
    'modinst : SYMBOL'
    p[0] = Atom(p[1],[])
    p[0].lineno = get_lineno(p,1)

def p_modinst_symbol_lp_pnames_rp(p):
    'modinst : SYMBOL LPAREN pnames RPAREN'
    p[0] = Atom(p[1],p[3])
    p[0].lineno = get_lineno(p,1)

def p_inst_modinst(p):
   'inst : modinst'
   p[0] = Instantiation(None,app_to_atom(p[1]))

def p_inst_atom_colon_modinst(p):
    'inst : modinst COLON modinst'
    p[0] = Instantiation(app_to_atom(p[1]),app_to_atom(p[3]))

def p_top_symdecl(p):
    'top : top symdecl'
    p[0] = p[1]
    p[0].declare(p[2])

def p_symdecl_relationdecl(p):
    'symdecl : relationdecl'
    p[0] = p[1]

def p_symdecl_constantdecl(p):
    'symdecl : constantdecl'
    p[0] = p[1]

def p_constantdecl_constant_tterms(p):
    'constantdecl : INDIV tterms'
    p[0] = ConstantDecl(*p[2])

def p_relationdecl_relation_tatoms(p):
    'relationdecl : RELATION tatoms'
    p[0] = RelationDecl(*apps_to_atoms(p[2]))

def p_tatoms_tatom(p):
    'tatoms : tatom'
    p[0] = [p[1]]

def p_tatoms_tatoms_comma_tatom(p):
    'tatoms : tatoms COMMA tatom'
    p[0] = p[1]
    p[0].append(p[3])

def p_tatom_symbol(p):
    'tatom : SYMBOL'
    p[0] = Atom(p[1],[])
    p[0].lineno = get_lineno(p,1)

def p_tatom_symbol_targs(p):
    'tatom : SYMBOL targs'
    p[0] = Atom(p[1],p[2])
    p[0].lineno = get_lineno(p,1)

def p_tatom_lp_symbol_relop_symbol_rp(p):
    'tatom : LPAREN var relop var RPAREN'
    p[0] = Atom(p[3],[p[2],p[4]])
    p[0].lineno = get_lineno(p,3)

def p_top_derived_defns(p):
    'top : top DERIVED defns'
    p[0] = p[1]
    p[0].declare(DerivedDecl(*p[3]))

def p_top_progress_defns(p):
    'top : top PROGRESS defns'
    p[0] = p[1]
    p[0].declare(ProgressDecl(*p[3]))

def p_top_rely_atom_arrow_atom(p):
    'top : top RELY atom ARROW atom'
    p[0] = p[1]
    p[0].declare(RelyDecl(Implies(p[3],p[5])))

def p_top_mixord_callatom_arrow_callatom(p):
    'top : top MIXORD callatom ARROW callatom'
    p[0] = p[1]
    p[0].declare(MixOrdDecl(Implies(p[3],p[5])))

def p_top_rely_atom(p):
    'top : top RELY atom'
    p[0] = p[1]
    p[0].declare(RelyDecl(p[3]))

def p_top_concept_cdefns(p):
    'top : top CONCEPT cdefns'
    p[0] = p[1]
    p[0].declare(ConceptDecl(*p[3]))

def p_top_init_fmla(p):
    'top : top INIT labeledfmla'
    p[0] = p[1]
    d = InitDecl(p[3])
    d.lineno = get_lineno(p,2)
    p[0].declare(d)

def p_top_update_terms_from_terms_upaxes(p):
    'top : top UPDATE apps FROM apps upaxes'
    p[0] = p[1]
    dfns = [x.rep for x in p[3]]
    deps = [x.rep for x in p[5]]
    p[0].declare(UpdateDecl(PatternBasedUpdate(SymbolList(*dfns),
                                               SymbolList(*deps),
                                               UpdatePatternList(*p[6]))))

def p_top_type_symbol(p):
    'top : top TYPE SYMBOL'
    p[0] = p[1]
    tdfn = TypeDef(p[3],UninterpretedSort(p[3]))
    tdfn.lineno = get_lineno(p,3)
    p[0].declare(TypeDecl(tdfn))

def p_top_type_symbol_eq_sort(p):
    'top : top TYPE SYMBOL EQ sort'
    p[0] = p[1]
    p[5].name = p[3]
    tdfn = TypeDef(p[3],p[5])
    tdfn.lineno = get_lineno(p,4)
    p[0].declare(TypeDecl(tdfn))

def p_tsyms_tsym(p):
    'tsyms : var'
    p[0] = [p[1]]

def p_tsyms_tsyms_comma_tsym(p):
    'tsyms : tsyms COMMA var'
    p[0] = p[1]
    p[0].append(p[3])

def p_targs_lparen_rparen(p):
    'targs : LPAREN RPAREN'
    p[0] = []

def p_targs_lparen_tsyms_rparen(p):
    'targs : LPAREN tsyms RPAREN'
    p[0] = p[2]

def p_param_term_colon_symbol(p):
    'param : SYMBOL COLON SYMBOL'
    p[0] = App(p[1])
    p[0].lineno = get_lineno(p,1)
    p[0].sort = p[3]

def p_params_param(p):
    'params : param'
    p[0] = [p[1]]

def p_params_params_comma_param(p):
    'params : params COMMA param'
    p[0] = p[1]
    p[0].append(p[3])

def p_optargs(p):
    'optargs : '
    p[0] = []

def p_optargs_params(p):
    'optargs : LPAREN params RPAREN'
    p[0] = p[2]

def p_optreturns(p):
    'optreturns :'
    p[0] = []
    
def p_optreturns_tsyms(p):
    'optreturns : RETURNS LPAREN params RPAREN'
    p[0] = p[3]

def p_optactualreturns(p):
    'optactualreturns :'
    p[0] = []

def p_optactualreturns(p):
    'optactualreturns : callatoms ASSIGN'
    p[0] = p[1]

def p_tapp_symbol(p):
    'tapp : SYMBOL'
    p[0] = App(p[1])
    p[0].lineno = get_lineno(p,1)

def p_tapp_symbol_targs(p):
    'tapp : SYMBOL targs'
    p[0] = App(p[1],*p[2])
    p[0].lineno = get_lineno(p,1)

def p_tapp_lp_symbol_infix_symbol_rp(p):
    'tapp : LPAREN var infix var RPAREN'
    p[0] = App(p[3],p[2],p[4])
    p[0].lineno = get_lineno(p,3)


def p_tterm_term(p):
    'tterm : tapp'
    p[0] = p[1]

def p_tterm_term_colon_symbol(p):
    'tterm : tapp COLON SYMBOL'
    p[0] = p[1]
    p[0].sort = p[3]

def p_tterms_tterm(p):
    'tterms : tterm'
    p[0] = [p[1]]

def p_tterms_tterms_comma_tterm(p):
    'tterms : tterms COMMA tterm'
    p[0] = p[1]
    p[0].append(p[3])

def p_sort_lcb_names_rcb(p):
    'sort : LCB names RCB'
    p[0] = EnumeratedSort(p[2])

def p_names_symbol(p):
    'names : SYMBOL'
    p[0] = [p[1]]

def p_names_names_comma_symbol(p):
    'names : names COMMA SYMBOL'
    p[0] = p[1]
    p[0].append(p[3])

def p_upaxes(p):
    'upaxes : '
    p[0] = []

def p_upaxes_upaxes_upax(p):
    'upaxes : upaxes upax'
    p[0] = p[1]
    p[0].append(p[2])

if True or iu.get_numeric_version() <= [1]:
    def p_upax_params_apps_in_action_arrow_ensures_fmla(p):
        'upax : PARAMS tterms IN action ARROW requires ensures'
        p[0] = UpdatePattern(ConstantDecl(*p[2]),p[4],p[6],p[7])
else:
    def p_upax_params_apps_in_action_ensures_fmla(p):
        'upax : PARAMS tterms IN action requires ensures'
        p[0] = UpdatePattern(ConstantDecl(*p[2]),p[4],p[5],p[6])


def p_requires(p):
    'requires : '
    p[0] = And()

def p_requires_requires_fmla(p):
    'requires : REQUIRES fmla'
    p[0] = p[2]

def p_modifies(p):
    'modifies : '
    p[0] = None

def p_modifies_modifies_lcb_rcb(p):
    'modifies : MODIFIES LCB RCB'
    p[0] = []

def p_modifies_modofies_times(p):
    'modifies : MODIFIES TIMES'
    p[0] = None

def p_modifies_modifies_atoms(p):
    'modifies : MODIFIES atoms'
    p[0] = p[2]

# def p_ensures(p):
#     'ensures : '
#     p[0] = And()

def p_ensures_ensures_fmla(p):
    'ensures : ENSURES fmla'
    p[0] = p[2]

def p_optaction(p):
    'optaction :'
    p[0] = Sequence()

def p_optaction_action(p):
    'optaction : action'
    p[0] = p[1]

if iu.get_numeric_version() <= [1,1]:
  def p_top_action_symbol_eq_loc_action_loc(p):
    'top : top ACTION SYMBOL loc EQ LCB optaction RCB loc'
    p[0] = p[1]
    if not hasattr(p[7],'lineno'):
        p[7].lineno = get_lineno(p,6)
    p[0].declare(ActionDecl(ActionDef(Atom(p[3],[]),p[7])))
else:
  def p_top_action_symbol_optargs_optreturns_eq_action(p):
    'top : top ACTION SYMBOL optargs optreturns EQ LCB optaction RCB'
    p[0] = p[1]
    if not hasattr(p[8],'lineno'):
        p[8].lineno = get_lineno(p,7)
    p[0].declare(ActionDecl(ActionDef(Atom(p[3],[]),p[8],formals=p[4],returns=p[5])))

if not (iu.get_numeric_version() <= [1,1]):
    def p_top_mixin_callatom_before_callatom(p):
        'top : top MIXIN callatom BEFORE callatom'
        m = MixinBeforeDef(p[3],p[5])
        m.lineno = get_lineno(p,2)
        d = MixinDecl(m)
        d.lineno = get_lineno(p,2)
        p[0] = p[1]
        p[0].declare(d)
    def p_top_mixin_callatom_after_callatom(p):
        'top : top MIXIN callatom AFTER callatom'
        m = MixinAfterDef(p[3],p[5])
        m.lineno = get_lineno(p,2)
        d = MixinDecl(m)
        d.lineno = get_lineno(p,2)
        p[0] = p[1]
        p[0].declare(d)
    def p_top_isolate_callatom_eq_callatoms(p):
        'top : top ISOLATE callatom EQ callatoms'
        d = IsolateDecl(IsolateDef(*([p[3]] + p[5])))
        d.args[0].with_args = 0
        d.lineno = get_lineno(p,2)
        p[0] = p[1]
        p[0].declare(d)
    def p_top_isolate_callatom_eq_callatoms_with_callatoms(p):
        'top : top ISOLATE callatom EQ callatoms WITH callatoms'
        d = IsolateDecl(IsolateDef(*([p[3]] + p[5] + p[7])))
        d.args[0].with_args = len(p[7])
        d.lineno = get_lineno(p,2)
        p[0] = p[1]
        p[0].declare(d)
    def p_top_extract_callatom_eq_callatoms(p):
        'top : top EXTRACT callatom EQ callatoms'
        d = IsolateDecl(IsolateDef(*([p[3]] + p[5])))
        d.args[0].with_args = len(p[5])
        d.lineno = get_lineno(p,2)
        p[0] = p[1]
        p[0].declare(d)
    def p_top_export_callatom(p):
        'top : top EXPORT callatom'
        d = ExportDecl(ExportDef(p[3],Atom('')))
        d.lineno = get_lineno(p,2)
        p[0] = p[1]
        p[0].declare(d)
    def p_optdelegee(p):
        'optdelegee :'
        p[0] = None
    def p_optdelegee_callatom(p):
        'optdelegee : ARROW callatom'
        p[0] = p[2]
    def p_top_delegate_callatom_opt(p):
        'top : top DELEGATE callatoms optdelegee'
        if p[4] is not None:
            d = DelegateDecl(*[DelegateDef(s,p[4]) for s in p[3]])
        else:
            d = DelegateDecl(*[DelegateDef(s) for s in p[3]])
        d.lineno = get_lineno(p,2)
        p[0] = p[1]
        p[0].declare(d)

    # def p_top_delegate_callatom(p):
    #     'top : top DELEGATE callatoms ARROW callatom'
    #     d = DelegateDecl(*[DelegateDef(s,p[5]) for s in p[3]])
    #     d.lineno = get_lineno(p,2)
    #     p[0] = p[1]
    #     p[0].declare(d)

def p_top_state_symbol_eq_state_expr(p):
    'top : top STATE SYMBOL EQ state_expr'
    p[0] = p[1]
    p[0].declare(StateDecl(StateDef(p[3],p[5])))

def p_assert_rhs_lcb_requires_modifies_ensures_rcb(p):
    'assert_rhs : LCB requires modifies ensures RCB'
    p[0] = RME(p[2],p[3],p[4])

def p_assert_rhs_fmla(p):
    'assert_rhs : fmla'
    p[0] = p[1]

def p_top_assert_symbol_arrow_assert_rhs(p):
    'top : top ASSERT SYMBOL ARROW assert_rhs'
    p[0] = p[1]
    thing = Implies(Atom(p[3],[]),p[5])
    thing.lineno = get_lineno(p,4)
    p[0].declare(AssertDecl(thing))

def p_oper_symbol(p):
    'oper : SYMBOL'
    p[0] = p[1]

def p_oper_relop(p):
    'oper : relop'
    p[0] = p[1]

def p_oper_infix(p):
    'oper : infix'
    p[0] = p[1]

def p_top_interpret_symbol_arrow_symbol(p):
    'top : top INTERPRET oper ARROW oper'
    p[0] = p[1]
    thing = InterpretDecl(Implies(Atom(p[3],[]),Atom(p[5],[])))
    thing.lineno = get_lineno(p,4)
    p[0].declare(thing)
    
def p_top_interpret_symbol_arrow_lcb_symbol_dots_symbol_rcb(p):
    'top : top INTERPRET oper ARROW LCB SYMBOL DOTS SYMBOL RCB'
    p[0] = p[1]
    thing = InterpretDecl(Implies(Atom(p[3],[]),Range(p[6],p[8])))
    thing.lineno = get_lineno(p,4)
    p[0].declare(thing)

def p_loc(p):
    'loc : '
    p[0] = None

def p_loc_symbol(p):
    'loc : SYMBOL'
    p[0] = p[1]

def p_action_lcb_rcb(p):
    'action : LCB RCB'
    p[0] = Sequence()
    p[0].lineno = get_lineno(p,1)

def p_action_lcb_action_rcb(p):
    'action : LCB action RCB'
    p[0] = p[2]

def p_action_assume(p):
    'action : ASSUME fmla'
    p[0] = AssumeAction(p[2])
    p[0].lineno = get_lineno(p,1)

def p_action_assert(p):
    'action : ASSERT fmla'
    p[0] = AssertAction(p[2])
    p[0].lineno = get_lineno(p,1)

def p_action_ensures(p):
    'action : ENSURES fmla'
    p[0] = EnsuresAction(p[2])
    p[0].lineno = get_lineno(p,1)

def p_action_set_lit(p):
    'action : SET lit'
    p[0] = SetAction(p[2])
    p[0].lineno = get_lineno(p,1)

def p_termtuple_lp_term_comma_terms_rp(p):
    'termtuple : LPAREN term COMMA terms RPAREN'
    p[0] = Tuple(*([p[3]]+p[5]))
    p[0].lineno = get_lineno(p,1)
    
def p_action_term_assign_fmla(p):
    'action : term ASSIGN fmla'
    p[0] = AssignAction(p[1],p[3])
    p[0].lineno = get_lineno(p,2)

def p_termtuple_lp_term_comma_terms_rp(p):
    'termtuple : LPAREN term COMMA terms RPAREN'
    p[0] = Tuple(*([p[2]]+p[4]))
    p[0].lineno = get_lineno(p,1)

def p_action_termtuple_assign_fmla(p):
    'action : termtuple ASSIGN callatom'
    p[0] = CallAction(*([p[3]]+list(p[1].args)))
    p[0].lineno = get_lineno(p,2)

def p_action_term_assign_times(p):
    'action : term ASSIGN TIMES'
    p[0] = HavocAction(p[1])
    p[0].lineno = get_lineno(p,2)

def p_action_if_fmla_lcb_action_rcb(p):
    'action : IF fmla LCB action RCB'
    p[0] = IfAction(p[2],p[4])
    p[0].lineno = get_lineno(p,1)

def p_action_if_fmla_lcb_action_rcb_else_LCB_action_RCB(p):
    'action : IF fmla LCB action RCB ELSE action'
    p[0] = IfAction(p[2],p[4],p[7])
    p[0].lineno = get_lineno(p,1)

def p_action_if_times_lcb_action_rcb_else_LCB_action_RCB(p):
    'action : IF TIMES LCB action RCB ELSE action'
    p[0] = ChoiceAction(p[4],p[7])
    p[0].lineno = get_lineno(p,1)

if iu.get_numeric_version() <= [1,2]:
    def p_action_field_assign_term(p):
        'action : term DOT SYMBOL ASSIGN term'
        p[0] = AssignFieldAction(p[1],p[3],p[5])
        p[0].lineno = get_lineno(p,4)


    def p_action_field_assign_null(p):
        'action : term DOT SYMBOL ASSIGN NULL'
        p[0] = NullFieldAction(p[1],p[3])
        p[0].lineno = get_lineno(p,4)

    def p_action_field_assign_field(p):
        'action : term DOT SYMBOL ASSIGN term DOT SYMBOL'
        p[0] = CopyFieldAction(p[1],p[3],p[5],p[7])
        p[0].lineno = get_lineno(p,4)

    def p_action_field_assign_false(p):
        'action : term DOT SYMBOL ASSIGN FALSE'
        p[0] = NullFieldAction(p[1],p[3])
        p[0].lineno = get_lineno(p,4)

def p_action_instantiate_atom(p):
    'action : INSTANTIATE callatom'
#    p[0] = InstantiateAction(app_to_atom(p[2]))
    p[0] = InstantiateAction(p[2])
    p[0].lineno = get_lineno(p,1)

def p_callatom_atom(p):
    'callatom : atom'
    p[0] = p[1]

if iu.get_numeric_version() <= [1,2]:

    def p_callatom_callatom_colon_callatom(p):
        'callatom : callatom COLON callatom'
        p[0] = compose_atoms(p[1],p[3])
        p[0].lineno = get_lineno(p,1)

else:

    def p_callatom_callatom_dot_callatom(p):
        'callatom : callatom DOT callatom'
        p[0] = compose_atoms(p[1],p[3])
        p[0].lineno = get_lineno(p,1)


def p_callatoms_callatom(p):
    'callatoms : callatom'
    p[0] = [p[1]]

def p_callatoms_callatoms_callatom(p):
    'callatoms : callatoms COMMA callatom'
    p[0] = p[1]
    p[0].append(p[3])

# def p_action_call_optreturns_callatom(p):
#     'action : CALL optactualreturns callatom'
#     p[0] = CallAction(*([p[3]] + p[2]))
#     p[0].lineno = get_lineno(p,1)

def p_action_call_callatom(p):
    'action : CALL callatom'
    p[0] = CallAction(p[2])
    p[0].lineno = get_lineno(p,1)

def p_action_call_callatom_assign_callatom(p):
    'action : CALL callatom ASSIGN callatom'
    p[0] = CallAction(p[4],p[2])
    p[0].lineno = get_lineno(p,1)

def p_action_action_semi_action(p):
    'action : action SEMI action'
    if isinstance(p[1],Sequence):
        p[0] = p[1]
        p[0].args.append(p[3])
    else:
        p[0] = Sequence(p[1],p[3])
        p[0].lineno = p[1].lineno

def p_action_local_params_lcb_action_rcb(p):
    'action : LOCAL params LCB action RCB'
    # we rename the locals to avoid name capture
    lsyms = [s.prefix('loc:') for s in p[2]]
    subst = dict((x.rep,y.rep) for x,y in zip(p[2],lsyms))
    action = subst_prefix_atoms_ast(p[4],subst,None,None)
    p[0] = LocalAction(*(lsyms+[action]))
    p[0].lineno = get_lineno(p,1)

def p_eqn_SYMBOL_EQ_SYMBOL(p):
    'eqn : SYMBOL EQ SYMBOL'
    p[0] = Equals(App(p[1]),App(p[3]))

def p_eqns_eqn(p):
    'eqns : eqn'
    p[0] = [p[1]]

def p_eqns_eqns_comma_eqn(p):
    'eqns : eqns COMMA eqn'
    p[0] = p[1]
    p[0].append(p[3])

def p_action_let_eqns_lcb_action_rcb(p):
    'action : LET eqns LCB action RCB'
    p[0] = LetAction(*(p[2]+[p[4]]))

def p_symbols(p):
    'symbols : SYMBOL'
    p[0] = [p[1]]

def p_symbols_symbols_symbol(p):
    'symbols : symbols COMMA SYMBOL'
    p[0] = p[1]
    p[0].append(p[3])

def p_cdefns_cdefn(p):
    'cdefns : cdefn'
    p[0] = [p[1]]

def p_cdefns_cdefns_comma_cdefn(p):
    'cdefns : cdefns COMMA cdefn'
    p[0] = p[1]
    p[0].append(p[3])

def p_cdefn_atom_expr(p):
    'cdefn : atom EQ expr'
    p[0] = Definition(app_to_atom(p[1]),p[3])
    p[0].lineno = get_lineno(p,2)

def p_defns_defn(p):
    'defns : defn'
    p[0] = [p[1]]

def p_defns_defns_comma_defn(p):
    'defns : defns COMMA defn'
    p[0] = p[1]
    p[0].append(p[3])

def p_defn_atom_fmla(p):
    'defn : atom EQ fmla'
    p[0] = Definition(app_to_atom(p[1]),p[3])
    p[0].lineno = get_lineno(p,2)

def p_expr_fmla(p):
    'expr : LCB fmla RCB'
    p[0] = NamedSpace(Literal(1,p[2]))

def p_exprterm_aterm(p):
    'exprterm : aterm'
    p[0] = p[1]

def p_exprterm_var(p):
    'exprterm : var'
    p[0] = p[1]

def p_expr_exprterm(p):
    'expr : exprterm'
    p[0] = NamedSpace(Literal(1,app_to_atom(p[1])))

def p_expr_exprterm_relop_exprterm(p):
    'expr : exprterm relop exprterm'
    p[0] = NamedSpace(Literal(1,Atom(p[2],[p[1],p[3]])))
    p[0].lineno = get_lineno(p,2)

def p_expr_exprterm_tildaeq_exprterm(p):
    'expr : exprterm TILDAEQ exprterm'
    p[0] = NamedSpace(Literal(0,Atom('=',[p[1],p[3]])))
    p[0].lineno = get_lineno(p,2)

def p_expr_tilda_atom(p):
    'expr : TILDA expr'
    p[0] = NamedSpace(~p[2].lit)

# def p_expr_lit(p):
#     'expr : lit'
#     p[0] = NamedSpace(p[1])

def p_expr_lparen_expr_rparen(p):
    'expr : LPAREN expr RPAREN'
    p[0] = p[2]

def p_expr_prod(p):
    'expr : prod'
    p[0] = ProductSpace(p[1])
    
def p_expr_sum(p):
    'expr : sum'
    p[0] = SumSpace(p[1])
    
def p_prod_expr_expr(p):
    'prod : expr TIMES expr'
    p[0] = [p[1],p[3]]

def p_prod_prod_expr(p):
    'prod : prod TIMES expr'
    p[0] = p[1]
    p[0].append(p[3]) # is this side effect OK?

def p_sum_expr_expr(p):
    'sum : expr PLUS expr'
    p[0] = [p[1],p[3]]

def p_sum_sum_expr(p):
    'sum : sum PLUS expr'
    p[0] = p[1]
    p[0].append(p[3]) # is this side effect OK?

def p_state_expr_true(p):
    'state_expr : TRUE'
    p[0] = And()

def p_state_expr_false(p):
    'state_expr : FALSE'
    p[0] = OR()

def p_state_expr_symbol(p):
    'state_expr : SYMBOL'
    p[0] = Atom(p[1],[])

def p_state_expr_symbol_lparen_state_expr_rparen(p):
    'state_expr : SYMBOL LPAREN state_expr RPAREN'
    p[0] = Atom(p[1],[p[3]])

def p_state_expr_state_expr_or_state_expr(p):
    'state_expr : state_expr OR state_expr'
    if isinstance(p[1],Or):
        p[0] = p[1]
        p[0].args.append(p[3])
    else:
        p[0] = Or(p[1],p[3])

def p_state_expr_lcb_requires_modifies_ensures_rcb(p):
    'state_expr : LCB requires modifies ensures RCB'
    p[0] = RME(p[2],p[3],p[4])
    
def p_state_expr_entry(p):
    'state_expr : ENTRY'
    p[0] = RME(And(),[],And())

from ivy_logic_parser import *

def p_error(token):
    if token is not None:
        report_error(ParseError(token.lineno,token.value,"syntax error"))
    else:
        report_error(ParseError(None,None,'unexpected end of input'));

# Build the parsers
parser = yacc.yacc(start='top',tabmodule='ivy_parsetab',errorlog=yacc.NullLogger())
#parser = yacc.yacc(start='top',tabmodule='ivy_parsetab')
# formula_parser = yacc.yacc(start = 'fmla', tabmodule='ivy_formulatab')

def parse(s,nested=False):
    global error_list
    global stack
    if not nested:
        error_list = []
        stack = []
    vernum = iu.get_numeric_version()
    with LexerVersion(vernum):
        # shallow copy the parser and lexer to try for re-entrance (!!!)
        res = copy.copy(parser).parse(s,lexer=copy.copy(lexer))
    if error_list:
        raise iu.ErrorList(error_list)
    return res
    
def to_formula(s):
    return formula_parser.parse(s)

if __name__ == '__main__':
#    while True:
#       try:
#       s = raw_input('input > ')
#       except EOFError:
#           break
#       if not s: continue
       s = open('test.ivy','r').read()
       try:
           result = parse(s)
           print result
           print result.defined
       except iu.ErrorList as e:
           print repr(e)
#       print "enum: %s" % result.enumerate(dict(),lambda x:True)

def clauses_to_concept(name,clauses):
    vars =  used_variables_clauses(clauses)
    ps = [ProductSpace([NamedSpace(~lit) for lit in clause]) for clause in clauses]
    ss = ps[0] if len(ps) == 1 else SumSpace(ps)
    return (Atom(name,vars),ss)

    

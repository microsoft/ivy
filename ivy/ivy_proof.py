#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy_utils as iu
import ivy_logic as il
import ivy_logic_utils as lu
import ivy_ast as ia

class Redefinition(iu.IvyError):
    pass
class Circular(iu.IvyError):
    pass
class NoMatch(iu.IvyError):
    pass
class ProofError(iu.IvyError):
    pass

class MatchProblem(object):
    def __init__(self,pat,inst,freesyms,constants):
        self.pat,self.inst,self.freesyms,self.constants = pat,inst,set(freesyms),constants
    def __str__(self):
        return '{{pat:{},inst:{},freesyms:{}}}'.format(self.pat,self.inst,map(str,self.freesyms))

class ProofChecker(object):
    """ This is IVY's built-in proof checker """

    def __init__(self,axioms,definitions,schemata):
        """ A proof checker starts with sets of axioms, definitions and schemata
    
        - axioms is a list of ivy_ast.LabeledFormula
        - definitions is a list of ivy_ast.LabeledFormula
        - schemata is a map from string names to ivy_ast.SchemaBody
        """
    
        self.axioms  = list(axioms)
        self.definitions = dict((d.formula.defines(),d) for d in definitions)
        self.schemata = dict(schemata.iteritems())
        self.deps = set()  # set of dependencies of existing definitions

    def admit_definition(self,defn,proof=None):
        """ Admits a definition if it is non-recursive or match a definition schema. 
            If a proof is given it is used to match the definition to a schema, else
            default heuristic matching is used.
        
        - defn is an ivy_ast.LabeledFormula
        """

        sym = defn.formula.defines()
        if sym in self.definitions:
            raise Redefinition(defn,"redefinition of {}".format(sym))
        if sym in self.deps:
            raise Circular(defn,"symbol {} defined after reference".format(sym))
        deps = list(lu.symbols_ast(defn.formula.rhs()))
        self.deps.update(deps)
        if sym in deps:
            # Recursive definitions must match a schema
            if proof is None:
                raise NoMatch(defn,"no proof given for recursive definition")
            subgoals = self.match_schema(defn.formula,proof)
            if subgoals is None:
                raise NoMatch(defn,"recursive definition does not match the given schema")
        else:
            subgoals = []
        self.definitions[sym] = defn
        
    def admit_proposition(self,prop,proof=None):
        """ Admits a proposition with proof.  If a proof is given it
            is used to match the definition to a schema, else default
            heuristic matching is used.
        
        - prop is an ivy_ast.LabeledFormula
        """

        if proof is None:
            raise NoMatch(prop,"no proof given for property")
        subgoals = self.apply_proof([prop],proof)
        if subgoals is None:
            raise NoMatch(proof,"goal does not match the given schema")
        self.axioms.append(prop)
        return subgoals

    def apply_proof(self,decls,proof):
        """ Apply a proof to a list of goals, producing subgoals, or None if
        the proof fails. """

        if len(decls) == 0:
            return []
        if isinstance(proof,ia.SchemaInstantiation):
            return self.match_schema(decls[0].formula,proof) + decls[1:]
        elif isinstance(proof,ia.LetTactic):
            return self.let_tactic(decls,proof)
        elif isinstance(proof,ia.ComposeTactics):
            return self.compose_proofs(decls,proof.args)
        assert False,"unknown proof type {}".format(type(proof))

    def compose_proofs(self,decls,proofs):
        for proof in proofs:
            decls = self.apply_proof(decls,proof)
            if decls is None:
                return None
        return decls

    def let_tactic(self,decls,proof):
        return [ia.LabeledFormula(decls[0].label,
                                  il.Implies(il.And(proof.args),decls[0]))] + decls[1:]

    def match_schema(self,decl,proof):
        """ attempt to match a definition or property decl to a schema

        - decl is an ivy_ast.Definition or ivy_ast.Property
        - proof is an ivy_ast.SchemaInstantiation

        Returns a match or None
        """
        
        schemaname = proof.schemaname()
        if schemaname not in self.schemata:
            raise ProofError(proof,"No schema {} exists".format(schemaname))
        schema = self.schemata[schemaname]
        schema = transform_defn_schema(schema,decl)
        prob = match_problem(schema,decl)
        prob = transform_defn_match(prob)
        pmatch = compile_match(proof,prob,schemaname)
        prob.pat = apply_match_alt(pmatch,prob.pat)
        fomatch = fo_match(prob.pat,prob.inst,prob.freesyms,prob.constants)
        if fomatch is not None:
            prob.pat = apply_match(fomatch,prob.pat)
            prob.freesyms = apply_match_freesyms(fomatch,prob.freesyms)
        res = match(prob.pat,prob.inst,prob.freesyms,prob.constants)
#        show_match(res)
        if res is not None:
            subgoals = []
            for x in schema.prems():
                if isinstance(x,ia.LabeledFormula):
                    fmla = apply_match_alt(remove_vars_match(pmatch,x.formula),x.formula)
                    fmla = apply_match(remove_vars_match(fomatch,fmla),fmla)
                    fmla = apply_match(remove_vars_match(res,fmla),fmla)
                    g = ia.LabeledFormula(x.label,fmla)
                    g.lineno = x.lineno
                    subgoals.append(g)
            return subgoals
        return None

def remove_vars_match(mat,fmla):
    """ Remove the variables bindings from a match. This is used to
    prevent variable capture when applying the match to premises. Make sure free variables
    are not captured by fmla """
    res = dict((s,v) for s,v in mat.iteritems() if il.is_ui_sort(s))
    sympairs = [(s,v) for s,v in mat.iteritems() if il.is_constant(s)]
    symfmlas = il.rename_vars_no_clash([v for s,v in sympairs],[fmla])
    res.update((s,w) for (s,v),w in zip(sympairs,symfmlas))
#    show_match(res)
    return res


def show_match(m):
    if m is None:
        print 'no match'
        return 
    print 'match {'
    for x,y in m.iteritems():
        print '{} : {}'.format(x,y)
    print '}'
        
def match_problem(schema,decl):
    """ Creating a matching problem from a schema and a declaration """
    freesyms = set(x.args[0] for x in schema.prems() if isinstance(x,ia.ConstantDecl))
    freesyms.update(x for x in schema.prems() if isinstance(x,il.UninterpretedSort))
    freesyms.update(lu.variables_ast(schema.conc()))
    return MatchProblem(schema.conc(),decl,freesyms,set(lu.variables_ast(decl)))

def transform_defn_schema(schema,decl):
    """ Transform definition schema to match a definition. """
    conc = schema.conc()
    if not(isinstance(decl,il.Definition) and isinstance(conc,il.Definition)):
        return schema
    declargs = decl.lhs().args
    concargs = conc.lhs().args
    if len(declargs) > len(concargs):
        schema = parameterize_schema([x.sort for x in declargs[:len(declargs)-len(concargs)]],schema)
    return schema

def transform_defn_match(prob):
    """ Transform a problem of matching definitions to a problem of
    matching the right-hand sides. Requires prob.inst is a definition. """

    conc,decl,freesyms = prob.pat,prob.inst,prob.freesyms
    if not(isinstance(decl,il.Definition) and isinstance(conc,il.Definition)):
        return prob
    declsym = decl.defines()
    concsym = conc.defines()
    # dmatch = match(conc.lhs(),decl.lhs(),freesyms)
    # if dmatch is None:
    #     print "left-hand sides didn't match: {}, {}".format(conc.lhs(),decl.lhs())
    #     return None
    declargs = decl.lhs().args
    concargs = conc.lhs().args
    if len(declargs) < len(concargs):
        return None
    declrhs = decl.rhs()
    concrhs = conc.rhs()
    vmap = dict((x.name,y.resort(x.sort)) for x,y in zip(concargs,declargs))
    concrhs = lu.substitute_ast(concrhs,vmap)
    dmatch = {concsym:declsym}
    for x,y in zip(func_sorts(concsym),func_sorts(declsym)):
        if x in freesyms:
            if x in dmatch and dmatch[x] != y:
                print "lhs sorts didn't match: {}, {}".format(x,y)
                return None
            dmatch[x] = y
        else:
            if x != y:
                print "lhs sorts didn't match: {}, {}".format(x,y)
                return None
    concrhs = apply_match(dmatch,concrhs)
    freesyms = apply_match_freesyms(dmatch,freesyms)
    freesyms = [x for x in freesyms if x not in concargs]
    constants = set(x for x in prob.constants if x not in declargs)
    return MatchProblem(concrhs,declrhs,freesyms,constants)


def parameterize_schema(sorts,schema):
    """ Add initial parameters to all the free symbols in a schema.

    Takes a list of sorts and an ivy_ast.SchemaBody. """

    vars = make_distinct_vars(sorts,schema.conc())
    match = {}
    prems = []
    for prem in schema.prems():
        if isinstance(prem,ia.ConstantDecl):
            sym = prem.args[0]
            vs2 = [il.Variable('X'+str(i),y) for i,y in enumerate(sym.sort.dom)]
            sym2 = sym.resort(il.FuncConstSort(*(sorts + list(sym.sort.dom) + [sym.sort.rng])))
            match[sym] = il.Lambda(vs2,sym2(*(vars+vs2)))
            prems.append(ia.ConstantDecl(sym2))
        else:
            prems.append(prem)
    conc = apply_match(match,schema.conc())
    return schema.clone(prems + [conc])

# A "match" is a map from symbols to lambda terms
    
def compile_match(proof,prob,schemaname):
    """ Compiles match in a proof. Only the symbols in
    freesyms may be used in the match."""

    match = proof.match()
    freesyms = prob.freesyms
    res = dict()
    for m in proof.match():
        if il.is_app(m.lhs()):
            res[m.defines()] = il.Lambda(m.lhs().args,m.rhs())
        else:
            res[m.lhs()] = m.rhs()
    # iu.dbg('freesyms')
    # freesyms = apply_match_freesyms(res,freesyms)
    # iu.dbg('freesyms')
    # for sym in res:
    #     if sym not in freesyms:
    #         raise ProofError(proof,'{} is not a premise of schema {}'.format(repr(sym),schemaname))
    return res

def apply_match(match,fmla):
    """ apply a match to a formula. 

    In effect, substitute all symbols in the match with the
    corresponding lambda terms and apply beta reduction
    """

    args = [apply_match(match,f) for f in fmla.args]
    if il.is_app(fmla):
        if fmla.rep in match:
            func = match[fmla.rep]
            return func(*args)
        return apply_match_func(match,fmla.rep)(*args)
    if il.is_variable(fmla) and fmla in match:
        return match[fmla]
    return fmla.clone(args)

def apply_match_alt(match,fmla):
    """ apply a match to a formula. 

    In effect, substitute all symbols in the match with the
    corresponding lambda terms and apply beta reduction
    """

    args = [apply_match_alt(match,f) for f in fmla.args]
    if il.is_app(fmla):
        func = apply_match_func(match,fmla.rep)
        if func in match:
            func = match[func]
            return func(*args)
        return func(*args)
    if il.is_variable(fmla):
        fmla = il.Variable(fmla.name,match.get(fmla.sort,fmla.sort))
        fmla = match.get(fmla,fmla)
        return fmla
    return fmla.clone(args)

def apply_match_func(match,func):
    sorts = func_sorts(func)
    sorts = [match.get(s,s) for s in sorts]
    return il.Symbol(func.name,sorts[0] if len(sorts) == 1 else il.FunctionSort(*sorts))

def apply_match_sym(match,sym):
    if il.is_variable(sym):
        return il.Variable(sym.name,match.get(sym.sort,sym.sort))
    return match.get(sym,sym) if isinstance(sym,il.UninterpretedSort) else apply_match_func(match,sym)

def apply_match_freesyms(match,freesyms):
    return set(apply_match_sym(match,sym) for sym in freesyms if sym not in match)

def apply_match_freesyms_alt(match,freesyms):
    msyms = [apply_match_sym(match,sym) for sym in freesyms]
    return [sym for sym in msyms if sym not in match]

def func_sorts(func):
    return list(func.sort.dom) + [func.sort.rng]

def term_sorts(term):
    """ Returns a list of the domain and range sorts of the head function of a term, if any """
    return func_sorts(term.rep) if il.is_app(term) else []

def funcs_match(pat,inst,freesyms):
    psorts,isorts = map(func_sorts,(pat,inst))
    return (pat.name == inst.name and len(psorts) == len(isorts)
            and all(x == y for x,y in zip(psorts,isorts) if x not in freesyms))

def heads_match(pat,inst,freesyms):
    """Returns true if the heads of two terms match. This means they have
    the same top-level operator and same number of
    arguments. Quantifiers do not match anything. A function symbol matches
    if it has the same name and if it agrees on the non-free sorts in
    its type.
    """
    return (il.is_app(pat) and il.is_app(inst) and funcs_match(pat.rep,inst.rep,freesyms)
        or not il.is_app(pat) and not il.is_quantifier(pat)
           and type(pat) is type(inst) and len(pat.args) == len(inst.args))
    
def make_distinct_vars(sorts,*asts):
    vars = [il.Variable('V'+str(i),sort) for i,sort in enumerate(sorts)]
    return lu.rename_variables_distinct_asts(vars,asts)
    

def extract_terms(inst,terms):
    """ Returns a lambda term t such that t(terms) = inst and
    terms do not occur in t. vars is a list of distinct variables
    of same types as terms that are not free in inst. """

    vars = make_distinct_vars([t.sort for t in terms], inst)
    def rec(inst):
        for term,var in zip(terms,vars):
            if term == inst:
                return var
        return inst.clone(map(rec,inst.args))
    return il.Lambda(vars,rec(inst))

def fo_match(pat,inst,freesyms,constants):
    """ Compute a partial first-order match. Matches free FO variables to ground terms,
    but ignores variable occurrences under free second-order symbols. """

    if il.is_variable(pat):
        if pat in freesyms and all(x in constants for x in lu.variables_ast(inst)):
            res = {pat:inst}
            if pat.sort == inst.sort:
                return res
            if pat.sort in freesyms:
                res[pat.sort] = inst.sort
                return res
    if il.is_quantifier(pat) and il.is_quantifier(inst):
        with RemoveSymbols(freesyms,pat.variables):
            return fo_match(pat.body,inst.body,freesyms,constants)
    if heads_match(pat,inst,freesyms):
        matches = [fo_match(x,y,freesyms,constants) for x,y in zip(pat.args,inst.args)]
        res =  merge_matches(*matches)
        return res
    return dict()
    
            

def match(pat,inst,freesyms,constants):
    """ Match an instance to a pattern.

    A match is an assignment sigma to freesyms such
    that sigma pat =_alpha inst.

    """

    if il.is_quantifier(pat):
        return match_quants(pat,inst,freesyms,constants)
    if heads_match(pat,inst,freesyms):
        matches = [match(x,y,freesyms,constants) for x,y in zip(pat.args,inst.args)]
        matches.extend([match_sort(x,y,freesyms) for x,y in zip(term_sorts(pat),term_sorts(inst))])
        return merge_matches(*matches)
    if il.is_app(pat) and pat.rep in freesyms:
        B = extract_terms(inst,pat.args)
        if all(v in constants for v in lu.variables_ast(B)):
            return {pat.rep:B}


def match_quants(pat,inst,freesyms,constants):
    """ Match an instance to a pattern that is a quantifier.
    """

    if type(pat) is not type(inst) or len(pat.variables) != len(inst.variables):
        return None
    with AddSymbols(freesyms,pat.variables):
        matches = [match(x,y,freesyms,constants) for x,y in zip(pat.variables,inst.variables)]
        matches.append(match(pat.body,inst.body,freesyms,constants))
        mat = merge_matches(*matches)
        if mat is not None:
            for x in pat.variables:
                if x in mat:
                    del mat[x]
        return mat


def match_sort(pat,inst,freesyms):
    if pat in freesyms:
        return {pat:inst}
    return dict() if pat == inst else None

def merge_matches(*matches):
    if len(matches) == 0:
        return dict()
    if any(match is None for match in matches):
        return None
    res = dict(matches[0].iteritems())
    for match2 in matches[1:]:
        for sym,lmda in match2.iteritems():
            if sym in res:
                if not equiv_alpha(lmda,res[sym]):
                    return None
            else:
                res[sym] = lmda
    return res

def equiv_alpha(x,y):
    """check if two closed terms are equivalent module alpha
    conversion. for now, we assume the terms are closed
    """
    if x == y:
        return True
    if il.is_lambda(x) and il.is_lambda(y):
        return x.body == il.substitute(y.body,zip(x.variables,y.variables))
    return False
    pass

class AddSymbols(object):
    """ temporarily add some symbols to a set of symbols """
    def __init__(self,symset,symlist):
        self.symset,self.symlist = symset,list(symlist)
    def __enter__(self):
        global sig
        self.saved = []
        for sym in self.symlist:
            if sym in self.symset:
                self.saved.append(sym)
                self.remove(sym)
            self.symset.add(sym)
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global sig
        for sym in self.symlist:
            self.symset.remove(sym)
        for sym in self.saved:
            self.symset.add(sym)
        return False # don't block any exceptions

class RemoveSymbols(object):
    """ temporarily add some symbols to a set of symbols """
    def __init__(self,symset,symlist):
        self.symset,self.symlist = symset,list(symlist)
    def __enter__(self):
        global sig
        self.saved = []
        for sym in self.symlist:
            if sym in self.symset:
                self.saved.append(sym)
                self.remove(sym)
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global sig
        for sym in self.saved:
            self.symset.add(sym)
        return False # don't block any exceptions

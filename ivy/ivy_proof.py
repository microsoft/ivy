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
            if self.match_schema(defn.formula,proof) is None:
                raise NoMatch(defn,"recursive definition does not match the given schema")
        self.definitions[sym] = defn
        
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
        conc = schema.conc()
        if type(conc) is not type(decl):
            iu.dbg('type(conc)')
            iu.dbg('type(decl)')
            return None
        freesyms = set(x.args[0] for x in schema.prems() if isinstance(x,ia.ConstantDecl))
        freesyms.update(x for x in schema.prems() if isinstance(x,il.UninterpretedSort))
        if isinstance(decl,il.Definition):
            declsym = decl.defines()
            concsym = conc.defines()
            declargs = decl.lhs().args
            concargs = conc.lhs().args
            if len(declargs) != len(concargs):
                return None
            declrhs = decl.rhs()
            concrhs = conc.rhs()
            vmap = dict((x.name,il.Variable(y.name,x.sort)) for x,y in zip(concargs,declargs))
            concrhs = lu.substitute_ast(concrhs,vmap)
            dmatch = {concsym:declsym}
            for x,y in zip(func_sorts(concsym),func_sorts(declsym)):
                if x in freesyms:
                    if x in dmatch and dmatch[x] != y:
                        print "lhs sorts didn't match"
                        return None
                    dmatch[x] = y
                else:
                    if x != y:
                        print "lhs sorts didn't match"
                        return None
            concrhs = apply_match(dmatch,concrhs)
            iu.dbg('concrhs')
            inst = declrhs
            pat = concrhs
        else:
            raise ProofError(proof,"Property schemata not supported yet")
        pmatch = compile_match(proof,freesyms,schemaname)
        iu.dbg('pmatch')
        pat = apply_match(pmatch,pat)
        iu.dbg('pat')
        iu.dbg('freesyms')
        res = match(pat,inst,freesyms)
        iu.dbg('res')
        res = merge_matches(res,pmatch)
        print res
        return res
        

# A "match" is a map from symbols to lambda terms
    
def compile_match(proof,freesyms,schemaname):
    """ Compiles match in a proof. Only the symbols in
    freesyms may be used in the match."""

    match = proof.match
    res = dict()
    for m in proof.match():
        sym = m.defines()
        if sym not in freesyms:
            raise ProofError(proof,'{} is not a premise of schema {}'.format(sym))
        res[sym] = il.Lambda(m.lhs().args,m.rhs())
    return res

def apply_match(match,fmla):
    """ apply a match to a formula. 

    In effect, substitute all symbols in the match with the
    corresponding lambda terms and apply beta reduction
    """

    args = [apply_match(match,f) for f in fmla.args]
    if il.is_app(fmla):
        if fmla.rep in match:
            return match[fmla.rep](*args)
        sorts = func_sorts(fmla.rep)
        sorts = [match.get(s,s) for s in sorts]
        func = il.Symbol(fmla.rep.name,sorts[0] if len(sorts) == 1 else il.FunctionSort(*sorts))
        return func(*args)
    return fmla.clone(args)

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
    
def extract_terms(inst,terms):
    """ Returns a lambda term t such that t(terms) = inst and
    terms do not occur in t. vars is a list of distinct variables
    of same types as terms that are not free in inst. """

    vars = [il.Variable('V'+str(i),t.sort) for i,t in enumerate(terms)]
    vars = lu.rename_variables_distinct_ast(vars,inst)
    def rec(inst):
        for term,var in zip(terms,vars):
            if term == inst:
                return var
        return inst.clone(map(rec,inst.args))
    return il.Lambda(vars,rec(inst))

def match(pat,inst,freesyms):
    """ Match an instance to a pattern.

    A match is an assignment sigma to freesyms such
    that sigma pat =_alpha inst.

    """

    iu.dbg('pat')
    iu.dbg('inst')
    if heads_match(pat,inst,freesyms):
        matches = [match(x,y,freesyms) for x,y in zip(pat.args,inst.args)]
        matches.extend([match_sort(x,y,freesyms) for x,y in zip(term_sorts(pat),term_sorts(inst))])
        return merge_matches(*matches)
    if il.is_app(pat) and pat.rep in freesyms:
        B = extract_terms(inst,pat.args)
        iu.dbg('B')
        if lu.is_ground_ast(B):
            return {pat.rep:B}

def match_sort(pat,inst,freesyms):
    if pat in freesyms:
        return {pat:inst}
    return dict() if pat == inst else None

def merge_matches(*matches):
    if len(matches) == 0:
        return dict()
    if any(match is None for match in matches):
        return None
    iu.dbg('matches[0]')
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
    return false
    pass

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
        if isinstance(decl,il.Definition):
            declsym = decl.defines()
            concsym = conc.defines()
            declargs = decl.lhs().args
            concargs = conc.lhs().args
            if len(declargs) != len(concargs):
                return None
            declrhs = decl.rhs()
            concrhs = conc.rhs()
            vmap = dict((x.name,y) for x,y in zip(concargs,declargs))
            concrhs = lu.substitute_ast(concrhs,vmap)
            concrhs = lu.rename_ast(concrhs,{concsym:declsym})
            inst = declrhs
            pat = concrhs
        else:
            raise ProofError(proof,"Property schemata not supported yet")
        pmatch = compile_match(proof.match())
        iu.dbg('pmatch')
        pat = apply_match(pmatch,pat)
        iu.dbg('pat')
        res = match(pat,inst)
        res = merge_matches(res,pmatch)
        print res
        return res
        

# A "match" is a map from symbols to lambda terms
    
def compile_match(match):
    """ compiles a list of definitions to a match """
    res = dict()
    for m in match:
        res[m.defines()] = il.Lambda(m.lhs().args,m.rhs())
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
    return fmla.clone(args)

def match(pat,inst):
    """ match an instance to a pattern. for now, pat matches
    inst iff pat == inst  """

    return dict() if pat == inst else None

def merge_matches(match1,match2):
    if match1 is None or match2 is None:
        return None
    res = dict(match1.iteritems())
    for sym,lmda in match2.iteritems():
        if sym in res:
            if not lambda_equiv(lmda,res[sym]):
                return None
        else:
            res[sym] = lmda
    return res

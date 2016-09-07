#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy_utils as iu
import ivy_logic as il
import ivy_logic_utils as lu
import ivy_solver

from collections import defaultdict
import string
import functools

################################################################################
#
# This Context object contains all the definitions in the current Ivy module
#
################################################################################

class Module(object):

    def __init__(self):
        self.clear()

    def clear(self):

        # these fields represent all the module declarations

        self.all_relations = [] # this includes both base and derived relations in declaration order
        self.definitions = []  # TODO: these are actually "derived" relations
        self.labeled_axioms = []
        self.labeled_props = []
        self.labeled_inits = []
        self.init_cond = lu.true_clauses()
        self.relations = dict()  # TODO: this is redundant, remove
        self.functions = dict()  # TODO: this is redundant, remove
        self.updates = []
        self.schemata = dict()
        self.instantiations = []
        self.concept_spaces = []
        self.labeled_conjs = []  # conjectures
        self.hierarchy = defaultdict(set)
        self.actions = {}
        self.predicates = {}
        self.assertions = []
        self.mixins = defaultdict(list)
        self.public_actions = set()
        self.isolates = {}
        self.exports = []
        self.imports = []
        self.delegates = []
        self.public_actions = set() # hash of the exported actions
        self.progress = []  # list of progress properties
        self.rely = [] # list of rely relations
        self.mixord = [] # list of mixin order relations
        self.destructor_sorts = {}
        self.sort_destructors = defaultdict(list)
        self.privates = set() # set of string (names of private actions)
        self.interps = defaultdict(list) # maps type names to lists of labeled interpretions
        self.natives = [] # list of NativeDef
        self.initializers = [] # list of name,action pairs
        self.params = []
        self.ghost_sorts = set() # set of sort names
        self.native_types = {} # map from sort names to ivy_ast.NativeType
        self.sort_order = [] # list of sorts names in order declared
        self.symbol_order = [] # list of symbols in order declared
        self.aliases = {} # map from name to name

        self.sig = il.sig.copy() # capture the current signature

    def __enter__(self):
        global module
        self.old_module = module
        self.old_sig = il.sig
        module = self
        il.sig = self.sig
        ivy_solver.clear()   # this clears cached values, needed when changing sig
        return self

    def __exit__(self,exc_type, exc_val, exc_tb):
        global module
        module = self.old_module
        il.sig = self.old_sig
        return False # don't block any exceptions

    def get_axioms(self):
        res = self.axioms
        for n,sch in self.schemata.iteritems():
            res += sch.instances
        return res

    def background_theory(self, symbols=None):
        if hasattr(self,"theory"):
            return self.theory
        return lu.Clauses([])

    def add_to_hierarchy(self,name):
        if iu.ivy_compose_character in name:
            pref,suff = string.rsplit(name,iu.ivy_compose_character,1)
            self.add_to_hierarchy(pref)
            self.hierarchy[pref].add(suff)

    def add_object(self,name):
        self.hierarchy[name]

    @property
    def axioms(self):
        return map(drop_label,self.labeled_axioms)

    @property
    def conjs(self):
        # This returns the list of conjectures as Clauses, without labels
        res = []
        for c in self.labeled_conjs:
            fmla = c.formula
            clauses = lu.formula_to_clauses(fmla)
            clauses.lineno = c.lineno
            res.append(clauses)
        return res

    def update_theory(self):
        theory = list(self.get_axioms())
        # axioms of the derived relations TODO: used only the
        # referenced ones, but we need to know abstract domain for
        # this
        for ldf in self.definitions:
            cnst = ldf.formula.to_constraint()
            if all(isinstance(p,il.Variable) for p in ldf.formula.args[0].args):
                theory.append(cnst) # TODO: make this a def?
        # extensionality axioms for structs
        for sort in sorted(self.sort_destructors):
            destrs = self.sort_destructors[sort]
            if any(d.name in self.sig.symbols for d in destrs):
                ea = il.extensionality(destrs)
                if il.is_epr(ea):
                    theory.append(ea)
        self.theory = lu.Clauses(theory)
        


    def theory_context(self):
        """ Set up to instiate the non-epr axioms """
        """ Return a set of clauses which represent the background theory
        restricted to the given symbols (should be like the result of used_symbols).
        """
        self.update_theory()

        non_epr = {}
        for ldf in self.definitions:
            cnst = ldf.formula.to_constraint()
            if not all(isinstance(p,il.Variable) for p in ldf.formula.args[0].args):
                non_epr[ldf.formula.defines()] = (ldf,cnst)
        return ModuleTheoryContext(functools.partial(instantiate_non_epr,non_epr))
        

    # This makes a semi-shallow copy so we can side-effect 

    def copy(self):
        m = Module()
        from copy import copy
        for x,y in self.__dict__.iteritems():
            if x is 'sig':
                m.__dict__[x] = y.copy()
            else:
                m.__dict__[x] = copy(y)
        return m

module = None

def instantiate_non_epr(non_epr,ground_terms):
    theory = []
    if ground_terms != None:
        matched = set()
        for term in ground_terms:
            if term.rep in non_epr and term not in matched:
                ldf,cnst = non_epr[term.rep]
                subst = dict((v,t) for v,t in zip(ldf.formula.args[0].args,term.args)
                             if not isinstance(v,il.Variable))
                inst = lu.substitute_constants_ast(cnst,subst)
                theory.append(inst)
#                iu.dbg('inst')
                matched.add(term)
    return lu.Clauses(theory)


def background_theory(symbols = None):
    return module.background_theory(symbols)

def find_action(name):
    return module.actions.get(name,None)

param_logic = iu.Parameter("complete",','.join(il.logics),
                           check=lambda ls: all(s in il.logics for s in ls.split(',')))

def logics():
    return param_logic.get().split(',')

def drop_label(labeled_fmla):
    return labeled_fmla.formula if hasattr(labeled_fmla,'formula') else labeled_fmla

class ModuleTheoryContext(object):

    def __init__(self,instantiator):
        self.instantiator = instantiator

    def __enter__(self):
        self.old_instantiator = lu.instantiator
        lu.instantiator = self.instantiator
        return self

    def __exit__(self,exc_type, exc_val, exc_tb):
        lu.instantiator = self.old_instantiator
        return False # don't block any exceptions

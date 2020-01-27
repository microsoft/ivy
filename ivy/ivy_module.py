#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy_utils as iu
import ivy_logic as il
import ivy_logic_utils as lu
import ivy_solver
import ivy_concept_space as ics
import ivy_ast

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
        self.theorems = dict()
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
        self.constructor_sorts = {}
        self.sort_constructors = defaultdict(list)
        self.privates = set() # set of string (names of private actions)
        self.interps = defaultdict(list) # maps type names to lists of labeled interpretions
        self.natives = [] # list of NativeDef
        self.native_definitions = [] # list of definitions whose rhs is NativeExpr
        self.initializers = [] # list of name,action pairs
        self.params = [] # list of symbol
        self.param_defaults = [] # list of string or None
        self.ghost_sorts = set() # set of sort names
        self.native_types = {} # map from sort names to ivy_ast.NativeType
        self.sort_order = [] # list of sorts names in order declared
        self.symbol_order = [] # list of symbols in order declared
        self.aliases = {} # map from name to name
        self.before_export = {} # map from string to action
        self.attributes = {} # map from name to atom
        self.variants = defaultdict(list) # map from sort name to list of sort
        self.supertypes = defaultdict(list) # map from sort name to sort
        self.ext_preconds = {} # map from action name to formula
        self.proofs = [] # list of pair (labeled formula, proof)
        self.named = [] # list of pair (labeled formula, atom)
        self.subgoals = [] # (labeled formula * labeled formula list) list
        self.isolate_info = None # IsolateInfo or None
        self.conj_actions = dict() # map from conj names to action name list
        self.conj_subgoals = None # None or labeled formula list
        self.assumed_invariants = [] # labeled_formula_list
        self.finite_sorts = set() # set of sort names
        
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
            res += sch.formula.instances
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
        else:
            self.hierarchy['this'].add(name)

    def add_object(self,name):
        assert not isinstance(name,ivy_ast.This)
        self.hierarchy[name]

    @property
    def axioms(self):
        return [drop_label(x) for x in self.labeled_axioms if not x.temporal]

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
                if not isinstance(ldf.formula,il.DefinitionSchema):
#                    theory.append(ldf.formula) # TODO: make this a def?
                    ax = ldf.formula
                    ax = ax.to_constraint() if isinstance(ax.rhs(),il.Some) else ax
                    if ldf.formula.args[0].args:
                        ax = il.ForAll(ldf.formula.args[0].args,ax)
                    theory.append(ax) # TODO: make this a def?
        # extensionality axioms for structs
        for sort in sorted(self.sort_destructors):
            destrs = self.sort_destructors[sort]
            if any(d.name in self.sig.symbols for d in destrs):
                ea = il.extensionality(destrs)
                if il.is_epr(ea):
                    theory.append(ea)
        # exclusivity axioms for variants
        theory.extend(self.variant_axioms())
        self.theory = lu.Clauses(theory)

    def variant_axioms(self):
        theory = []
        for sort in sorted(self.variants):
            sort_variants = self.variants[sort]
            if any(v.name in self.sig.sorts for v in sort_variants) and sort in self.sig.sorts:
                ea = il.exclusivity(self.sig.sorts[sort],sort_variants)
                theory.append(ea) # these are always in EPR
        return theory


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
        

    def is_variant(self,lsort,rsort):
        """ true if rsort is a variant of lsort """
        return (all(isinstance(a,il.UninterpretedSort) for a in (lsort,rsort))
                and lsort.name in self.variants and rsort in self.variants[lsort.name])

    def variant_index(self,lsort,rsort):
        """ returns the index of variant rsort of lsort """
        for idx,sort in enumerate(self.variants[lsort.name]):
            if sort == rsort:
                return idx

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

    # This removes implemented types

    def canonize_types(self):
        global sort_refinement
        with self.sig:
            sort_refinement = il.sort_refinement()
            if len(list(sort_refinement)) == 0:
                return # save time if nothing to do
            self.definitions = resort_labeled_asts(self.definitions)
            self.labeled_axioms = resort_labeled_asts(self.labeled_axioms)
            self.labeled_props = resort_labeled_asts(self.labeled_props)
            self.labeled_inits = resort_labeled_asts(self.labeled_inits)
            self.init_cond = resort_clauses(self.init_cond)
            self.concept_spaces = resort_concept_spaces(self.concept_spaces)
            self.labeled_conjs = resort_labeled_asts(self.labeled_conjs)
            self.assertions = resort_labeled_asts(self.assertions)
            self.progress = resort_asts(self.progress)
            self.initializers = resort_name_ast_pairs(self.initializers)
            self.params = resort_symbols(self.params)
            self.ghost_sorts = remove_refined_sortnames_from_set(self.ghost_sorts)
            self.sort_order = remove_refined_sortnames_from_list(self.sort_order)
            self.symbol_order = resort_symbols(self.symbol_order)
            self.aliases = resort_aliases_map(self.aliases)
            self.before_export = resort_map_any_ast(self.before_export)
            self.ext_preconds = resort_map_any_ast(self.ext_preconds)
            lu.resort_sig(sort_refinement)

            
        # Make concept spaces from the conjecture

    def update_conjs(self):
        mod = self
        for i,cax in enumerate(mod.labeled_conjs):
            fmla = cax.formula
            csname = 'conjecture:'+ str(i)
            variables = list(lu.used_variables_ast(fmla))
            sort = il.RelationSort([v.sort for v in variables])
            sym = il.Symbol(csname,sort)
            space = ics.NamedSpace(il.Literal(0,fmla))
            mod.concept_spaces.append((sym(*variables),space))

    def call_graph(self):
        callgraph = defaultdict(list)
        for actname,action in self.actions.iteritems():
            for called_name in action.iter_calls():
                callgraph[called_name].append(actname)
        return callgraph

def resort_ast(ast):
    return lu.resort_ast(ast,sort_refinement)

def resort_clauses(clauses):
    return lu.resort_clauses(clauses,sort_refinement)

def resort_asts(asts):
    return [lu.resort_ast(ast,sort_refinement) for ast in asts]

def resort_labeled_asts(asts):
    return [ast.clone([ast.args[0],lu.resort_ast(ast.args[1],sort_refinement)]) for ast in asts]

resort_concept_spaces = resort_asts

def resort_map_symbol_sort(m):
    return dict((lu.resort_symbol(sym,sort_refinement),lu.resort_sort(sort,sort_refinement))
                for sym,sort in m.iteritems())

def resort_name_ast_pairs(pairs):
    return [(n,lu.resort_ast(a,sort_refinement)) for n,a in pairs]

def resort_symbols(symbols):
    return [lu.resort_symbol(symbol,sort_refinement) for symbol in symbols]

def remove_refined_sortnames_from_set(sorts):
    refd = set(s.name for s in sort_refinement)
    return set(n for n in sorts if n not in refd)

def remove_refined_sortnames_from_list(sorts):
    refd = set(s.name for s in sort_refinement)
    return list(n for n in sorts if n not in refd)

def resort_aliases_map(amap):
    res = dict(amap.iteritems())
    for s1,s2 in sort_refinement.iteritems():
        res[s1.name] = s2.name

def resort_map_any_ast(m):
    return dict((a,lu.resort_ast(b,sort_refinement)) for a,b in m.iteritems())


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
                if all(lu.is_ground_ast(x) for x in subst.values()):
                       inst = lu.substitute_constants_ast(cnst,subst)
                       theory.append(inst)
#                iu.dbg('inst')
                matched.add(term)
    return lu.Clauses(theory)


def background_theory(symbols = None):
    return module.background_theory(symbols)

def find_action(name):
    return module.actions.get(name,None)

param_logic = iu.Parameter("complete",','.join(il.default_logics),
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

def relevant_definitions(symbols):
    dfn_map = dict((ldf.formula.defines(),ldf.formula.args[1]) for ldf in module.definitions)
    rch = set(iu.reachable(symbols,lambda sym: lu.symbols_ast(dfn_map[sym]) if sym in dfn_map else []))
    return [ldf for ldf in module.definitions if ldf.formula.defines() in rch]
    
def sort_dependencies(mod,sortname,with_variants=True):
    if sortname in mod.sort_destructors:
        return [s.name for destr in mod.sort_destructors[sortname]
                for s in destr.sort.dom[1:] + (destr.sort.rng,)]
    if sortname in mod.native_types:
        t = mod.native_types[sortname]
        if isinstance(t,ivy_ast.NativeType):
            return [s.rep for s in t.args[1:] if s.rep in mod.sig.sorts]
    if with_variants and sortname in mod.variants:
        return [s.name for s in mod.variants[sortname]]
    return []

# Holds info about isolate for user consumption
#
# -- implementations is a list of pairs (mixer,mixee,action) for present action implementaitons
# -- monitors is a list of triples (mixer,mixee,action) for present monitors

class IsolateInfo(object):
    def __init__(self):
        self.implementations,self.monitors = [],[]

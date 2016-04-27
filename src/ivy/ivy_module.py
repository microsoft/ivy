#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy_utils as iu
import ivy_logic as il
import ivy_logic_utils as lu
import ivy_solver

from collections import defaultdict
import string

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
        self.concepts = []  # TODO: these are actually "derived" relations
        self.labeled_axioms = []
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
        self.delegates = []
        self.public_actions = set() # hash of the exported actions
        self.progress = []  # list of progress properties
        self.rely = [] # list of rely relations
        self.mixord = [] # list of mixin order relations

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
        """ Return a set of clauses which represent the background theory
        restricted to the given symbols (should be like the result of used_symbols).
        """
        theory = list(self.get_axioms())
        # axioms of the derived relations TODO: used only the
        # referenced ones, but we need to know abstract domain for
        # this
        for df in self.concepts:
            theory.append(df.to_constraint()) # TODO: make this a def?
        return lu.Clauses(theory)


    def add_to_hierarchy(self,name):
        if iu.ivy_compose_character in name:
            pref,suff = string.rsplit(name,iu.ivy_compose_character,1)
            self.add_to_hierarchy(pref)
            self.hierarchy[pref].add(suff)

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


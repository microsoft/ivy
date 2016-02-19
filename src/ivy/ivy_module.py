#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy_utils as iu
import ivy_logic as il
import ivy_logic_utils as lu

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
        self.axioms = []
        self.init_cond = lu.true_clauses()
        self.relations = dict()  # TODO: this is redundant, remove
        self.functions = dict()  # TODO: this is redundant, remove
        self.updates = []
        self.schemata = dict()
        self.instantiations = []
        self.concept_spaces = []
        self.conjs = []  # conjectures
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

        self.sig = il.sig # capture the current signature

    def __enter__(self):
        global module
        self.old_module = module
        self.old_sig = il.sig
        module = self
        
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



module = None

def background_theory(symbols = None):
    return module.background_theory(symbols)

def find_action(name):
    return module.actions.get(name,None)

param_logic = iu.Parameter("complete","epr",check=lambda s: (s in il.logics))

def logic():
    return param_logic.get()




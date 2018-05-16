import ivy_actions as ia
import ivy_module as im
import ivy_logic as il
import ivy_utils as iu
import logic_util as lu
import ivy_logic_utils as ilu
from collections import defaultdict
from tarjan import tarjan
from itertools import chain

# Here we have definitions relating to IVy's built-in theories.
    
theories = {
'int' : """#lang ivy
    schema rec[t] = {
	type q
	function base(X:t) : q
	function step(X:q,Y:t) : q
	function fun(X:t) : q
	#---------------------------------------------------------
	definition fun(X:t) = base(X) if X <= 0 else step(fun(X-1),X)
    }

    schema ind[t] = {
        relation p(X:t)
        property forall X. X <= 0 -> p(X)
        property forall X. p(X) -> p(X+1)
        #--------------------------
        property p(X)    
    }

    schema lep[t] = {
        function n : t
        function p(X:t) : bool
        #---------------------------------------------------------
        property exists L. (L >= n & forall B. (B >= n & p(B)-> p(L) & L <= B))
    }
"""
}

class Theory(object):
    def __init__(self,name,*args):
        self.args = args
        self.name = name
    def __str__(self):
        return self.name

class IntegerTheory(Theory):
    num_params = 0
    @property
    def schemata():
        return theories['int']
    
class BitVectorTheory(Theory):
    num_params = 1
    @property
    def bits(self):
        return self.args[0]
    @property
    def schemata():
        return theories['int']
    

theory_classes = {
    'int' : IntegerTheory,
    'bv' : BitVectorTheory,
}

def parse_theory(name):
    things = name.split('[')
    thy = things[0]
    things = things[1:]
    if not all(t.endswith(']') for t in things):
        raise iu.IvyError(None,'bad theory syntax: {}'.format(name))
    prms = [int(t[:-1]) for t in things]
    if thy not in theory_classes:
        raise iu.IvyError(None,'unknown theory: {}'.format(name))
    thyc = theory_classes[thy]
    na = thyc.num_params
    if len(prms) != na:
        raise iu.IvyError(None,'wrong number of theory parameters: {}',format(name))
    return thyc(name,*prms)

def get_theory_schemata(name):
    if iu.version_le("1.6",iu.get_string_version()):
        if name.startswith('bv[') or name == 'nat':
            return theories['int']
        return theories.get(name,None)
    return None

# This returns the theory associated with a first-order sort, or if the sort
# is uninterpreted, the sort itself.

def get_sort_theory(sort):
    name = sort.name
    if name in il.sig.interp:
        interp = il.sig.interp[name]
        if isinstance(interp,str):
            interp = parse_theory(interp)
    else:
        interp = sort
    return interp

def has_integer_interp(sort):
    name = sort.name
    if name in il.sig.interp:
        interp = il.sig.interp[name]
        return interp in ['int','nat']
    return False

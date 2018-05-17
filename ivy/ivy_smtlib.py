#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
   This module defines the theories available in SMTLIB
"""

class Theory(object):
    def __init__(self,ivy_name,sorts,ops,infinite):
        self.ivy_name,self.sorts,self.ops,self.infinite = ivy_name,sorts,ops,infinite
    pass

class Sort(object):
    def __init__(self,ivy_name):
        self.ivy_name = ivy_name

class Operator(object):
    def __init__(self,ivy_name,dom,rng):
        self.ivy_name,self.dom,self.rng = ivy_name,dom,rng


intSort = Sort('int')
intOps = [Operator(n,[intSort,intSort],intSort) for n in ['+','-','*','/']]
liaTheory = Theory('int',[intSort],intOps,True)

# Returns true if the theory with quantifiers is decidable
def quantifiers_decidable(theory_name):
    return theory_name not in ['int','nat']

    

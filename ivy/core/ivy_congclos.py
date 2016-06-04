#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_logic import *
from collections import defaultdict

class UndoRep(object):
    def __init__(self,node,rep):
        self.node = node
        self.rep = rep
    def undoit(self):
        self.node[1] = self.rep

class CongClos(object):
    """
    Congruence closure structure. For now we have no function symbols
    so this is just union-find. Representative terms are minimal in
    term order, which for the moment is ascii sorting order.
    
    >>> c = CongClos()
    >>> c.union(to_term("v"),to_term("w"))
    >>> c.find(to_term("w"))
    v
    """

    def __init__(self):
        self.tab = defaultdict(list)
        self.trail = []
        self.pushes = []

    def set_rep(self,node,rep):
        if node[1] != rep:
            self.trail.append(UndoRep(node,node[1]))
            node[1] = rep

    def get_rep_rec(self,node):
        if node[1] == None:
            return node
        rep = self.get_rep_rec(node[1])
        self.set_rep(node,rep)
        return rep

    def get_rep_node(self,term):
        name = term.rep
        node = self.tab[name]
        if not node:
            node.append(term)
            node.append(None)
        return self.get_rep_rec(node)
            
    def find(self,term):
        return self.get_rep_node(term)[0]

    def find_by_name(self,name):
        """ Same as find, but looks up a constant by name, creating a
        constant with the given name if needed. """
        node = self.tab[name]
        if not node:
            node.append(Constant(name))
            node.append(None)
        return self.get_rep_rec(node)[0]

    def union(self,term1,term2):
        rep1 = self.get_rep_node(term1)
        rep2 = self.get_rep_node(term2)
        if rep1 is not rep2:
            if rep1[0].rep < rep2[0].rep:
                self.set_rep(rep2,rep1)
            else:
                self.set_rep(rep1,rep2)

    def add_equality(self,lit):
        self.union(lit.atom.args[0],lit.atom.args[1])

    def theory(self):
        result = []
        for name in self.tab:
            node = self.tab[name]
            var = node[0]
            rep = self.get_rep_rec(node)[0]
            if var is not rep:
                result.append(Literal(1,Atom("=",[var,rep])))
        return result

    def lit_rep(self,lit):
        terms = [(a if isinstance(a,Variable) else self.find(a)) for a in lit.atom.args]
        return Literal(lit.polarity,Atom(lit.atom.relname,terms))

    def clause_rep(self,clause):
        return [self.lit_rep(l) for l in clause]

    def push(self):
        self.pushes.append(len(self.trail))

    def pop(self):
        new_len = self.pushes.pop()
        while len(self.trail) > new_len:
            self.trail.pop().undoit()
        

if __name__ == "__main__":
    c = CongClos()
    c.union(to_term("v"),to_term("w"))
    c.push()
    c.union(to_term("u"),to_term("v"))
    print c.find(to_term("w"))
    c.pop()
    print c.tab
    print c.theory()

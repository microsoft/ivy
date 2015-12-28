#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from ivy_resolution import mgu_eq
from ivy_logic import *
from ivy_logic_utils import * 
import ivy_congclos as congclos
from collections import defaultdict
import ivy_logic

def verbose():
    return False

# hash consing literals

literals = []
lit_hash = dict()

def lit_id(lit):
    """
    Get a unique id for a literal.

    >>> lit_id(to_literal('p(V)'))
    0
    >>> literals[0]
    p(V)
    >>> lit_id(to_literal('q(x)'))
    1
    >>> literals[1]
    q(x)
    >>> lit_id(to_literal('p(V)'))
    0
    """

    key = (lit.polarity, lit.atom.relname, tuple([t.rep for t in lit.atom.args]))
    if key in lit_hash:
        return lit_hash[key]
    id = len(literals)
    literals.append(lit)
    lit_hash[key] = id
    return id

def canonize_literal(lit):
    """ 
    rename variables to constants in a canonical way.

    >>> canonize_literal(to_literal('p(t,X,Y)'))
    p(t, __v1, __v2)
    >>> canonize_literal(to_literal('~p(t,X,X)'))
    ~p(t, __v1, __v1)
    """

    subs = dict()
    terms = []
    for i,t in enumerate(lit.atom.args):
        if isinstance(t,Variable):
            if t.rep not in subs:
                subs[t.rep] = Constant("__v" + str(i))
            terms.append(subs[t.rep])
        else:
            terms.append(t)
    return (Literal(lit.polarity,Atom(lit.atom.relname,terms)),subs)

def canonize_literal_vars(lit):
    """ 
    rename variables to constants in a canonical way.

    >>> canonize_literal(to_literal('p(t,X,Y)'))
    p(t, V1, V2)
    >>> canonize_literal(to_literal('~p(t,X,X)'))
    ~p(t, V1, V1)
    """

    subs = dict()
    terms = []
    for i,t in enumerate(lit.atom.args):
        if isinstance(t,Variable):
            if t.rep not in subs:
                subs[t.rep] = Variable("V" + str(i),t.sort)
            terms.append(subs[t.rep])
        else:
            terms.append(t)
    return Literal(lit.polarity,Atom(lit.atom.relname,terms))

def canonize_literal_unique(lit):
    """ 
    rename variables to constants in a canonical way.

    >>> canonize_literal(to_literal('p(t,X,Y)'))
    p(t, V1, V2)
    >>> canonize_literal(to_literal('~p(t,X,X)'))
    ~p(t, V1, V1)
    """

    subs = dict()
    terms = []
    for i,t in enumerate(lit.atom.args):
        if isinstance(t,Variable):
            if t.rep not in subs:
                subs[t.rep] = Variable("W" + str(i),t.sort)
            terms.append(subs[t.rep])
        else:
            terms.append(t)
    return Literal(lit.polarity,Atom(lit.atom.relname,terms))

def lit_is_specialization(lit):
    return (lit.polarity == 0
            and lit.atom.relname == "="
            and lit.atom.args[0].rep.startswith('__v')
            and isinstance(lit.atom.args[0],Constant)) 

def get_specializations(cl,specs):
    clspecs = [lit for lit in cl if lit_is_specialization(lit)]
    if len(cl) - len(clspecs) <= 1:
        for lit in clspecs:
            specs[lit.atom.args[0].rep].add(lit.atom.args[1].rep)

def make_index():
    return [[],[],defaultdict(make_index)]

def index_lookup(index,lit):
    index = index[lit.polarity][lit.atom.relname]
    for t in lit.atom.args:
        index = index[2]["V" if isinstance(t,Variable) else t.rep]
    return index

equational_theory = None

class EqualityTheory(object):
    """ Context Manager that establishes an equational theory. The
    theory is returned to its previous value when the context exits.
    """
    def __init__(self,et):
        self.equational_theory = et
    def __enter__(self):
        global equational_theory
        self.old_theory = equational_theory
        equational_theory = self.equational_theory
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global equational_theory
        equational_theory = self.old_theory
        return False # don't block any exceptions

def find_term(term):
    if equational_theory == None:
        return term
    return equational_theory.find(term)

def ground_match(term,index):
    if equational_theory == None:
        yield term.rep
    else:
        trep = equational_theory.find(term)
        for t2 in index:
            if equational_theory.find_by_name(t2) is trep:
                yield t2

def find_subsumed_rec(index, terms, idx):
    if idx >= len(terms):
        yield index
        return
    t = terms[idx]
    if isinstance(t,Variable):
        for x,sub_index in index[2].iteritems():
            for y in find_subsumed_rec(sub_index, terms, idx+1):
                yield y
    else:
        for t2 in ground_match(t,index[2]):
            for y in find_subsumed_rec(index[2][t2], terms, idx+1):
                yield y
        
def find_subsuming_rec(index, terms, idx):
    if idx >= len(terms):
        yield index
        return
    t = terms[idx]
    if "V" in index[2]:
        for y in find_subsuming_rec(index[2]["V"], terms, idx+1):
            yield y
    if not isinstance(t,Variable):
        for t2 in ground_match(t,index[2]):
            for y in find_subsuming_rec(index[2][t2], terms, idx+1):
                yield y

def find_unifying_rec(index, terms, idx):
    if idx >= len(terms):
        yield index
        return
    t = terms[idx]
    if isinstance(t,Variable) or t.rep.startswith('__v'):
        for x,sub_index in index[2].iteritems():
            for y in find_unifying_rec(sub_index, terms, idx+1):
                yield y
    else:
        if "V" in index[2]:
            for y in find_unifying_rec(index[2]["V"], terms, idx+1):
                yield y
        for t2 in ground_match(t,index[2]):
            for y in find_unifying_rec(index[2][t2], terms, idx+1):
                yield y


def find_subsumed(index,lit):
    index = index[lit.polarity][lit.atom.relname]
    return find_subsumed_rec(index,lit.atom.args,0)

def find_subsuming(index,lit):
    index = index[lit.polarity][lit.atom.relname]
    return find_subsuming_rec(index,lit.atom.args,0)

def find_unifying(index,lit):
    index = index[lit.polarity][lit.atom.relname]
    return find_unifying_rec(index,lit.atom.args,0)

def lit_rep(lit):
    if equational_theory == None:
        return lit
    terms = [(a if isinstance(a,Variable) else equational_theory.find(a)) for a in lit.atom.args]
    return Literal(lit.polarity,Atom(lit.atom.relname,terms))

def clause_rep(clause):
    if equational_theory == None:
        return clause
    return [lit_rep(l) for l in clause]

def lit_subsume_mod_eq(lit1,lit2,env):
    return lit_subsume(lit_rep(lit1),lit_rep(lit2),env)

new_specialization = True

class UnitRes(object):
    """ 
    Performs unit resolution
    """

    def __init__(self,clauses):
        self.clauses = [] # copy the clauses
        self.index = [defaultdict(make_index),defaultdict(make_index)]
        self.unit_queue = []
        self.subsumed = []
        self.unsat = False
        self.used_units = 0
        self.stack = []
        self.clauses_gen = [] # clause generations
        self.unit_queue_gen = [] # unit queue generations
        self.unit_ids = set()
        self.detected_specializations = []
#        self.equational_theory = None
        self.equational_theory = congclos.CongClos()
        self.unit_term_index = defaultdict(list)
        with UnsortedContext():
            with self.context():
                for cl in clauses:
                    self.add_clause(cl)

    def context(self):
        return EqualityTheory(self.equational_theory)

    def unit_subsumed_basic(self,lit):
        subsuming = find_subsuming(self.index,lit)
        for index in subsuming:
            for lit2_idx in index[0]:
                lit2 = self.unit_queue[lit2_idx]
                if lit_subsume_mod_eq(lit2,lit,dict()):
                    return True
        return False
#            return any(any( for lit2 in index[0]) for index in subsuming)

    def unit_subsumed(self,lit):
        return (self.unit_subsumed_basic(lit)
                or (is_disequality_lit(lit) and self.unit_subsumed_basic(swap_args_lit(lit))))

    def add_clause_basic(self,cl,gen=0):
        n = len(cl)
        if n == 0:
            self.unsat = True
            self.used_units = len(self.unit_queue)
        elif n == 1:
            lit = lit_rep(canonize_literal_vars(cl[0]))
            if not is_taut_lit(lit) and not self.unit_subsumed(lit):
                litid = lit_id(lit)
                index_lookup(self.index,lit)[0].append(len(self.unit_queue))
                self.unit_queue.append(lit)
                self.unit_queue_gen.append(gen)
                self.unit_ids.add(litid)
                if verbose():
                    print "added %s %s" % (lit,litid)
        else:
            i = len(self.clauses)
            self.clauses.append(cl)
            self.clauses_gen.append(gen)
            self.reindex(i)

    def add_clause(self,cl,gen=0):
        self.add_clause_basic(cl,gen)
        # apply hyper binary resolution with transitivity axiom
        # inference: x = y -> x = z |- x = y -> y = z (mod symmetry)
        if len(cl) == 2 and is_ground_clause(cl):
            for i in [0,1]:
                lhs,rhs = cl[i], cl[1-i]
                if is_disequality_lit(lhs) and is_equality_lit(rhs):
                    for j in [0,1]:
                        subs = {lhs.atom.args[j].rep : lhs.atom.args[1-j]}
                        new_rhs = substitute_constants_lit(rhs,subs)
                        if not lit_eq(rhs,new_rhs):
                            new_cl = [lhs,new_rhs]
                            print "applied transitivity: %s" % cl
                            self.add_clause_basic(new_cl,gen)

    def update_equational_theory(self,lit):
        if lit.polarity == 1 and lit.atom.relname == '=':
            t0,t1 = lit.atom.args[0],lit.atom.args[1]
            if isinstance(t0,Constant) and isinstance(t1,Constant):
                equational_theory.union(t0,t1)
                if verbose():
                    print "merged %s %s" % (t0,t1)

    def get_watching(self,lit):
        return index_lookup(self.index,lit)[1]

    def deindex(self,i):
        for j in range(0,len(self.clauses[i])):
            lit = self.clauses[i][j]
            wl = self.get_watching(lit)
            wl.remove((i,j))

    def reindex(self,i):
        for j,lit in enumerate(self.clauses[i]):
            self.get_watching(lit).append((i,j))

    def index_unit_terms(self,i):
        used = set()
        for t in self.unit_queue[i].atom.args:
            if not isinstance(t,Variable) and t.rep not in used:
                used.add(t.rep)
                if any(lit_eq(self.unit_queue[j],self.unit_queue[i]) for j in self.unit_term_index[t.rep]):
                    print "bad add: %s %s %s" % (self.unit_queue[i],i,self.unit_term_index[t.rep])
                    exit(1)
                self.unit_term_index[t.rep].append(i)
        # also index units by their relation name
        self.unit_term_index[self.unit_queue[i].atom.relname].append(i)

    def deindex_unit_terms(self,i):
        used = set()
        for t in self.unit_queue[i].atom.args:
            if not isinstance(t,Variable) and t.rep not in used:
                used.add(t.rep)
                self.unit_term_index[t.rep].remove(i)
        # also index units by their relation name
        self.unit_term_index[self.unit_queue[i].atom.relname].remove(i)

    def unit_subsumed_by_used(self,lit):
        subsuming = find_subsuming(self.index,lit)
        for index in subsuming:
            for lit2_idx in index[0]:
                if lit2_idx < self.used_units:
                    lit2 = self.unit_queue[lit2_idx]
                    if lit_subsume_mod_eq(lit2,lit,dict()):
                        return True
        return False

    def subsumed_by_used_lit(self,a1,a2,clause):
        for lit in clause:
            if self.unit_subsumed_by_used(lit) or self.unit_subsumed_by_used(Literal(1-lit.polarity,lit.atom)):
#                if verbose():
#                print "%s %s -> %s canceled by literal %s" % (a1,a2,clause,lit)
                return True
        return False

    def allow_eqs(self,lit,eqs,is_unit = False, other = None):
        if lit.atom.relname == '=':
            return not eqs
        if all(atom.args[0].rep.startswith('__v') and not atom.args[1].rep.startswith('__v') for atom in eqs):
            if not new_specialization or is_unit:
                return True
            if eqs and verbose():
                print "spec: %s, %s -> %s" % (lit,other,eqs)
            self.detected_specializations.extend(eqs)
        return not eqs


    def propagate_equality(self,lit,gen):
        lit = lit_rep(lit)
        if is_taut_lit(lit):
            return
        t0,t1 = lit.atom.args[0],lit.atom.args[1] 
        if t0.rep < t1.rep:
            t0,t1 = t1,t0
        for lit_idx in self.unit_term_index[t0.rep]:
            lit2 = self.unit_queue[lit_idx]
            lit3 = substitute_constants_lit(lit2,{t0.rep:t1})
            if not lit_eq(lit2,lit3):
                new_cl = [lit3]
                if verbose():
                    print "rewrite! %s,%s -> %s" % (lit,lit2,new_cl)
                new_gen = max(gen+1,self.unit_queue_gen[lit_idx])
                self.add_clause(new_cl,new_gen)
                if self.unsat:
                    return
        self.update_equational_theory(lit)
        for lit_idx in self.unit_term_index[t1.rep]:
            lit2 = self.unit_queue[lit_idx]
            if verbose():
                print "re-propagate: %s" % lit2
            self.propagate_lit(lit2,max(gen+1,self.unit_queue_gen[lit_idx]))
            if self.unsat:
                return
                

    def propagate_lit(self,lit,gen=0,specs = None):
        """
        Perform unit resolution using a literal.

        >>> r = UnitRes(to_clauses("[[a(),b()]]"))
        >>> r.propagate_lit(to_literal('~a()'))
        >>> r.unit_queue
        [b()]
        >>> r.watching
        [{}, {'a': [], 'b': []}]
        >>> r.subsumed
        [0]
        >>> r.clauses
        [[a(), b()]]
        """

#        print self.index
        if self.equational_theory != None and is_ground_equality_lit(lit):
            self.propagate_equality(lit,gen)
            return
#        if lit.atom.relname == '=' and lit.polarity == 0:
#            return
        lits = [lit,Literal(lit.polarity,Atom('=',[lit.atom.args[1],lit.atom.args[0]]))] if lit.atom.relname == '=' else [lit]
        for lit in lits:
            keep = keep_lit(lit)
            indices = list(find_unifying(self.index,Literal(1 - lit.polarity,lit.atom))) # save this in cas index changes
            lit = lit_rep(canonize_literal_unique(lit))
            for index in indices:
                wl = index[1]
    #        print "%s -- %s" % (lit,wl)
                for i,j in list(wl): # copy the list in case we modify it
                    cl = self.clauses[i]
        #            print "cl: %s lit: %s" % (cl,lit)
                    lit2 = lit_rep(cl[j])
                    if lit2.polarity != 1-lit.polarity or lit2.atom.relname != lit.atom.relname:
                        print "!!! %s %s %s %s %s" % (i,j,lit,lit2,cl)
                        exit(1)
                    if is_equality_lit(lit2) and all(isinstance(t,Variable) for t in lit2.atom.args):
                        continue
                    match, subs, eqs = mgu_eq(lit.atom, lit2.atom)
        #            print "lit: %s" % lit
                    if match and self.allow_eqs(lit,eqs,False,cl):
                        if atom_subsume(lit.atom,lit2.atom):
                            self.deindex(i)
                            self.subsumed.append(i)
        #                print "lit: %s" % lit
                        new_cl = [substitute_lit(lit1, subs) for k,lit1 in enumerate(cl) if k != j] + [Literal(0,eq) for eq in eqs]
                        if not new_specialization and not (specs == None):
                            if verbose():
                                print "using specs: %s" % specs
                            new_cl = substitute_constants_clause(new_cl,specs)
                        new_cl = simplify_clause(new_cl)
                        if not is_tautology(new_cl) and not self.subsumed_by_used_lit(lit,cl,new_cl):
                            if verbose():
                                print "%s,%s -> %s" % (lit,cl,new_cl)
                            new_gen = max(gen+1,self.clauses_gen[i])
                            self.add_clause(new_cl,new_gen)
                            if self.unsat:
                                return
                
                if keep:
                    self.resolve_units(lit,index[0],gen,False) # have to unify against units too!
                    if self.unsat:
                        return
            # if we are not keeping this unit as a consequence,
            # resolve it against all of the the units that might match
            # under equality, so that we can infer disequalities
            if keep == False:
                others = [x for x in self.unit_term_index[lit.atom.relname] if self.unit_queue[x].polarity != lit.polarity]
                self.resolve_units(lit,others,gen,True) # 
                if self.unsat:
                    return


    def resolve_units(self,lit,units,gen,allow_unit_diseqs):
        for lit_idx in list(units): # copy the list in case it changes
            lit2 = lit_rep(self.unit_queue[lit_idx])
            match, subs, eqs = mgu_eq(lit.atom, lit2.atom)
#            print "lit: %s" % lit
            if match and (self.allow_eqs(lit,eqs,True) or (allow_unit_diseqs and len(eqs) == 1 and keep_atom(eqs[0]))):
                new_cl = [Literal(0,eq) for eq in eqs]
                if not self.subsumed_by_used_lit(lit,lit2,new_cl):
                    if verbose():
                        print "units resolve! %s,%s -> %s" % (lit,lit2,new_cl)
                    new_gen = max(gen+1,self.unit_queue_gen[lit_idx])
                    self.add_clause(new_cl,new_gen)
                    if self.unsat:
                        return
                

    def propagate(self, specs = None):
        """
        Do unit propagation to a fixed point. The propagated units are
        added to unsed_units.

        >>> from dilemma import *
        >>> r = UnitRes(to_clauses("[[~a()],[a(),~b()],[b(),c()]]"))
        >>> r.propagate()
        >>> r.used_units
        [~a(), ~b(), c()]
        """
        
        save_thing = ivy_logic.allow_unsorted
        ivy_logic.allow_unsorted = True
        while self.used_units < len(self.unit_queue):
            lit_num = self.used_units
            lit = self.unit_queue[lit_num]
            gen = self.unit_queue_gen[lit_num]
            self.propagate_lit(lit,gen,specs)
            if self.used_units < lit_num + 1:
                self.used_units = lit_num + 1
            # maintain invariant that all used units have terms indexed
            for j in range(lit_num,self.used_units):
                self.index_unit_terms(j) # this lit might get rewritten later
        ivy_logic.allow_unsorted = save_thing

def keep_atom(atom):
    name = atom.relname
    if name.is_skolem():
        return False
    for term in atom.args:
        if is_constant(term) and term.rep.is_skolem():
            return False
    return True

def keep_lit(lit):
    return keep_atom(lit.atom)
        
    
if __name__ == "__main__":
#    r = UnitRes(to_clauses("[[p(v)],[~r(),=(v,w)],[~p(w),q(w)],[r()]]"))
    r = UnitRes(to_clauses("p(U,v) & v = u & (~p(x,u) | q(u))"))
    with r.context():
        r.propagate()
        print r.unit_queue


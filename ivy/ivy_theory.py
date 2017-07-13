import ivy_actions as ia
import ivy_module as im
import ivy_logic as il
import ivy_utils as iu
import logic_util as lu
from collections import defaultdict
from tarjan import tarjan
from itertools import chain

# Union-find data structure for stratification check

class UFNode(object):
    """
    A sort variable, to be replaced by an arbitrary sort.

    The instance property is used to implement union find, and it can
    either be None, another UFNode object, or a sort object.

    """
    def __init__(self):
        global ufidctr
        self.instance = None
        self.id = ufidctr
        ufidctr += 1
    def __str__(self):
        return str(self.id)
    def __repr__(self):
        return str(self.id)


ufidctr = 0

def find(x):
    """
    Find the representative of a node
    """
    if x.instance is None:
        return x
    else:
        # collapse the path and return the root
        x.instance = find(x.instance)
        return x.instance

def unify(s1, s2):
    """
    Unify nodes s1 and s2.
    """
    s1 = find(s1)
    s2 = find(s2)

    if s1 != s2:
        s1.instance = s2


def show_strat_map(m):
    print 'strat_map = {'
    for x,y in m.iteritems():
        if isinstance(x,tuple):
            print '({},{}) : {}'.format(x[0],x[1],y)
        else:
            print '{} : {}'.format(x,y)
    print '}'
        

# Here we have rules for checking that VC's are in
# a decidable fragment

def get_qa_arcs(fmla,ast,pol,univs,strat_map):
    if isinstance(fmla,il.Not):
        for a in get_qa_arcs(fmla.args[0],ast,not pol,univs,strat_map):
            yield a
        return
    is_e = il.is_exists(fmla)
    is_a = il.is_forall(fmla)
    if is_e and pol or is_a and not pol:
        fvs = set(il.free_variables(fmla))
        for u in univs:
            if u in fvs:
                for e in il.quantifier_vars(fmla):
                    yield (find(strat_map[u]),find(strat_map[e]),ast)
    if is_e and not pol or is_a and pol:
        for a in get_qa_arcs(fmla.args[0],ast,pol,univs+list(il.quantifier_vars(fmla)),strat_map):
            yield a
    for arg in fmla.args:
        for a in get_qa_arcs(arg,ast,pol,univs,strat_map):
            yield a

def get_sort_arcs(assumes,asserts,strat_map):
    # for sym in il.all_symbols():
    #     name = sym.name
    #     sort = sym.sort
    #     rng = sort.rng
    #     if il.is_uninterpreted_sort(rng):
    #         for ds in sort.dom:
    #             if il.is_uninterpreted_sort(ds):
    #                 yield (ds,rng,sym)

    for func,node in list(strat_map.iteritems()):
        if isinstance(func,tuple):
            yield (find(node),find(strat_map[func[0]]),func[0])

    for fmla,ast in assumes + asserts:
        for a in get_qa_arcs(fmla,ast,True,list(lu.free_variables(fmla)),strat_map):
            yield a

    for fmla,ast in asserts:
        for a in get_qa_arcs(fmla,ast,False,[],strat_map):
            yield a
    

def get_sort_sccs(arcs):
    m = defaultdict(set)
    for ds,rng,ast in arcs:
        m[ds].add(rng)

    sccs = tarjan(m)
    return sccs
                    

def map_fmla(fmla,strat_map):
    if il.is_binder(fmla):
        return map_fmla(fmla.body,strat_map)
    if il.is_variable(fmla):
        if fmla not in strat_map:
            strat_map[fmla] = UFNode()
        return strat_map[fmla]
    nodes = [map_fmla(f,strat_map) for f in fmla.args]
    if il.is_eq(fmla):
        unify(*nodes)
        return None
    if il.is_ite(fmla):
        unify(*nodes[1:])
        return nodes[1]
    if il.is_app(fmla):
        func = fmla.rep
        if not il.is_interpreted_symbol(func):
            for idx,node in enumerate(nodes):
                if node is not None:
                    unify(strat_map[(func,idx)],node)
            return strat_map[func]
    return None
                
def create_strat_map(assumes,asserts):
    strat_map = defaultdict(UFNode)
    for pair in assumes+asserts:
        map_fmla(pair[0],strat_map)
    return strat_map

def get_unstratified_funs(assumes,asserts):

    vu = il.VariableUniqifier()
    
    def vupair(p):
        return (vu(p[0]),p[1])

    assumes = map(vupair,assumes)
    asserts = map(vupair,asserts)
    strat_map = create_strat_map(assumes,asserts)
    

    arcs = list(get_sort_arcs(assumes,asserts,strat_map))

    sccs = get_sort_sccs(arcs)
    scc_map = dict((name,idx) for idx,scc in enumerate(sccs) for name in scc)
    scc_arcs = [[] for x in sccs]

    unstrat = set()
    for ds,rng,ast in arcs:
        if scc_map[ds] == scc_map[rng]:
            scc_arcs[scc_map[ds]].append(ast)
            
    fun_sccs = [(x,y) for x,y in zip(sccs,scc_arcs) if y]

    return fun_sccs


def get_assumes_and_asserts():    
    assumes = []
    asserts = []
    for name,action in im.module.actions.iteritems():
        for sa in action.iter_subactions():
            if isinstance(sa,ia.AssumeAction):
                assumes.append((sa.args[0],sa))
            if isinstance(sa,ia.AssertAction):
                asserts.append((sa.args[0],sa))
            if isinstance(sa,ia.IfAction):
                asserts.append((sa.get_cond(),sa))

    for ldf in im.module.definitions:
        assumes.append((ldf.formula.to_constraint(),ldf))

    for ldf in im.module.labeled_axioms:
        assumes.append((ldf.formula,ldf))

    for ldf in im.module.labeled_props:
        asserts.append((ldf.formula,ldf))

    # TODO: check axioms, inits, conjectures

    return assumes,asserts

def report_error(logic,note,ast,unstrat):
    msg = "The verification condition is not in logic {}{} because {}.".format(logic,note,il.reason())
    if il.reason() == "functions are not stratified":
        for sorts,asts in unstrat:
            msg += "\n\nNote: the following functions form a cycle:\n"
            for a in asts:
                if isinstance(a,il.Symbol):
                    msg += '  function {}\n'.format(a)
                else:
                    msg += '  {}\n'.format(iu.IvyError(a,"quantifier alternation"))                
    iu.dbg('ast.lineno')
    raise iu.IvyError(ast,msg)

def check_can_assert(logic,fmla,ast,unstrat):
    check_can_assume(logic,fmla,ast,unstrat)
    if not il.is_in_logic(il.Not(fmla),logic,unstrat):
        report_error(logic," when negated",ast,unstrat)

def check_can_assume(logic,fmla,ast,unstrat):
    if not il.is_in_logic(il.close_formula(fmla),logic,unstrat):
        report_error(logic,"",ast,unstrat)
    
def check_theory():
    assumes,asserts = get_assumes_and_asserts()
    unstrat = get_unstratified_funs(assumes,asserts)
    
    errs = []
    for logic in im.logics():
        try:
            for a in assumes:
                check_can_assume(logic,*a,unstrat=unstrat)

            for a in asserts:
                check_can_assert(logic,*a,unstrat=unstrat)
            return
        except iu.IvyError as err:
            errs.append(err)

    # if we got here, all logics had errors

    if len(errs) == 1:
        raise errs[0]

    raise iu.ErrorList(errs)
    
theories = {
'int' : """#lang ivy1.6
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
        property X <= 0 -> p(X)
        property p(X) -> p(X+1)
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

def get_theory(name):
    return theories.get(name,None)


    

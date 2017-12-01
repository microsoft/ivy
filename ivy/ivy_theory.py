import ivy_actions as ia
import ivy_module as im
import ivy_logic as il
import ivy_utils as iu
import logic_util as lu
import ivy_logic_utils as ilu
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
        self.variables = set()
    def __str__(self):
        return str(self.id) + '[' + ','.join(str(x) for x in self.variables) + ']'
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
    if s1 is None or s2 is None:
        return

    s1 = find(s1)
    s2 = find(s2)

    if s1 != s2:
        s1.instance = s2


def show_strat_map(m):
    print 'strat_map = {'
    for x,y in m.iteritems():
        y = find(y)
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
    if isinstance(fmla,il.Implies):
        for a in get_qa_arcs(fmla.args[0],ast,not pol,univs,strat_map):
            yield a
        for a in get_qa_arcs(fmla.args[1],ast,pol,univs,strat_map):
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
    if isinstance(fmla,il.Ite):
        for a in get_qa_arcs(fmla.args[0],ast,not pol,univs,strat_map):
            yield a
    if isinstance(fmla,il.Iff) or (il.is_eq(fmla) and il.is_boolean(fmla.args[0])):
        for a in get_qa_arcs(fmla.args[0],ast,not pol,univs,strat_map):
            yield a
        for a in get_qa_arcs(fmla.args[1],ast,not pol,univs,strat_map):
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

    show_strat_map(strat_map)
    for func,node in list(strat_map.iteritems()):
        if isinstance(func,tuple) and not il.is_interpreted_symbol(func[0]):
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
            res = UFNode()
            res.variables.add(fmla)
            strat_map[fmla] = res
        return strat_map[fmla]
    nodes = [map_fmla(f,strat_map) for f in fmla.args]
    if il.is_eq(fmla):
        unify(*nodes)
        if il.is_interpreted_sort(fmla.args[0].sort):
            unify(strat_map[(fmla.rep,0)],nodes[0])
        return None
    if il.is_ite(fmla):
        unify(*nodes[1:])
        return nodes[1]
    if il.is_app(fmla):
        func = fmla.rep
        if func in symbols_over_universals or True:
            for idx,node in enumerate(nodes):
                if node is not None:
                    unify(strat_map[(func,idx)],node)
            return strat_map[func]
    return None
                
def create_strat_map(assumes,asserts,macros):
    global symbols_over_universals
    global universally_quantified_variables
    all_fmlas = [il.close_formula(pair[0]) for pair in assumes]
    all_fmlas.extend(il.Not(pair[0]) for pair in asserts)
    all_fmlas.extend(pair[0] for pair in macros)
#    for f in all_fmlas:
#        print f
    symbols_over_universals = il.symbols_over_universals(all_fmlas)
    iu.dbg('[str(x) for x in symbols_over_universals]')
    universally_quantified_variables = il.universal_variables(all_fmlas)
    
    strat_map = defaultdict(UFNode)
    for pair in assumes+asserts+macros:
        map_fmla(pair[0],strat_map)

#    show_strat_map(strat_map)
#    print 'universally_quantified_variables:{}'.format(universally_quantified_variables)
    return strat_map

def get_unstratified_funs(assumes,asserts,macros):

    vu = il.VariableUniqifier()
    
    def vupair(p):
        return (vu(p[0]),p[1])

    assumes = map(vupair,assumes)
    asserts = map(vupair,asserts)
    macros = map(vupair,macros)
    strat_map = create_strat_map(assumes,asserts,macros)
    
    for f,g in macros:
        print 'macro: {}'.format(f)


    arcs = list(get_sort_arcs(assumes+macros,asserts,strat_map))

    sccs = get_sort_sccs(arcs)
    scc_map = dict((name,idx) for idx,scc in enumerate(sccs) for name in scc)
    scc_arcs = [[] for x in sccs]

    unstrat = set()
    for ds,rng,ast in arcs:
        if scc_map[ds] == scc_map[rng]:
            scc_arcs[scc_map[ds]].append(ast)
            
    for y in strat_map.values():
        find(y).variables.update(y.variables)

    fun_sccs = [(x,y) for x,y in zip(sccs,scc_arcs)
                if y and any(len(n.variables) > 0 for n in x)]

    arc_map = defaultdict(list)
    for x,y,z in arcs:
        arc_map[x].append(y)
    for scc in sccs:
        for n in scc:
            for m in arc_map[n]:
                m.variables.update(n.variables)
    
    # print 'sccs:'
    # for scc in sccs:
    #     print [str(x) for x in scc]


#    show_strat_map(strat_map)

    bad_interpreted = set()
    for x,y in strat_map.iteritems():
        y = find(y)
        if isinstance(x,tuple) and (il.is_interpreted_symbol(x[0]) or x[0].name == '='):
            if any(v in universally_quantified_variables and 
                   v.sort == x[0].sort.dom[x[1]] and
                   il.has_infinite_interpretation(v.sort) for v in y.variables):
                bad_interpreted.add(x[0])

    return fun_sccs, bad_interpreted


def get_assumes_and_asserts(preconds_only):    
    assumes = []
    asserts = []
    macros = []
#    for name,action in im.module.actions.iteritems():
        # for sa in action.iter_subactions():
        #     if isinstance(sa,ia.AssumeAction):
        #         assumes.append((sa.args[0],sa))
        #     if isinstance(sa,ia.AssertAction):
        #         asserts.append((sa.args[0],sa))
        #     if isinstance(sa,ia.IfAction):
        #         asserts.append((sa.get_cond(),sa))
    if preconds_only:
        for name in im.module.before_export:
            action = im.module.before_export[name]
            triple = action.update(im.module,[])
            foo = ilu.close_epr(ilu.clauses_to_formula(triple[1]))
            assumes.append((foo,action))
    else:
        for name in im.module.public_actions:
            action = im.module.actions[name]
            triple = action.update(im.module,[])
            #        print 'ivy_theory.py: triple[1]: {}'.format(triple[1])
            foo = ilu.close_epr(ilu.clauses_to_formula(triple[1]))
            #       print 'ivy_theory.py: foo (1): {}'.format(foo)
            assumes.append((foo,action))
            #        print 'ivy_theory.py: triple[2]: {}'.format(triple[2])
            foo = ilu.close_epr(ilu.clauses_to_formula(triple[2]))
            #        print 'ivy_theory.py: foo (2): {}'.format(foo)
            assumes.append((foo,action))
        
    for ldf in im.module.definitions:
        if ldf.formula.defines() not in ilu.symbols_ast(ldf.formula.rhs()):
            macros.append((ldf.formula.to_constraint(),ldf))
        else: # can't treat recursive definition as macro
            assumes.append((ldf.formula.to_constraint(),ldf))

    for ldf in im.module.labeled_axioms:
        if not ldf.temporal:
            assumes.append((ldf.formula,ldf))

    for ldf in im.module.labeled_props:
        if not ldf.temporal:
            asserts.append((ldf.formula,ldf))

    for ldf in im.module.labeled_conjs:
        asserts.append((ldf.formula,ldf))
        assumes.append((ldf.formula,ldf))
    # TODO: check axioms, inits, conjectures

    return assumes,asserts,macros

def report_error(logic,note,ast):
    msg = "The verification condition is not in logic {}{} because {}.".format(logic,note,il.reason())
    if il.reason() == "functions are not stratified":
        for sorts,asts in unstrat:
            msg += "\n\nNote: the following functions form a cycle:\n"
            for a in asts:
                if isinstance(a,il.Symbol):
                    msg += '  {}\n'.format(il.sym_decl_to_str(a))
                else:
                    msg += '  {}\n'.format(iu.IvyError(a,"quantifier alternation"))                
    raise iu.IvyError(ast,msg)

def report_epr_error(unstrat,bad_interpreted):
    msg = "The verification condition is not in logic epr."
    for sorts,asts in unstrat:
        msg += "\n\nNote: the following functions form a cycle:\n"
        for a in asts:
            if isinstance(a,il.Symbol):
                msg += '  {}\n'.format(il.sym_decl_to_str(a))
            else:
                msg += '  {}\n'.format(iu.IvyError(a,"skolem function"))                
    if bad_interpreted:
        msg += "\n\nNote: the following interpreted functions occur over variables:\n"
        for sym in bad_interpreted:
            msg += '  {}\n'.format(il.sym_decl_to_str(sym))
            
    raise iu.IvyError(None,msg)

def check_can_assert(logic,fmla,ast):
    check_can_assume(logic,fmla,ast)
    if not il.is_in_logic(il.Not(fmla),logic):
        report_error(logic," when negated",ast)

def check_can_assume(logic,fmla,ast):
    if not il.is_in_logic(il.close_formula(fmla),logic):
        report_error(logic,"",ast)
    
def check_theory(preconds_only=False):
    assumes,asserts,macros = get_assumes_and_asserts(preconds_only)

    errs = []
    for logic in im.logics():
        try:
            if logic == 'epr':
                unstrat,bad_interpreted = get_unstratified_funs(assumes,asserts,macros)
                if unstrat or bad_interpreted:
                    report_epr_error(unstrat,bad_interpreted)
            else:
                for a in chain(assumes,macros):
                    check_can_assume(logic,*a)

                for a in asserts:
                    check_can_assert(logic,*a)
            return
        except iu.IvyError as err:
            errs.append(err)

    # if we got here, all logics had errors

    if len(errs) == 1:
        raise errs[0]

    raise iu.ErrorList(errs)
    
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
    if iu.version_le("1.6",iu.get_string_version()):
        if name.startswith('bv['):
            return theories['int']
        return theories.get(name,None)
    return None


    

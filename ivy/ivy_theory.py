import ivy_actions as ia
import ivy_module as im
import ivy_logic as il
import ivy_utils as iu
import logic_util as lu
from collections import defaultdict
from tarjan import tarjan

# Here we have rules for checking that VC's are in
# a decidable fragment

def get_qa_arcs(fmla,ast,pol,univs):
    if isinstance(fmla,il.Not):
        for a in get_qa_arcs(fmla.args[0],ast,not pol,univs):
            yield a
        return
    is_e = il.is_exists(fmla)
    is_a = il.is_forall(fmla)
    if is_e and pol or is_a and not pol:
        fvs = set(il.free_variables(fmla))
        for u in univs:
            if u in fvs:
                for e in il.quantifier_vars(fmla):
                    yield (u.sort,e.sort,ast)
    if is_e and not pol or is_a and pol:
        for a in get_qa_arcs(fmla.args[0],ast,pol,univs+list(il.quantifier_vars(fmla))):
            yield a
    for arg in fmla.args:
        for a in get_qa_arcs(arg,ast,pol,univs):
            yield a

def get_sort_arcs(assumes,asserts):
    for sym in il.all_symbols():
        name = sym.name
        sort = sym.sort
        rng = sort.rng
        if il.is_uninterpreted_sort(rng):
            for ds in sort.dom:
                if il.is_uninterpreted_sort(ds):
                    yield (ds,rng,sym)

    for fmla,ast in assumes + asserts:
        for a in get_qa_arcs(fmla,ast,True,list(lu.free_variables(fmla))):
            yield a

    for fmla,ast in asserts:
        for a in get_qa_arcs(fmla,ast,False,[]):
            yield a
    

def get_sort_sccs(arcs):
    m = defaultdict(set)
    for ds,rng,ast in arcs:
        m[ds.name].add(rng.name)

    sccs = tarjan(m)
    return sccs
                    

def get_unstratified_funs(assumes,asserts):
    arcs = list(get_sort_arcs(assumes,asserts))

    sccs = get_sort_sccs(arcs)
    scc_map = dict((name,idx) for idx,scc in enumerate(sccs) for name in scc)
    scc_arcs = [[] for x in sccs]

    unstrat = set()
    for ds,rng,ast in arcs:
        if scc_map[ds.name] == scc_map[rng.name]:
            scc_arcs[scc_map[ds.name]].append(ast)
            
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
    # TODO: check axioms, inits, conjectures

    return assumes,asserts

def report_error(logic,note,ast,unstrat):
    msg = "This formula is not in logic {}{} because {}".format(logic,note,il.reason())
    for sorts,asts in unstrat:
        msg += "\n\nNote: the sort(s) " + ','.join(sorts) + ' form a function cycle using:\n'
        for a in asts:
            if isinstance(a,il.Symbol):
                msg += '  function {}\n'.format(a)
            else:
                msg += '  {}\n'.format(iu.IvyError(a,"quantifier alternation"))                
    raise iu.IvyError(ast,msg)

def check_can_assert(logic,fmla,ast,unstrat):
    check_can_assume(logic,fmla,ast,unstrat)
    if not il.is_in_logic(il.Not(fmla),logic,unstrat):
        report_error(logic," when negated",ast,unstrat)

def check_can_assume(logic,fmla,ast,unstrat):
    if not il.is_in_logic(fmla,logic,unstrat):
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
    

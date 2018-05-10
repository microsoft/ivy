import ivy_actions as ia
import ivy_module as im
import ivy_logic as il
import ivy_utils as iu
import logic_util as lu
import ivy_logic_utils as ilu
from collections import defaultdict
from tarjan import tarjan
from itertools import chain
from ivy_union_find import *

# Here we have rules for checking that VC's are in
# a decidable fragment


# These functions compute the stratification graph, as described in
#
#   Yeting Ge and Leonardo de Moura, Complete instantiation for
#   quantified formulas in Satisfiability Modulo Theories
#
# The nodes of this graph the sets `S_v` and `A_f,j`, where `v` is a
# universally quantified variable, `f` is an uninterpreted symbol and
# `j` is an argument position of `f` (since variable names are
# globally unique, we don't identify variable occurrences by a pair
# `k,i` as in the paper). 
#
# Nodes `S_v` and `A_f,j` are unified (using union-find) when `v`
# occurs as the `jth` argument of `f`.  An arc occurs in the graph from `S_v`
# to `A_f,j` when some term containing `S_v` *not* at top level occurs
# as the the `jth` argument of `f`. 
#
# The formula is in the finite essentially uninterpreted fragment
# (FEU) iff this graph is acyclic.
#
# The graph is represented by a pair `(strat_map,arcs)` where `strat_map`
# maps nodes `S_v` and `A_f,j` to union-find nodes and `arcs` is a
# list of arcs `(x,y)`, represented as quadruples `(x,y,term,j)` where
# `x` and `y` are union-find nodes, `term` is the term that generated
# the arc, and `j` is the relevant argument position.
#
# We add the following rules for equality (modulo symmetry):
#
#    | equality term          |  constraint    |
#    |------------------------|----------------|
#    | v = t[w]               | S_w --> S_v    |
#    | v = w                  | S_v = S_w      |

# We treat an ite `t1[v] if c else t2[w]` as if it were converted to `f(v,w)`
# and the constraint `forall v,w. (c -> f(v,w) = t1[v]) & (~c -> f(v,w) = t2[w]`.

# We treat quantifier alternations as if the were skolemized. That is, if
# we have `exists w. t[v,w]` we treat it as `t<f(v)/w>`. 

# The globals macro_var_map and macro_dep_map are explained below.

def map_fmla(lineno,fmla,strat_map,arcs):
    """ Add all of the subterms of `fmla` to the stratification graph. """

    global universally_quantified_variables
    global macro_var_map
    global macro_dep_map

    if il.is_binder(fmla):
        return map_fmla(lineno,fmla.body,strat_map,arcs)
    if il.is_variable(fmla):
        if fmla in universally_quantified_variables:
            if fmla not in strat_map:
                res = UFNode()
                strat_map[fmla] = res
            return strat_map[fmla],set()
        return macro_var_map.get(fmla,None), macro_dep_map.get(fmla,set())
    nodes,uvs = iu.unzip_pairs([map_fmla(lineno,f,strat_map,arcs) for f in fmla.args])
    iu.dbg('uvs')
    all_uvs = iu.union_of_list(uvs)
    iu.dbg('nodes')
    iu.dbg('type(all_uvs)')
    all_uvs.update(nodes)
    if il.is_eq(fmla):
        unify(*nodes)
        if all(x is not None for x in nodes):
            unify(*nodes)
        elif nodes[0] is not None:
            arcs.extend((strat_map[v],nodes[0],fmla,lineno) for v in uvs[1])
        elif nodes[1] is not None:
            arcs.extend((strat_map[v],nodes[1],fmla,lineno) for v in uvs[0])
        return None,all_uvs 
    if il.is_ite(fmla):
        if all(x is not None for x in nodes[1:]):
            unify(*nodes[1:])
        elif nodes[1] is not None:
            arcs.extend((strat_map[v],nodes[1],fmla,lineno) for v in uvs[2])
        elif nodes[2] is not None:
            arcs.extend((strat_map[v],nodes[2],fmla,lineno) for v in uvs[1])
        return None,all_uvs
    if il.is_app(fmla):
        func = fmla.rep
        if not il.is_interpreted_symbol(func):
            for idx,node in enumerate(nodes):
                anode = strat_map[(func,idx)]
                if node is not None:
                    unify(anode,node)
                arcs.extend((v,anode,fmla,idx) for v in uvs[idx])
        return None,all_uvs
    return None
                
# We treat macros (non-recursive definitions) as if they were
# syntactically expanded. However, since actually expanding them
# would be exponential, we instead compute the set of universally quantified
# variables that can be substituted under each macro parameter.
#
# There are two maps that store this information:
#
# - macro_dep_map stores, for each macro parameter the universal variables
#   that substituted strictly *under* the parameter, that is, not as
#   the top-level symbol.
#
# - macro_var_map stores, for each macro parameter the universal
#   variables that are substituted *exactly* for the parameter, that is,
#   as the top-level symbol. The set of universal variables is unified
#   in the stratification map and represented by a single element. 
#
# These sets have to be propagated downward from calling to called
# macros, so we travese the list of macros in reverse order.
#
# TODO: make sure macros are really listed in dependency order.

def create_macro_maps(assumes,asserts,macros,strat_map):
    global universally_quantified_variables
    global macro_var_map
    global macro_dep_map
    macro_map = dict()
    for _,lf in macros:
        macro_map[lf.formula.defines()] = lf
    macro_dep_map = defaultdict(set)
    macro_var_map = dict()
    def var_map_add(w,vn):
        if w in macro_var_map:
            unify(macro_var_map[w],vn)
        else:
            macro_var_map[w] = vn
    for fmla,_ in assumes+asserts+list(reversed(macros)):
        for app in ilu.apps_ast(fmla):
            if app.rep in macro_map:
                mvs = macro_map[app.rep].formula.args[0].args
                for v,w in zip(app.args,mvs):
                    if il.is_variable(w):
                        if il.is_variable(v):
                            if v in universally_quantified_variables:
                                var_map_add(w,strat_map[v])
                            if v in macro_var_map:
                                var_map_add(w,macro_var_map[v])
                            if v in macro_dep_map:
                                macro_dep_map[w].update(macro_dep_map[v])
                        else:
                            for v in ilu.used_variables_ast(v):
                                if v in universally_quantified_variables:
                                    macro_dep_map[w].add(v)
                            if v in macro_var_map:
                                macro_dep_map[w].add(macro_var_map[v])
                            if v in macro_dep_map:
                                macro_dep_map[w].update(macro_var_map[v])
    print 'macro_var_map: {'
    for x,y in macro_var_map.iteritems():
        print '{} -> {}'.format(x,y)
    print '}'
#
# We treat AE quantifier alternations as if the were skolemized. That
# is, if we have `exists w. t[v,w]` we treat it as `t<f(v)/w>`. In
# practice, though, we don't have to add the skolem function's
# arguments to the stratification graph, since `f` only occurs with
# argument `v`, which is a universal variable.  Instead, it's
# equivalent to add `w -> v` to `macro_dep_map`. The following
# procedure does this for a given formula.
#

def make_skolems(fmla,ast,pol,univs):
    global macro_dep_map
    if isinstance(fmla,il.Not):
        make_skolems(fmla.args[0],ast,not pol,univs)
    if isinstance(fmla,il.Implies):
        make_skolems(fmla.args[0],ast,not pol,univs)
        make_skolems(fmla.args[1],ast,pol,univs)
    is_e = il.is_exists(fmla)
    is_a = il.is_forall(fmla)
    if is_e and pol or is_a and not pol:
        fvs = set(il.free_variables(fmla))
        for u in univs:
            if u in fvs:
                for e in il.quantifier_vars(fmla):
                    macro_dep_map[e].extend(u)
    if is_e and not pol or is_a and pol:
        make_skolems(fmla.args[0],ast,pol,univs+list(il.quantifier_vars(fmla)))
    for arg in fmla.args:
        make_skolems(arg,ast,pol,univs)
    if isinstance(fmla,il.Ite):
        make_skolems(fmla.args[0],ast,not pol,univs)
    if isinstance(fmla,il.Iff) or (il.is_eq(fmla) and il.is_boolean(fmla.args[0])):
        make_skolems(fmla.args[0],ast,not pol,univs)
        make_skolems(fmla.args[1],ast,not pol,univs)

def create_strat_map(assumes,asserts,macros):
    """ Given a list of assumptions, assertions and macros, compute
    the stratification graph. The difference between assumes and
    asserts is that the free variables in assumes are treated as
    universally quantified, while the asserts are treated as
    negated.

    Each argument is a list of pairs `(fmla,ast)` where `fmla` is the
    formula and `ast` an ast giving the origin of the formula.

    """

    global universally_quantified_variables

    # Gather all the formulas in the VC.

    all_fmlas = [il.close_formula(pair[0]) for pair in assumes]
    all_fmlas.extend(il.Not(pair[0]) for pair in asserts)
    all_fmlas.extend(pair[0] for pair in macros)

    # Get the universally quantified variables. The free variables of
    # asserts and macros won't count as universal.

    universally_quantified_variables = il.universal_variables(all_fmlas)

    print 'universally_quantified_variables : {}'.format([str(v) for v in universally_quantified_variables])
    
    # Create an empty graph.

    strat_map = defaultdict(UFNode)
    arcs = []

    # Handle macros, as described above.

    create_macro_maps(assumes,asserts,macros,strat_map)

    # Simulate the Skolem functions that would be generated by AE alternations.

    for fmla,ast in assumes + macros + asserts:
        make_skolems(fmla,ast,True,[])

    # Construct the stratification graph by calling `map_fmla` on all
    # of the formulas in teh VC.

    for pair in assumes+asserts+macros:
        map_fmla(pair[1].lineno,pair[0],strat_map,arcs)

    show_strat_graph(strat_map,arcs)
    return strat_map,arcs

# This is just for debugging

def show_strat_graph(m,a):
    print 'nodes = {'
    for x,y in m.iteritems():
        z = find(y)
        if isinstance(x,tuple):
            print '({},{}) : {} -> {}'.format(x[0],x[1],y,z)
        else:
            print '{} : {} -> {}'.format(x,y,z)
    print '}'
    print 'arcs = {'
    for arc in a:
        print '(' + ','.join(str(x) for x in arc) + ')'
    print '}'
    
        



def get_unstratified_funs(assumes,asserts,macros):
    """ Take a list of assumes, assert and macros, and determines
    whether collectively they are in the FEU fragment. """

    # Alpha convert so that all the variables have unique names,

    vu = il.VariableUniqifier()
    
    def vupair(p):
        return (vu(p[0]),p[1])

    assumes = map(vupair,assumes)
    asserts = map(vupair,asserts)
    macros = map(vupair,macros)

    # Create the stratificaiton graph, as described above.

    strat_map,arcs = create_strat_map(assumes,asserts,macros)
    
    # Check for cycles in the stratification graph.

    cycle = iu.cycle(arcs, first = lambda x: x[0].id, second = lambda x: x[1].id)


    bad_interpreted = set()
    # for x,y in strat_map.iteritems():
    #     if isinstance(x,tuple) and (il.is_interpreted_symbol(x[0]) or x[0].name == '='):
    #         for w in y.variables:
    #             for v in list(find(macro_var_map[w]).univ_variables) + [w]:
    #                 if v in universally_quantified_variables:
    #                     if v.sort == x[0].sort.dom[x[1]]:
    #                         if il.has_infinite_interpretation(v.sort):
    #                             bad_interpreted.add(x[0])
    #                             break

    return cycle, bad_interpreted


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
        if not isinstance(ldf.formula,il.DefinitionSchema):
            if ldf.formula.defines() not in ilu.symbols_ast(ldf.formula.rhs()):
#                print 'macro : {}'.format(ldf.formula)
                macros.append((ldf.formula.to_constraint(),ldf))
            else: # can't treat recursive definition as macro
#                print 'axiom : {}'.format(ldf.formula)
                assumes.append((ldf.formula.to_constraint(),ldf))

    for ldf in im.module.labeled_axioms:
        if not ldf.temporal:
#            print 'axiom : {}'.format(ldf.formula)
            assumes.append((ldf.formula,ldf))

    for ldf in im.module.labeled_props:
        if not ldf.temporal:
#            print 'prop : {}{} {}'.format(ldf.lineno,ldf.label,ldf.formula)
            asserts.append((ldf.formula,ldf))

    for ldf in im.module.labeled_conjs:
        asserts.append((ldf.formula,ldf))
        assumes.append((ldf.formula,ldf))
    # TODO: check axioms, inits, conjectures

#    for x in assumes:
#        print 'assume: {}'.format(x[0])
#    for x in asserts:
#        print 'assert: {}'.format(x[0])
#    for x in macros:
#        print 'macro: {}'.format(x[0])
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
    if unstrat:
        msg += "\n\nNote: the following terms generate an infinite sequence of instantiations:\n"
        for arc in unstrat:
            msg += '  ' + str(arc[2]) + '\n'
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
    
def check_fragment(preconds_only=False):
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

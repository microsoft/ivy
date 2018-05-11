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

# The return value of `map_fmla` is a pair `(v,uvs)` where:
#
# -  `v` is `S_v` if the fmla is a universal variable, else None
# -  `uvs` is the set of `S_w` for universal variables `w` occurring *under* the
#    formula, that is, not at top level.

# Each macro is evaluated only once and memoized. The evaluation is an
# over-approximation, since its return value includes *all* of the
# universal variables that are be substituted into the macro
# parameters, and not just those substituted at any particular call
# site. This over-approximation is made to avoid expanding all the
# macros, which would be exponential.

# Macro expansion uses global maps macro_map, macro_value_map,
# macro_var_map and macro_dep_map.  These are explained below.

def map_fmla(lineno,fmla,strat_map,arcs):
    """ Add all of the subterms of `fmla` to the stratification graph. """

    global universally_quantified_variables
    global macro_var_map
    global macro_dep_map
    global macro_map
    global macro_val_map

    if il.is_binder(fmla):
        return map_fmla(lineno,fmla.body,strat_map,arcs)
    if il.is_variable(fmla):
        if fmla in universally_quantified_variables:
            if fmla not in strat_map:
                res = UFNode()
                strat_map[fmla] = res
            return strat_map[fmla],set()
        node,vs = macro_var_map.get(fmla,None), macro_dep_map.get(fmla,set())
        return node,vs
    nodes,uvs = iu.unzip_pairs([map_fmla(lineno,f,strat_map,arcs) for f in fmla.args])
    all_uvs = iu.union_of_list(uvs)
    all_uvs.update(n for n in nodes if n is not None)
    if il.is_eq(fmla):
        if all(x is not None for x in nodes):
            unify(*nodes)
        elif nodes[0] is not None:
            arcs.extend((v,nodes[0],fmla,lineno) for v in uvs[1])
        elif nodes[1] is not None:
            arcs.extend((v,nodes[1],fmla,lineno) for v in uvs[0])
        return None,all_uvs 
    if il.is_ite(fmla):
        if all(x is not None for x in nodes[1:]):
            unify(*nodes[1:])
        elif nodes[1] is not None:
            arcs.extend((v,nodes[1],fmla,lineno) for v in uvs[2])
        elif nodes[2] is not None:
            arcs.extend((v,nodes[2],fmla,lineno) for v in uvs[1])
        return nodes[1] or nodes[2],all_uvs
    if il.is_app(fmla):
        func = fmla.rep
        if not il.is_interpreted_symbol(func):
            if func in macro_value_map:
                return macro_value_map[func]
            if func in macro_map:
                defn = macro_map[func]
                res = map_fmla(defn.lineno,defn.formula.rhs(),strat_map,arcs)
                macro_value_map[func] = res
                return res
            for idx,node in enumerate(nodes):
                anode = strat_map[(func,idx)]
                if node is not None:
                    unify(anode,node)
                arcs.extend((v,anode,fmla,lineno) for v in uvs[idx])
        return None,all_uvs
    return None,all_uvs
                
# We treat macros (non-recursive definitions) as if they were
# syntactically expanded. However, since actually expanding them would
# be exponential, we instead compute the set of universally quantified
# variables that can be substituted under each macro parameter. This
# gives us an over-approximaiton of the variables dependencies of all
# call sites.
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
# In addition, we set up two maps for evaluating macros:
#
# - macro_map maps each symbol defined by a macro to its definition
#
# - macro_value_map is the memo table that maps each symbol defined by
#   a macro to the result of map_fmla for its right-hand-side.

# TODO: make sure macros are really listed in dependency order.

def create_macro_maps(assumes,asserts,macros,strat_map):
    global universally_quantified_variables
    global macro_var_map
    global macro_dep_map
    global macro_map
    global macro_value_map
    macro_map = dict()
    for _,lf in macros:
        macro_map[lf.formula.defines()] = lf
    macro_dep_map = defaultdict(set)
    macro_var_map = dict()
    macro_value_map = dict()
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
                            for u in ilu.used_variables_ast(v):
                                if u in universally_quantified_variables:
                                    macro_dep_map[w].add(strat_map[u])
                                if u in macro_var_map:
                                    macro_dep_map[w].add(macro_var_map[u])
                                if u in macro_dep_map:
                                    macro_dep_map[w].update(macro_var_map[u])
    # print 'macro_var_map: {'
    # for x,y in macro_var_map.iteritems():
    #     print '{} -> {}'.format(x,y)
    # print '}'
    # print 'macro_dep_map: {'
    # for x,y in macro_dep_map.iteritems():
    #     print '{} -> {}'.format(x,y)
    # print '}'

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

#    print 'universally_quantified_variables : {}'.format([str(v) for v in universally_quantified_variables])
    
    # Create an empty graph.

    strat_map = defaultdict(UFNode)
    arcs = []

    # Handle macros, as described above.

    create_macro_maps(assumes,asserts,macros,strat_map)

    # Simulate the Skolem functions that would be generated by AE alternations.

    for fmla,ast in assumes + macros + asserts:
        make_skolems(fmla,ast,True,[])

    # Construct the stratification graph by calling `map_fmla` on all
    # of the formulas in the VC. We don't include the macro definitions
    # here, because these are 'inlined' by `map_fmla`.

    for pair in assumes+asserts:
        map_fmla(pair[1].lineno,pair[0],strat_map,arcs)

#    show_strat_graph(strat_map,arcs)
    return strat_map,arcs

# Show a stratification graph. This is just for debugging.

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
    
        
def report_feu_error(text):
    raise iu.IvyError(None,"The verification condition is not in the fragment FEU.\n\n{}".format(text))

def report_cycle(cycle):
    if cycle is not None:
        report_feu_error("The following terms may generate an infinite sequence of instantiations:\n"+
                         '\n'.join('  ' + str(arc[3]) + str(arc[2]) for arc in cycle))

def report_interp_over_var(v,fmla,ast):
    report_feu_error('An interpreted symbol is applied to a universally quantified variable:\n'+
                     '{}{}'.format(ast.lineno,fmla))

def check_feu(assumes,asserts,macros):
    """ Take a list of assumes, assert and macros, and determines
    whether collectively they are in the FEU fragment, raising an error
    exception if not. """

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

    report_cycle(iu.cycle(arcs, first = lambda x: find(x[0]), second = lambda x: find(x[1])))

    for fmla,lf in assumes+asserts+macros:
        for app in ilu.apps_ast(fmla):
            if il.is_interpreted_symbol(app.rep):
                for v in app.args:
                    if il.is_variable(v) and il.has_infinite_interpretation(v.sort):
                        if v in universally_quantified_variables or v in macro_var_map:
                            report_interp_over_var(v,app,lf)
                    if il.is_app(v) and v.rep in macro_value_map and macro_value_map[v.rep][0] is not None:
                        report_interp_over_var(v,app,lf)
                        

    # for x,y in strat_map.iteritems():
    #     if isinstance(x,tuple) and (il.is_interpreted_symbol(x[0]) or x[0].name == '='):
    #         for w in y.variables:
    #             for v in list(find(macro_var_map[w]).univ_variables) + [w]:
    #                 if v in universally_quantified_variables:
    #                     if v.sort == x[0].sort.dom[x[1]]:
    #                         if il.has_infinite_interpretation(v.sort):
    #                             bad_interpreted.add(x[0])
    #                             break


# Here we try to extract all the assumes, asserts and macros that
# might wind up in the prover context when checking the current
# isolate. This is a bit conservative, since not all of these may wind
# up in the *same* prover context, and also a bit error-prone, since
# changes to the VC generation procedure by invalidate this code. On
# the whole it would probably be better to fragment check each prover
# context separately.

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

    
def check_fragment(preconds_only=False):
    if 'fo' not in im.logics():
        assumes,asserts,macros = get_assumes_and_asserts(preconds_only)
        check_feu(assumes,asserts,macros)

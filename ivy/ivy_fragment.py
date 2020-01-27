import ivy_actions as ia
import ivy_module as im
import ivy_logic as il
import ivy_utils as iu
import logic_util as lu
import ivy_logic_utils as ilu
import ivy_theory as thy
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
# Equality for uninterpreted sorts is treated as if we had the axioms
# of equality (reflexivity, symmetry, transitivity and congruence).
# To simulte this, we add the following constraints (from section 4.1,
# ibid):
#
#    | equality argument      |  constraint    |
#    |------------------------|----------------|
#    | v:s                    | S_s = S_v      |
#    | t[v]:s                 | S_v --> S_s    |
#
# Here, `S_s` is a special set of relevant terms associated with sort `s`. 
# This sort is represented in `strat_map` by a fake symbol '=' of sort `s`.
#
# We drop the constraint that `A_f,i = S_s` when `dom_f,j = s` from
# section 4.1, as this seems to be unnecessary and rules out some
# useful formulas.
#
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

# As a side effect, we check the conditions for the formula to be in
# the FAU fragment (see below). The argument `pol` indicates the
# number of negations under which the formula occurs. It is 0 for an
# even number, one for an odd number and None if the formula occurs
# under both an even number and an odd number of negations.

def map_fmla(lineno,fmla,pol):
    """ Add all of the subterms of `fmla` to the stratification graph. """

    global universally_quantified_variables
    global macro_var_map
    global macro_dep_map
    global macro_map
    global macro_val_map
    global strat_map
    global arcs

    if il.is_binder(fmla):
        return map_fmla(lineno,fmla.body,pol)
    if il.is_variable(fmla):
        if fmla in universally_quantified_variables:
            if fmla not in strat_map:
                res = UFNode()
                res.var = fmla
                strat_map[fmla] = res
            return strat_map[fmla],set()
        node,vs = macro_var_map.get(fmla,None), macro_dep_map.get(fmla,set())
        return node,vs
    reses = [map_fmla(lineno,f,il.polar(fmla,pos,pol)) for pos,f in enumerate(fmla.args)]
    nodes,uvs = iu.unzip_pairs(reses)
    all_uvs = iu.union_of_list(uvs)
    all_uvs.update(n for n in nodes if n is not None)
    if il.is_eq(fmla):
        if not il.is_interpreted_sort(fmla.args[0].sort):
            S_sigma = strat_map[il.Symbol('=',fmla.args[0])]
            for x,uv in zip(nodes,uvs):
                if x is not None:
                    unify(x,S_sigma)
                arcs.extend((v,S_sigma,fmla,lineno) for v in uv)
        else:
            check_interpreted(fmla,nodes,uvs,lineno,pol)
        return None,all_uvs 
    if il.is_ite(fmla):
        # S_sigma = strat_map[il.Symbol('=',fmla.args[1])]
        # for x,uv in zip(nodes[1:],uvs[1:]): 
        #     if x is not None:
        #         unify(x,S_sigma)
        #     arcs.extend((v,S_sigma,fmla,lineno) for v in uv)
        # TODO: treat ite as pseudo-macro: does this work?
        if nodes[1] and nodes[2]:
            unify(*nodes[1:])
        return nodes[1] or nodes[2],all_uvs
    if il.is_app(fmla):
        func = fmla.rep
        if not il.is_interpreted_symbol(func):
            if func in macro_value_map:
                return macro_value_map[func]
            if func in macro_map:
                defn,lf = macro_map[func]
                res = map_fmla(lf.lineno,defn.rhs(),None)
                macro_value_map[func] = res
                return res
            for idx,node in enumerate(nodes):
                anode = strat_map[(func,idx)]
                if node is not None:
                    unify(anode,node)
                arcs.extend((v,anode,fmla,lineno,idx) for v in uvs[idx])
        else:
            check_interpreted(fmla,nodes,uvs,lineno,pol)
        return None,all_uvs
    return None,all_uvs
                
# An interpreted symbol over a variable puts us outside the FEU
# fragment. However, the FAU fragment allows "arithmetic literals"
# of the form X = t, X < Y, X < t, t < X, where t is a ground term and
# the arguments are of integer sort. 
#
# Check that a given application of a symbol does not violate this
# rule. Takes the map_fmla results for the symbol arguments, and the
# lineno for error reporting purposes.

def check_interpreted(app,nodes,uvs,lineno,pol):
    for idx,(node,uv) in enumerate(zip(nodes,uvs)):
        if node is not None:
            if not is_arithmetic_literal(app,idx,nodes,uvs,pol):
                report_interp_over_var(app,lineno,node)


# Here, we determine whether a term is an arithmetic literal. To
# determine wheter the arguments are ground or universal variables, we
# use the result of map_fmla (that is, the top-level variable and
# under-variables). This accounts for the fact the macro expansion and
# and skolemization may introduce universals and skolemization may
# turn some variables into constants.

def is_arithmetic_literal(app,pos,nodes,uvs,pol):
    """ Given an application `app` of an interpreted symbol, with a variable
    in argument position `pos`, where `nodes` gives the top-level universals
    of the arguments and `uvs` gives the lower-level universals, determine
    whether `app` is an arithmetic literal.

    As a side effect, if both arguments of an arithmetic literal are universals,
    we unify them (per the rule in seciont 4 of ibid). 
    """

    if ((il.is_inequality_symbol(app.rep) or il.is_eq(app))
        and thy.has_integer_interp(app.args[0].sort)):
        if il.is_strict_inequality_symbol(app.rep,pol):
            if nodes[1-pos] is not None:
                unify(*nodes)
                return True
        # If `app` is an integer theory literal and the other argument is ground, we are OK
        if nodes[1-pos] is None and not uvs[1-pos]:
            return True
    return False

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

def create_macro_maps(assumes,asserts,macros):
    global universally_quantified_variables
    global macro_var_map
    global macro_dep_map
    global macro_map
    global macro_value_map
    global strat_map
    macro_map = dict()
    for df,lf in macros:
        macro_map[df.defines()] = (df,lf)
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
                mvs = macro_map[app.rep][0].args[0].args
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
    # print 'macro_map: {'
    # for x,y in macro_map.iteritems():
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
# skolem_map maps existential variables to the terms that bind them. 

skolem_map = {}

def make_skolems(fmla,ast,pol,univs):
    global macro_dep_map
    global strat_map
    global skolem_map
    if isinstance(fmla,il.Not):
        make_skolems(fmla.args[0],ast,not pol,univs)
        return
    if isinstance(fmla,il.Implies):
        make_skolems(fmla.args[0],ast,not pol,univs)
        make_skolems(fmla.args[1],ast,pol,univs)
        return
    is_e = il.is_exists(fmla)
    is_a = il.is_forall(fmla)
    if is_e and pol or is_a and not pol:
        fvs = set(il.free_variables(fmla))
        for u in univs:
            if u in fvs:
                for e in il.quantifier_vars(fmla):
                    skolem_map[e] = (fmla,ast)
                    macro_dep_map[e].add(strat_map[u])
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
    global strat_map
    global arcs

    # Gather all the formulas in the VC.

    all_fmlas = [(il.close_formula(x),y) for x,y in assumes]
    all_fmlas.extend((il.Not(x),y) for x,y in asserts)
    all_fmlas.extend(macros)

    # Get the universally quantified variables. The free variables of
    # asserts and macros won't count as universal. We keep track of the
    # line numbers of these variables for error messages.

    universally_quantified_variables = dict()
    for fmla,lf in all_fmlas:
        for v in il.universal_variables([fmla]):
            if (il.is_uninterpreted_sort(v.sort) or
                il.has_infinite_interpretation(v.sort)):
                universally_quantified_variables[v] = lf

    # print 'universally_quantified_variables : {}'.format([str(v) for v in universally_quantified_variables])
    
    # Create an empty graph.

    strat_map = defaultdict(UFNode)
    arcs = []

    # Handle macros, as described above.

    create_macro_maps(assumes,asserts,macros)

    # Simulate the Skolem functions that would be generated by AE alternations.

    for fmla,ast in all_fmlas:
        make_skolems(fmla,ast,True,[])

    # Construct the stratification graph by calling `map_fmla` on all
    # of the formulas in the VC. We don't include the macro definitions
    # here, because these are 'inlined' by `map_fmla`.

    for pair in assumes+asserts:
        map_fmla(pair[1].lineno,pair[0],0)

#    show_strat_graph(strat_map,arcs)

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
    raise iu.IvyError(None,"The verification condition is not in the fragment FAU.\n\n{}".format(text))

def get_node_sort(n):
    for t,m in strat_map.iteritems():
        if m is n:
            if isinstance(t,tuple):
                return t[0].sort.dom[t[1]]
            return t.sort
    assert False

def report_arc(arc):
    v,anode,fmla,lineno = arc[0:4]
    res = '\n' + str(lineno) + str(fmla)
    if len(arc) > 4:
        idx = arc[4]
        term = fmla.args[idx]
        res += '\n    (position {} is a function from '.format(idx) + str(get_node_sort(v)) + ' to ' + str(term.sort) + ')'
        if term in skolem_map:
            sm = skolem_map[term]
            res += '\n    ' + str(sm[1].lineno) + 'skolem function defined by:\n         ' + str(sm[0])  
    return res

def report_cycle(cycle):
    if cycle is not None:
        report_feu_error("The following terms may generate an infinite sequence of instantiations:\n"+
                         '\n'.join('  ' + report_arc(arc) for arc in cycle))

def report_interp_over_var(fmla,lineno,node):
    """ Report a violation of FAU due to a universal variable
    occurring as an argument position of an interpreted symbol, but
    not in an arithmetic literal. """

    # First, try to fibd the offending variable in the strat map

    var_msg = ''
    for v,n in strat_map.iteritems():
        if n is node:
            if v in universally_quantified_variables:
                lf = universally_quantified_variables[v]
                var_msg = '\n{}The quantified variable is {}'.format(lf.lineno,var_uniq.undo(v))
    report_feu_error('An interpreted symbol is applied to a universally quantified variable:\n'+
                     '{}{}'.format(lineno,var_uniq.undo(fmla))+var_msg)

def check_feu(assumes,asserts,macros):
    """ Take a list of assumes, assert and macros, and determines
    whether collectively they are in the FEU fragment, raising an error
    exception if not. """

    # Alpha convert so that all the variables have unique names,

    global var_uniq
    var_uniq = il.VariableUniqifier()
    
    def vupair(p):
        return (var_uniq(p[0]),p[1])

    assumes = map(vupair,assumes)
    asserts = map(vupair,asserts)
    macros = map(vupair,macros)

    # Create the stratificaiton graph, as described above.

    create_strat_map(assumes,asserts,macros)
    
    # Check for cycles in the stratification graph.

    report_cycle(iu.cycle(arcs, first = lambda x: find(x[0]), second = lambda x: find(x[1])))

    # for fmla,lf in assumes+asserts+macros:
    #     for app in ilu.apps_ast(fmla):
    #         if il.is_interpreted_symbol(app.rep) or is_eq(app) and il.is_interpreted_sort(app.args[0].sort):
    #             for v in app.args:
    #                 if il.is_variable(v) and il.has_infinite_interpretation(v.sort):
    #                     if v in universally_quantified_variables or v in macro_var_map:
    #                         report_interp_over_var(v,app,lf)
    #                 if il.is_app(v) and v.rep in macro_value_map and macro_value_map[v.rep][0] is not None:
    #                     report_interp_over_var(v,app,lf)
                        

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
            if (ldf.formula.defines() not in ilu.symbols_ast(ldf.formula.rhs())
                and not isinstance(ldf.formula.rhs(),il.Some)):
                # print 'macro : {}'.format(ldf.formula)
                macros.append((ldf.formula,ldf))
            else: # can't treat recursive definition as macro
                # print 'axiom : {}'.format(ldf.formula)
                assumes.append((ldf.formula.to_constraint(),ldf))

    for ldf in im.module.labeled_axioms:
        if not ldf.temporal:
            # print 'axiom : {}'.format(ldf.formula)
            assumes.append((ldf.formula,ldf))

    for ldf in im.module.labeled_props:
        if not ldf.temporal:
            # print 'prop : {}{} {}'.format(ldf.lineno,ldf.label,ldf.formula)
            asserts.append((ldf.formula,ldf))

    for ldf in im.module.labeled_conjs:
        asserts.append((ldf.formula,ldf))
        assumes.append((ldf.formula,ldf))

    for ldf in im.module.assumed_invariants:
        if not ldf.explicit:
            assumes.append((ldf.formula,ldf))


    # TODO: check axioms, inits, conjectures

    # for x in assumes:
    #     print 'assume: {}'.format(x[0])
    # for x in asserts:
    #     print 'assert: {}'.format(x[0])
    # for x in macros:
    #     print 'macro: {}'.format(x[0])
    return assumes,asserts,macros

    
def check_fragment(preconds_only=False):
    if 'fo' not in im.logics():
        assumes,asserts,macros = get_assumes_and_asserts(preconds_only)
        check_feu(assumes,asserts,macros)

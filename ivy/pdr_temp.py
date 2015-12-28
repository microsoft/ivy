#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#


refine_or_reverse = RefineOrReverse(...)

# create an ART in the analysis state with one node corresponding to the ivy initial

last_art_node = init_art_node = add_initial_node()

current_conj = get_invariant_conjecture_to_prove()

my_action = action_or(all_actions)

# test conjecture in initial

# the property is true in all frames and all "clauses" are pushed

while (true):

    # check inductiveness

    # if more than one frame...
    if last_art_node != init_art_node:

        try_cover(last_art_node,node_pred(last_art_node))  # tactic
        
        if is_covered(last_art_node):
            break
   
    # not inductive -- extend ART

    last_art_node = execute_action(last_ast_node,my_action,the_abstract_domain or abstract to top)

    # push some facts?

    recalculate(last_art_node, ???)

    new_goal = test_conjecture(current_conj,last_art_node)

    push(new_goal)

    while not stack_empty():   # or if goal is not vacuous
        
        current_goal = top_stack()

        if refuted_goal(current_goal):
            remove_from_stack(current_goal)
            continue

        if goal_art_node(current_goal) == init_art_node:
            raise ...

        dg = diagram(current_goal)

        if refine_or_reverse(dg):
            pass
            # dg is proved
        else:
            # new goal pushed
            pass

    # propagate phase

    for art_node in art_preorder_traversal():
        propagate(art_node)
            

def propagate(node):

    # does recacluate only strengthen?

    facts_to_check = facts(pred(art_node)) - facts(art_node)
    implied_facts = efficient_implied_facts(
        forward_image(facts(pred(art_node)), action(art_node)),
        facts_to_check
        )
    for fact in implied_facts:
        add_fact(art_node, fact)

    recalculate_art_node(art_node,check_fact_list(facts(pred(art_node)) - facts(art_node)))

(pred(art_node)),mode=strengthen)

    s = new_solver
    s.add(forward_image(facts(pred(art_node)), action(art_node)))
    for fact in facts(pred(art_node)) - facts(art_node):
        s.push()
        s.add(~fact)
        result = s.check()
        s.pop()
        if result == unsat:
            add_fact(art_node, fact)



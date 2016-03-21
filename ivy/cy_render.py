#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Module with functions that render different Ivy objects to graphs
for visualization with cytoscape.js.

The graphs are rendered to Python objects compatible with
cytoscape.js's JSON format.
"""

from itertools import product
from collections import defaultdict

from tactics_api import refuted_goal
from widget_cy_graph import CyElements


def get_shape(concept_name):
    # TODO: this is specific for the leader_demo. make this general
    return {
        '__Node': 'ellipse',
        '__ID': 'octagon',
    }.get(concept_name.split('!')[0], 'ellipse')


def get_transitive_reduction(widget, a, edges):
    """
    Return a list of (edge, source, target) of edges that should not
    be displayed due to transitive reduction (also reflexive reduction).
    """

    # filter only all_to_all edges for which transitive reduction is turned on
    edges = [x for x in edges if
             widget.edge_display_checkboxes[x[0]]['transitive'].value and
             a[('edge_info', 'all_to_all') + x]]

    # first hide all self edges
    result = [x for x in edges if x[1] == x[2]]
    edges = [x for x in edges if x[1] != x[2]]

    by_source = defaultdict(list)
    for edge, source, target in edges:
        by_source[(edge, source)].append(target)

    for edge, x, y in edges:
        for z in by_source[(edge, y)]:
            result.append((edge, x, z))

    return frozenset(result)

_label_prefix = {
    'node_necessarily': '',
    'node_necessarily_not': u'\u00AC', # negation sign
    'node_maybe': '?',
}

_label_prefix_equality = {
    'node_necessarily': '=',
    'node_necessarily_not': u'\u2260', # not equal sign
    'node_maybe': u'\u225F', # =? sign
}

def render_concept_graph(widget):
    """
    Render the result of concept_alpha to an annotated graph.

    The graph is represented using Python objects compatible with
    Cytoscape's JSON format.

    TODO: maybe this should be a method of ConceptSessionWidget
    """
    concept_session = widget.concept_session
    a = dict(concept_session.abstract_value)
    domain = concept_session.domain

    # treat custom_edge_info and custom_node_label
    custom = set()
    for tag in a.keys():
        if tag[0].startswith('custom_'):
            not_custom_tag = (tag[0][len('custom_'):],) + tag[1:]
            a[not_custom_tag] = a[tag]
            custom.add(tag[2:])

    # get information from the abstract value
    nodes = set()
    node_labels = set()
    edges = set()
    for tag in a:
        if tag[0] == 'node_info':
            nodes.add(tag[2])
        elif tag[0] == 'edge_info':
            nodes.add(tag[3])
            nodes.add(tag[4])
            edges.add(tag[2:])
        elif tag[0] == 'node_label':
            nodes.add(tag[2])
            node_labels.add(tag[3])
    nodes = sorted(nodes)
    node_labels = sorted(node_labels)
    edges = sorted(edges)

    g = CyElements()

    # add nodes
    non_existing_nodes = set()
    for node in nodes:
        if a[('node_info', 'none', node)]:
            non_existing_nodes.add(node)
            classes = ['non_existing']
            class_disp = 'non existing'
        elif a[('node_info', 'at_least_one', node)] and a[('node_info', 'at_most_one', node)]:
            classes = ['exactly_one']
            class_disp = 'exactly one'
        elif a[('node_info', 'at_least_one', node)]:
            classes = ['at_least_one']
            class_disp = 'at least one'
        elif a[('node_info', 'at_most_one', node)]:
            classes = ['at_most_one']
            class_disp = 'at most one'
        else:
            classes = ['node_unknown']
            class_disp = 'maybe non existing, maybe more than one'

        possible_splits = []
        label_lines = []
        for label_name in node_labels:
            if ('node_label', 'node_necessarily', node, label_name) not in a:
                # label not present, probably not well sorted, skip
                continue
            possible_splits.append(label_name)
            if a[('node_label', 'node_necessarily', node, label_name)]:
                k = 'node_necessarily'
            elif a[('node_label', 'node_necessarily_not', node, label_name)]:
                k = 'node_necessarily_not'
            else:
                k = 'node_maybe'
            if (widget.node_label_display_checkboxes[label_name][k].value is False and
                (node, label_name) not in custom):
                # don't add invisible labels
                continue
            if label_name.startswith('='):
                disp = _label_prefix_equality[k] + label_name[1:]
            else:
                disp = _label_prefix[k] + label_name
            label_lines.append(disp)

        actions = ([
            ('remove', widget.remove_concept),
            ('suppose empty', widget.suppose_empty),
            ('materialize', widget.materialize_node),
        ] + [
            ('split by {}'.format(x), widget.split, x)
            for x in possible_splits
        ] + [
            ('add {}'.format(name),
             widget.add_projection, name, concept)
            for name, concept in
            concept_session.get_projections(node)
        ])

        disp = node
        if '+' in disp or '-' in disp:
            # for concepts that are the result of splits, display just the sort
            disp = str(domain.concepts[node].sorts[0])
        label = '\n'.join([disp] + label_lines)
        info = '\n'.join(
            [
                node,
                str(domain.concepts[node]),
                class_disp,
            ] +
            label_lines
        )
        # cluster by sort in concrete models
        if '!' in node:
            cluster = node.split('!')[0].lower()
        else:
            cluster = None

        if hasattr(widget, 'apply_structure_renaming'):
            label = widget.apply_structure_renaming(label)
            info = widget.apply_structure_renaming(info)
            actions = [
                (widget.apply_structure_renaming(action[0]), ) + tuple(action[1:])
                for action in actions
            ]

        shape = get_shape(node)

        g.add_node(
            obj=node,
            label=label,
            classes=classes,
            short_info=info,
            long_info=info,
            events=[],
            actions=actions,
            locked=True,
            cluster=cluster,
            shape=shape,
        )

    # add edges
    hidden_by_transitive = get_transitive_reduction(widget, a, edges)
    for edge, source, target in edges:
        x = (edge, source, target)

        if (x in hidden_by_transitive and x not in custom):
            # don't draw edges hidden by transitive reduction
            continue

        if (source in non_existing_nodes or
            target in non_existing_nodes):
            # don't draw edges to non-existing nodes
            continue

        classes = []
        if a[('edge_info', 'none_to_none') + x]:
            classes.append('none_to_none')
        elif a[('edge_info', 'all_to_all') + x]:
            classes.append('all_to_all')
        else:
            classes.append('edge_unknown')

        if (widget.edge_display_checkboxes[edge][classes[0]].value is False and
            x not in custom):
            # don't add invisible edges
            continue

        if not a[('edge_info', 'none_to_none') + x]:
            classes += [
                c for c in [
                    'total',
                    'functional',
                    'surjective',
                    'injective',
                ] if a.get(('edge_info', c) + x)
            ]

        # TODO: custom edge labels
        labels = ['{}({}, {}):'.format(edge, source, target)]
        labels += [
            c.replace('_', ' ') for c in [
                'none_to_none',
                'all_to_all',
                'total',
                'functional',
                'surjective',
                'injective',
            ] if a.get(('edge_info', c) + x)
        ]

        if hasattr(widget, 'apply_structure_renaming'):
            labels[0] = widget.apply_structure_renaming(labels[0])

        g.add_edge(
            edge,
            source,
            target,
            label=edge,
            classes=classes,
            short_info='\n'.join(labels),
            long_info=[str(domain.concepts[edge])] + labels[1:],
            events=[],
            actions=[
                ('remove', widget.remove_concept),
                ('materialize +', widget.materialize_edge, True),
                ('materialize -', widget.materialize_edge, False),
            ],
        )

    return g


def render_rg(rg, node_events, node_actions):
    """
    Render an ivy_arg.AnalysisGraph object

    node_actions is a function that maps nodes to action lists
    """
    g = CyElements()

    # add nodes for states
    for s in rg.states:
        if s.is_bottom():
            classes = ['bottom_state']
        else:
            classes = ['state']
        events = node_events
        actions = node_actions(s)
        g.add_node(
            obj=s,
            label=str(s.id),
            classes=classes,
            #short_info=str(s),
            #long_info=str(s),
            short_info=str(s.id),
            long_info=[str(x) for x in s.clauses.to_open_formula()],
            events=events,
            actions=actions,
            locked=True,
        )

    # add edges for transitions
    for source, op, label, target in rg.transitions:
        if label == 'join':
            classes = ['transition_join']
            label = 'join'
            info = 'join'
        else:
            classes = ['transition_action']
            label = label if label != str(op) else ''
            info = str(op)
        g.add_edge(
            op,
            source,
            target,
            label=label,
            classes=classes,
            short_info=info,
            long_info=info,
            events=[],
            actions=[],
        )

    # add edges for covering
    for covered, by in rg.covering:
        g.add_edge(
            'cover',
            covered,
            by,
            label='',
            classes=['cover'],
            short_info='',
            long_info='',
            events=[],
            actions=[],
        )

    return g


def render_proof_stack(proof_stack, node_events, node_actions):
    """
    Render a proof.ProofGoalStack object
    """
    g = CyElements()

    # add nodes
    for goal in proof_stack.stack:
        classes = ['proof_goal']
        short_info = "At ARG node {}".format(goal.node.id)
        if refuted_goal(goal):
            classes += ['refuted']
            short_info += ' (refuted)'
        long_info = [short_info, str(goal.formula)]
        g.add_node(
            obj=goal,
            label=str(goal.id),
            classes=classes,
            short_info=short_info,
            long_info=long_info,
            events=node_events,
            actions=node_actions(goal),
            locked=True,
        )

    # add edges
    for goal in proof_stack.stack:
        if goal.parent is not None:
            g.add_edge(
                'parent',
                goal,
                goal.parent,
                label='',
                classes=['proof_edge'],
                short_info='',
                long_info='',
                events=[],
                actions=[],
            )

    return g

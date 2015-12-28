#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Use DOT to layout a graph for cytoscape.js

TODO: add support for middle points in edges
"""

from __future__ import division

from collections import deque, defaultdict

from pygraphviz import AGraph

from ivy_utils import topological_sort


def cubic_bezier_point(p0, p1, p2, p3, t):
    """
    https://en.wikipedia.org/wiki/B%C3%A9zier_curve#Cubic_B.C3.A9zier_curves
    """
    a = (1.0 - t)**3
    b = 3.0 * t * (1.0 - t)**2
    c = 3.0 * t**2 * (1.0 - t)
    d = t**3
    return {
        "x": a * p0["x"] + b * p1["x"] + c * p2["x"] + d * p3["x"],
        "y": a * p0["y"] + b * p1["y"] + c * p2["y"] + d * p3["y"],
    }


def square_distance_to_segment(p, p1, p2):
    v0 = (p["x"] - p1["x"], p["y"] - p1["y"])
    v1 = (p2["x"] - p1["x"], p2["y"] - p1["y"])
    v0sq = v0[0] * v0[0] + v0[1] * v0[1]
    v1sq = v1[0] * v1[0] + v1[1] * v1[1]
    prod  = v0[0] * v1[0] + v0[1] * v1[1]
    v2sq = prod * prod / v1sq
    if prod < 0:
        return v0sq
    elif v2sq < v1sq:
        return v0sq - v2sq
    else:
        v3 = (v0[0] - v1[0], v0[1] - v1[1])
        return v3[0] * v3[0] + v3[1] * v3[1]


def approximate_cubic_bezier(p0, p1, p2, p3, threshold=1.0, limit=1024):
    """
    Return an series of points whose segments approximate the given
    bezier curve
    """
    threshold_squared = threshold ** 2
    points = {  # dict mapping t values to points
        0.0: p0,
        1.0: p3,
    }
    to_check = deque([(0.0, 1.0)])
    while len(to_check) > 0 and len(points) < limit:
        l, r = to_check.popleft()
        pl = points[l]
        pr = points[r]
        m = (l + r) / 2.0
        pm = cubic_bezier_point(p0, p1, p2, p3, m)
        if square_distance_to_segment(pm, pl, pr) > threshold_squared:
            points[m] = pm
            to_check.append((l, m))
            to_check.append((m, r))
    return [points[t] for t in sorted(points.keys())]


def get_approximation_points(bspline):
    """
    Retrurn a series of points whose segments approximate the given
    bspline
    """
    result = []
    for i in range(0, len(bspline) - 3, 3):
        result.extend(approximate_cubic_bezier(
            bspline[i], bspline[i+1], bspline[i+2], bspline[i+3],
            threshold=4.0,
            limit=100,
        )[:-1])
    result.append(bspline[-1])
    return result


def _to_position(st):
    sp = st.split(',')
    assert len(sp) == 2
    return {
        "x": float(sp[0]),
        "y": -float(sp[1]),
    }


def _to_edge_position(st):
    """
    http://www.graphviz.org/doc/info/attrs.html#k:splineType
    """
    sp = st.split()
    result = {}

    if sp[0].startswith('e,'):
        result["arrowend"] = _to_position(sp[0][2:])
        sp = sp[1:]

    if sp[0].startswith('s,'):
        result["arrowstart"] = _to_position(sp[0][2:])
        sp = sp[1:]

    result["bspline"] = [_to_position(x) for x in sp]
    result["approxpoints"] = get_approximation_points(result["bspline"])
    # print "approxpoints: ", len(result["approxpoints"])

    return result


def dot_layout(cy_elements):
    """
    Get a CyElements object and augment it (in-place) with positions,
    widths, heights, and spline data from a dot based layout.

    Returns the object.
    """
    elements = cy_elements.elements
    g = AGraph(directed=True, strict=False)

    # make transitive relations appear top to bottom
    # TODO: make this not specific to leader example
    elements = list(elements)
    nodes_by_id = dict(
        (e["data"]["id"], e)
        for e in elements if e["group"] == "nodes"
    )
    order = [
        (nodes_by_id[e["data"]["source"]], nodes_by_id[e["data"]["target"]])
        for e in elements if
        e["group"] == "edges" and
        e["data"]["obj"] in ('reach', 'le')
    ]
    elements = topological_sort(elements, order, lambda e: e["data"]["id"])

    # add nodes to the graph
    for e in elements:
        if e["group"] == "nodes":
            g.add_node(e["data"]["id"], label=e["data"]["label"].replace('\n', '\\n'))

    # TODO: remove this, it's specific to leader_demo
    weight = {
        'reach': 10,
        'le': 10,
        'id': 1,
    }
    constraint = {
        'pending': False,
    }

    # add edges to the graph
    for e in elements:
        if e["group"] == "edges":
            g.add_edge(
                e["data"]["source"],
                e["data"]["target"],
                e["data"]["id"],
                weight=weight.get(e["data"]["obj"], 0),
                #constraint=constraint.get(e["data"]["obj"], True),
            )

    # add clusters
    clusters = defaultdict(list)
    for e in elements:
        if e["group"] == "nodes" and e["data"]["cluster"] is not None:
            clusters[e["data"]["cluster"]].append(e["data"]["id"])
    for i, k in enumerate(sorted(clusters.keys())):
        g.add_subgraph(
            name='cluster_{}'.format(i),
            nbunch=clusters[k],
        )

    # now get positions, heights, widths, and bsplines
    g.layout(prog='dot')
    for e in elements:
        if e["group"] == "nodes":
            attr = g.get_node(e["data"]["id"]).attr
            e["position"] = _to_position(attr['pos'])
            e["data"]["width"] = 72 * float(attr['width'])
            e["data"]["height"] = 72 * float(attr['height'])

        elif e["group"] == "edges":
            attr = g.get_edge(e["data"]["source"], e["data"]["target"], e["data"]["id"]).attr
            e["data"].update(_to_edge_position(attr['pos']))
    g.draw('g.png')

    return cy_elements

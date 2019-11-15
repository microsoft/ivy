#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Use DOT to layout a graph for cytoscape.js

TODO: add support for middle points in edges
"""

from __future__ import division

from collections import deque, defaultdict

import platform
if True or platform.system() == 'Windows':
    from ivy_graphviz import AGraph
else:
    from pygraphviz import AGraph


from ivy_utils import topological_sort

import ivy_utils as iu

# import pygraphviz

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
    global y_origin
    sp = st.split(',')
    assert len(sp) == 2, st
    return {
        "x": float(sp[0]),
        "y": y_origin-float(sp[1]),
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


def _to_coord_list(st):
    """ create a sequence of positions from a dot-generated string """
    nums = st.split(',')
    pairs = [','.join((nums[2*i],nums[2*i+1])) for i in range(len(nums)//2)]
    return map(_to_position,pairs)


def dot_layout(cy_elements,edge_labels=False,subgraph_boxes=False,node_gt=None):
    """
    Get a CyElements object and augment it (in-place) with positions,
    widths, heights, and spline data from a dot based layout.

    edge_labels is true if labels should appear on edges
    subgraph_boxes is true if boxes should be drawn around subgraphs

    Returns the object.
    """
    elements = cy_elements.elements

#    g = AGraph(directed=True, strict=False)
    g = AGraph(directed=True, strict=False, forcelabels=True)

    # make transitive relations appear top to bottom

    elements = list(elements)
    nodes_by_id = dict(
        (e["data"]["id"], e)
        for e in elements if e["group"] == "nodes"
    )
    order = [
        (nodes_by_id[e["data"]["source"]], nodes_by_id[e["data"]["target"]])
        for e in elements if
        e["group"] == "edges" and
        "transitive" in e["data"] and
        e["data"]["transitive"]
    ]
    elements = topological_sort(elements, order, lambda e: e["data"]["id"])

    # get the node id's and stable sort them by cluster
    # the idea here is to convert the graph into a dag by sorting
    # the nodes, then reversing the back edges. In particular, we try to make
    # all the edges between two clusters go in the same direction so clustering
    # doesn't result in horizontal edges, which dot renders badly.

    sorted_nodes = [e["data"]["id"] for e in elements if e["group"] == "nodes"]
    sorted_nodes = sorted(enumerate(sorted_nodes),key = lambda x: (nodes_by_id[x[1]]["data"]["cluster"],x[0]))
    sorted_nodes = [y for idx,y in sorted_nodes]
    node_key = dict((id,idx) for idx,id in enumerate(sorted_nodes))

    if node_gt is None:
        node_gt = lambda X,y:False
    else:
        node_gt = lambda x,y: node_key[x] > node_key[y] 

    # add nodes to the graph
    for e in elements:
        if e["group"] == "nodes" and e["classes"]  != 'non_existing':
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
#            kwargs = {'weight': weight.get(e["data"]["obj"], 0)},
            kwargs = {'label':e["data"]["label"]}  if edge_labels else {}
            if node_gt(e["data"]["source"],e["data"]["target"]):
                g.add_edge(
                    e["data"]["target"],
                    e["data"]["source"],
                    e["data"]["id"],
                    dir = 'back',
                    **kwargs
                    #constraint=constraint.get(e["data"]["obj"], True),
                    )
            else:
                g.add_edge(
                    e["data"]["source"],
                    e["data"]["target"],
                    e["data"]["id"],
                    **kwargs
                    #constraint=constraint.get(e["data"]["obj"], True),
                    )

    # add clusters
    clusters = defaultdict(list)
    for e in elements:
        if e["group"] == "nodes" and e["data"]["cluster"] is not None and e["classes"]  != 'non_existing':
            clusters[e["data"]["cluster"]].append(e["data"]["id"])
    for i, k in enumerate(sorted(clusters.keys())):
        g.add_subgraph(
            name='cluster_{}'.format(i),
            nbunch=clusters[k],
            rank='min',
        )

    # now get positions, heights, widths, and bsplines
    g.layout(prog='dot')

    # get the y origin. we want the top left of the graph to be a
    # fixed coordinate (hopefully (0,0)) so the graph doesn't jump when
    # its height changes. Unfortunately, pygraphviz has a bug a gives
    # the wrong bbox, so we compute the max y coord.

#    bbox = pygraphviz.graphviz.agget(g.handle,'bb')

    global y_origin
    y_origin = 0.0
    for n in g.nodes():
        top = float(n.attr['pos'].split(',')[1]) + float(n.attr['height'])/2
        if top > y_origin:
            y_origin = top
    if subgraph_boxes:
        for sg in g.subgraphs():
            top = float(sg.graph_attr['bb'].split(',')[3])
            if top > y_origin:
                y_origin = top

    for e in elements:
        if e["group"] == "nodes" and e["classes"]  != 'non_existing':
            attr = g.get_node(e["data"]["id"]).attr
            e["position"] = _to_position(attr['pos'])
            e["data"]["width"] = 72 * float(attr['width'])
            e["data"]["height"] = 72 * float(attr['height'])

        elif e["group"] == "edges":
            if node_gt(e["data"]["source"],e["data"]["target"]):
                attr = g.get_edge(e["data"]["target"], e["data"]["source"], e["data"]["id"]).attr
                pos = attr['pos']
                pe = pos.split()
                ppe = pe[1:]
                ppe.reverse()
                pos = ' '.join([pe[0].replace('s','e')] + ppe)
            else:
                attr = g.get_edge(e["data"]["source"], e["data"]["target"], e["data"]["id"]).attr
                pos = attr['pos']
            e["data"].update(_to_edge_position(pos))
            if edge_labels and e["data"]["label"] != '':
                e["data"]["lp"] = _to_position(attr['lp'])
#    g.draw('g.png')

    if subgraph_boxes:
        for sg in g.subgraphs():
            box = cy_elements.add_shape(sg.name,classes='subgraphs')
            coords = _to_coord_list(sg.graph_attr['bb'])
            box["data"]["coords"] = coords

    return cy_elements

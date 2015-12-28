#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Cytoscape.js styles:

concept_style - for concept graphs
arg_style - for abstract reachability graph
proof_style - for proof stack/graph

"""


concept_style = [
    {
        "selector": "node",
        "style": {
            "content": "data(label)",
            "text-wrap": "wrap",
            # "font-family": "helvetica",
            "font-size": "14px",
            "text-outline-width": "3px",
            "text-outline-color": "#888",
            "text-valign": "center",
            "color": "#fff",
            "width": "data(width)",
            "height": "data(height)",
            # when cytoscape.js 2.5 comes out, could use
            # "width":"label"
            # https://github.com/cytoscape/cytoscape.js/issues/1041
            "border-color": "#000",
            # "shape": "octagon",
            "shape": "data(shape)",
            "background-color": "#888",
        },
    },

    #  node classes

    {
        "selector": "node.non_existing",
        "style": {
	    "display": "none",
        },
    },

    {
        "selector": "node.exactly_one",
        "style": {
            "border-width": "4px",
            "border-style": "solid",
        },
    },

    {
        "selector": "node.at_least_one",
        "style": {
            "border-width": "8px",
            "border-style": "double",
        },
    },

    {
        "selector": "node.at_most_one",
        "style": {
            "border-width": "3px",
            "border-style": "dotted",
        },
    },

    {
        "selector": "node.node_unknown",
        "style": {
            "border-width": "0px",
        },
    },

    #  edge classes

    {
        "selector": "edge",
        "style": {
            #"content": "data(label)",
            "target-arrow-shape": "triangle",
	    #"target-arrow-fill": "hollow",
	    #"source-arrow-fill": "hollow",
	    "target-arrow-fill": "filled",
	    "source-arrow-fill": "filled",

        },
    },

    {
        "selector": "edge.none_to_none",
        "style": {
            "width": "4px",
            "line-style": "dashed",
            "target-arrow-shape": "triangle",
            #"source-arrow-shape": "tee",
            #"mid-source-arrow-shape": "tee",
            #"mid-target-arrow-shape": "triangle",
	    "target-arrow-fill": "filled",
	    "source-arrow-fill": "filled",
        },
    },

    {
        "selector": "edge.all_to_all",
        "style": {
            "width": "4px",
            "line-style": "solid",
        },
    },

    {
        "selector": "edge.edge_unknown",
        "style": {
            "width": "4px",
            "line-style": "dotted",
        },
    },


    {
        "selector": "edge.total",
        "style": {
            "source-arrow-shape": "circle",
            "source-arrow-fill": "filled",
        },
    },

    {
        "selector": "edge.functional",
        "style": {
            "source-arrow-shape": "square",
        },
    },

    {
        "selector": "edge.injective",
        "style": {
            "target-arrow-shape": "triangle-backcurve",
        },
    },

    {
        "selector": "edge.surjective",
        "style": {
            "target-arrow-fill": "filled",
        },
    },

    # selection

    {
        "selector": "node:selected",
        "style": {
            "overlay-opacity": "0.2",
        },
    },

    {
        "selector": "edge:selected",
        "style": {
            "overlay-opacity": "0.2",
        },
    },

]


arg_style = [
    {
        "selector": "node",
        "style": {
            "content": "data(label)",
            "text-wrap": "wrap",
            # "font-family": "helvetica",
            # "font-size": "14px",
            "text-outline-width": "3px",
            "text-outline-color": "#888",
            "text-valign": "center",
            "color": "#fff",
            "width": "50",
            "height": "50",
            "border-color": "#000",
            # "shape": "octagon",
            "background-color": "#888",
        },
    },

    #  node classes

    {
        "selector": "node.state",
        "style": {
        },
    },

    {
        "selector": "node.bottom_state",
        "style": {
            "background-color": "#000",
            "text-outline-color": "#000",
        },
    },

    #  edge classes

    {
        "selector": "edge",
        "style": {
            "content": "data(label)",
            "width": "4px",
            "line-style": "solid",
            "edge-text-rotation": "none",
        },
    },

    {
        "selector": "edge.transition_join",
        "style": {
            "target-arrow-shape": "triangle-backcurve",
        },
    },

    {
        "selector": "edge.transition_action",
        "style": {
            "target-arrow-shape": "triangle",
        },
    },

    {
        "selector": "edge.cover",
        "style": {
            "content": "",
            "target-arrow-shape": "triangle",
            "line-style": "dashed",
        },
    },


    # selection

    {
        "selector": "node:selected",
        "style": {
            "overlay-opacity": "0.2",
        },
    },

    {
        "selector": "edge:selected",
        "style": {
            "overlay-opacity": "0.2",
        },
    },

]


proof_style = [
    {
        "selector": "node",
        "style": {
            "content": "data(label)",
            "text-wrap": "wrap",
            # "font-family": "helvetica",
            # "font-size": "14px",
            "text-outline-width": "3px",
            "text-outline-color": "#888",
            "text-valign": "center",
            "color": "#fff",
            "width": "50",
            "height": "50",
            "border-color": "#000",
            # "shape": "octagon",
            "background-color": "#888",
        },
    },

    {
        "selector": "edge",
        "style": {
            "target-arrow-shape": "triangle",
        },
    },

    # node classes

    {
        "selector": "node.refuted",
        "style": {
            "background-color": "#000",
            "text-outline-color": "#000",
        },
    },

    # selection

    {
        "selector": "node:selected",
        "style": {
            "overlay-opacity": "0.2",
        },
    },

    {
        "selector": "edge:selected",
        "style": {
            "overlay-opacity": "0.2",
        },
    },

]

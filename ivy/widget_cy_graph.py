#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This is a custom IPython widget that displays a graph using
cytoscape.js
"""

from time import sleep

from IPython.html import widgets
from IPython.utils.traitlets import Unicode, Any, Bool, Tuple
from IPython.utils.py3compat import string_types


def _object_key(x):
    return str(id(x))

_object_prefix = 'CY_OBJECT_'

def _is_user_object(x):
    return str(type(x)).startswith('<class ')


class CyGraphWidget(widgets.DOMWidget):
    _view_module = Unicode('nbextensions/ivy/js/widget_cy_graph', sync=True)
    _view_name = Unicode('CyGraphView', sync=True)

    _cy_elements = Tuple(sync=True) # cy_elements defined below
    cy_style = Tuple(sync=True)
    cy_layout = Any(None, sync=True)
    selected = Tuple((), sync=True)  # see elements for format
    info_area = Any(sync=True)

    def __init__(self, **kwargs):
        """Constructor"""
        super(CyGraphWidget, self).__init__(**kwargs)

        self.background_color = 'rgb(192,192,255)'

        self.on_msg(self._handle_cy_msg)

        self._obj_to_key = dict()
        self._key_to_obj = dict()

    cy_elements = property(lambda self: self._cy_elements)
    @cy_elements.setter
    def cy_elements(self, value):
        assert type(value) is CyElements
        elements = value.elements
        value.elements = None # prevents future use of this graph
        if self._cy_elements != elements:
            # clear the dictionaries to free memory
            # TODO: figure out why this sometime gives errors. in the
            # meantime this is commented out and we have a memory
            # leak.
            # self._obj_to_key = dict()
            # self._key_to_obj = dict()
            self.selected = [] # clear selection
            self._cy_elements = elements

    def _ele_to_tuple(self, ele):
        if ele['group'] == 'nodes':
            return (ele['data']['obj'],)
        else:
            return (ele['data']['obj'], ele['data']['source_obj'],  ele['data']['target_obj'])

    @property
    def elements(self):
        """
        All graph elements as a list of tuples. Nodes are represented by
        (obj, ) and edges by (obj, source_obj, target_obj)
        """
        return [self._ele_to_tuple(ele) for ele in self.cy_elements]

    def _handle_cy_msg(self, _, content):
        content = self._trait_from_json(content)
        if content['type'] == 'callback':
            content['callback'](*content['args'])

    def execute_new_cell(self, code):
        """
        Causes a new code cell to appear in the notebook and get exectued
        """
        self.send({
            "method": "execute_new_cell",
            "code": code,
        })

    # maintain references to python functions and objects of user
    # defined classes

    def _trait_to_json(self, x):
        x = super(CyGraphWidget, self)._trait_to_json(x)
        if callable(x) or _is_user_object(x):
            if x not in self._obj_to_key:
                k = _object_key(x)
                self._obj_to_key[x] = k
                self._key_to_obj[k] = x
            else:
                assert x == self._key_to_obj[self._obj_to_key[x]]
            return _object_prefix + self._obj_to_key[x]
        else:
            return x # Value must be JSON-able

    def _trait_from_json(self, x):
        x = super(CyGraphWidget, self)._trait_from_json(x)
        if isinstance(x, string_types) and x.startswith(_object_prefix):
            # we support object references at any level in a hierarchy
            # trusting that a string 'CY_OBJECT_XXXX' will not appear
            # out in the wild
            return self._key_to_obj[x[len(_object_prefix):]]
        else:
            return x


class CyElements(object):
    """
    A CyElements object is used to create graphs compatible with
    cytoscape.js's JSON format, that is then set to the
    CyGraphWidget's cy_elements property.

    Once a CyElements instance has been assigned to a CyGraphWidget, it
    becomes invalid for any future access.

    Graph elements (edges and nodes) have the following properties:

    obj: a python object that correspond to this the element. Must be
    hashable. For nodes, obj must be unique. For edges, the tuple
    (obj, source_obj, target_obj) must be unique. Used to reference
    nodes when adding edges, and used for reference in callbacks and
    in CyGraphWidget.selected.

    label: the display label of the element

    classes: space delimited string or list of strings used by style

    short_info: short string to display at the element's tooltip

    long_info: string or list of strings to display in the additional
    info area for the element

    events: list of (event_name, callback, *args), where event_type is
    a cytoscape.js event names and callback has signature:
    callback(obj[, source obj, target_obj], *args)

    actions: list of (action_name, callback, *args) where action_name
    is a string and callback has signature:
    callback(obj[, source obj, target_obj], *args).
    These will be displayed in a context menu.
    """

    def __init__(self):
        self.elements = []
        self.node_id = dict()
        self.edge_id = dict()

    def add_node(self, obj, label=None, classes=[], short_info='',
                 long_info='', events=[], actions=[], locked=True, cluster=None, shape='ellipse'):
        """
        Add a node. See class docstring for details.
        """
        assert self.elements is not None, "This object us not reusable"
        if label is None:
            label = str(obj)
        if not isinstance(classes, basestring):
            classes = ' '.join(str(x) for x in classes)
        nid = 'n{}'.format(len(self.node_id))
        assert obj not in self.node_id, "obj must be unique"
        self.node_id[obj] = nid
        self.elements.append({
            'group': 'nodes',
            'data': {
                'id': nid,
                'obj': obj,
                'label': label,
                'short_info': short_info,
                'long_info': long_info,
                'events': events,
                'actions': actions,
                'cluster': cluster,
                'shape': shape,
            },
            'classes': classes,
            'locked': locked,
        })

    def add_edge(self, obj, source_obj, target_obj, label=None,
                 classes=[], short_info='', long_info='', events=[],
                 actions=[], locked=True):
        """
        Add an edge. See class docstring for details.

        To add an edge, you must first add both source and target
        nodes.
        """
        assert self.elements is not None, "This object us not reusable"
        if label is None:
            label = str(obj)
        if not isinstance(classes, basestring):
            classes = ' '.join(str(x) for x in classes)
        eid = 'e{}'.format(len(self.edge_id))
        assert (obj, source_obj, target_obj) not in self.edge_id
        self.edge_id[(obj, source_obj, target_obj)] = eid
        self.elements.append({
            'group': 'edges',
            'data': {
                'id': eid,
                'source': self.node_id[source_obj],
                'target': self.node_id[target_obj],
                'obj': obj,
                'source_obj': source_obj,
                'target_obj': target_obj,
                'label': label,
                'short_info': short_info,
                'long_info': long_info,
                'events': events,
                'actions': actions,
            },
            'classes': classes,
        })

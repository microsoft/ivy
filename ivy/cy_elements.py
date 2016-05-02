#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

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
        self.shape_id = dict()

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
                 actions=[], locked=True, transitive=False):
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
                'transitive': transitive,
            },
            'classes': classes,
        })

    def add_shape(self, obj, label = '', classes=[], locked=True, shape='rectangle', coords=''):
        """
        Add a node. See class docstring for details.
        """
        assert self.elements is not None, "This object us not reusable"
        if not isinstance(classes, basestring):
            classes = ' '.join(str(x) for x in classes)
        sid = 's{}'.format(len(self.shape_id))
        self.shape_id[obj] = sid
        res = {
            'group': 'shapes',
            'data': {
                'id': sid,
                'obj': obj,
                'label': label,
                'shape': shape,
                'coords' : coords,
            },
            'classes': classes,
            'locked': locked,
        }
        self.elements.append(res)
        return res


# Some convenience functions

def get_group(element):
    return element['group']

def get_classes(element):
    return element['classes']

def get_shape(element):
    return element['data']['shape']

def get_label(element):
    return element['data']['label']

def get_id(element):
    return element['data']['id']

def get_obj(element):
    return element['data']['obj']

def get_source_obj(element):
    return element['data']['source_obj']

def get_target_obj(element):
    return element['data']['target_obj']

def get_coords(element):
    return element['data']['coords']

def get_shape(element):
    return element['data']['shape']

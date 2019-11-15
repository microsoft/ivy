# This is an interface to pydot that replaces pygraphviz, which is
# difficult to install on Windows.

import pydot
import tempfile
import os
from subprocess import Popen, PIPE

## Work around a bug in pydot parser

def add_elements(g, toks, defaults_graph=None,
                 defaults_node=None, defaults_edge=None):

    if defaults_graph is None:
        defaults_graph = {}
    if defaults_node is None:
        defaults_node = {}
    if defaults_edge is None:
        defaults_edge = {}

    for elm_idx, element in enumerate(toks):

        if isinstance(element, (pydot.Subgraph, pydot.Cluster)):

            pydot.dot_parser.add_defaults(element, defaults_graph)
            g.add_subgraph(element)

        elif isinstance(element, pydot.Node):

            pydot.dot_parser.add_defaults(element, defaults_node)
            g.add_node(element)

        elif isinstance(element, pydot.Edge):

            pydot.dot_parser.add_defaults(element, defaults_edge)
            g.add_edge(element)

        elif isinstance(element, pydot.dot_parser.ParseResults):

            for e in element:
                add_elements(g, [e], defaults_graph,
                             defaults_node, defaults_edge)

        elif isinstance(element, pydot.dot_parser.DefaultStatement):

            if element.default_type == 'graph':

                g.obj_dict['attributes'].update(element.attrs)

            elif element.default_type == 'node':

                defaults_node.update(element.attrs)

            elif element.default_type == 'edge':

                defaults_edge.update(element.attrs)

            else:
                raise ValueError(
                    'Unknown DefaultStatement: {s}'.format(
                         s=element.default_type))

        elif isinstance(element, pydot.dot_parser.P_AttrList):

            g.obj_dict['attributes'].update(element.attrs)

        else:
            raise ValueError(
                'Unknown element statement: {s}'.format(s=element))

# pydot.dot_parser.add_elements = add_elements

# work around some pydot parser bugs

def fix_parsed_graph(g):
    for n in g.get_node('graph'):
        g.attr.update(n.attr)
    g.del_node('graph')
    g.del_node('node')
    g.del_node('edge')
    for l in g.obj_dict['nodes'].values():
        for n in l:
            fix_attrs(n)
    for l in g.obj_dict['edges'].values():
        for e in l:
            fix_attrs(e)
    fix_attrs(g.obj_dict)
    if 'bb' not in g.attr:
        g.attr['bb'] = "0,0,0,0" # empty graphs won't get bounding boxes
    for sg in g.get_subgraphs():
        fix_parsed_graph(sg)

def fix_attrs(t):
    t['attributes'] = dict((x,y.strip('"').replace('\\\n','')) for x,y in t['attributes'].iteritems())

# Work around pydot printing bug by putting quotes around labels

def fix_labels(kwargs):
    if 'label' in kwargs:
        kwargs['label'] = '"' + kwargs['label'] + '"'
    return kwargs

class AGraph(object):
    def __init__(self,**kwargs):
        self.g = pydot.Dot(**kwargs)
    def add_node(self,name,**kwargs):
        return self.g.add_node(pydot.Node(name,**fix_labels(kwargs)))
    def add_edge(self,src,dst,id,**kwargs):
        e = pydot.Edge(src,dst,id=id,**fix_labels(kwargs))
        return self.g.add_edge(e)
    def add_subgraph(self,nbunch=None,name=None,**kwargs):
        res = pydot.Subgraph(graph_name=name)
        if nbunch:
            ids = set(nbunch)
            edges = self.g.obj_dict['edges']
            sub_edges = res.obj_dict['edges']
            for n in self.g.get_node_list():
                if n.get_name() in ids:
                    self.g.del_node(n)
                    res.add_node(n)
            for e in self.g.get_edge_list():
                src,dst = e.get_source(), e.get_destination()
                if src in ids and dst in ids:
                    self.g.del_edge(src,dst)
                    res.add_edge(e)
        self.g.add_subgraph(res)
    def layout(self,prog='dot'):
        tmp_fd, tmp_name = tempfile.mkstemp()
#        print 'temp_name={}'.format(tmp_name)
        os.close(tmp_fd)
        self.g.write(tmp_name)
        process = Popen(['dot','-Tdot',tmp_name], stdout=PIPE)
        txt,_ = process.communicate()
        exit_code = process.wait()
#        txt = self.g.create(prog=prog,format='dot')
        self.g =  pydot.dot_parser.parse_dot_data(txt)[0]
        fix_parsed_graph(self.g)
    def nodes(self):
        res = self.g.get_node_list()
        for sub in self.g.get_subgraphs():
            res.extend(sub.get_node_list())
        return res
    def get_edge(self,src,dst,id,g = None):
        g = g or self.g
        for e in g.get_edge(src,dst):
            if e.attr['id'] == id:
                return e
        for sg in g.get_subgraphs():
            e = self.get_edge(src,dst,id,sg)
            if e is not None:
                return e
        return None
    def get_node(self,name,g = None):
        g = g or self.g
        for e in g.get_node(name):
            return e
        for sg in g.get_subgraphs():
            e = self.get_node(name,sg)
            if e is not None:
                return e
        return None
    def subgraphs(self):
        return self.g.get_subgraphs()
    

    
    def __str__(self):
        return str(self.g)

pydot.Common.attr = property(lambda self: self.obj_dict['attributes'])
pydot.Subgraph.graph_attr = property(lambda self: self.obj_dict['attributes'])
pydot.Subgraph.name = property(lambda self: self.get_name())


if __name__ == "__main__":
    g = AGraph()
    g.add_node('1',label='foo')
    g.add_node('2',label='bar')
    g.add_edge('1','2','e1')
    g.add_subgraph(name='cluster_1',nbunch=['1','2'])
    g.add_node('3',label='foo')
    g.add_node('4',label='bar')
    g.add_edge('3','4','e1')
    g.add_subgraph(name='cluster_2',nbunch=['3','4'])
    print g
    g.layout()
    print g
    print 'nodes: {}'.format(g.g.get_node_list())
    for n in g.nodes():
        print n
    print g.get_edge('1','2','e1')
    print g.get_node('1')
    for sg in g.subgraphs():
        print sg.graph_attr['bb']



# Union-find data structure for stratification check

class UFNode(object):
    """
    A sort variable, to be replaced by an arbitrary sort.

    The instance property is used to implement union find, and it can
    either be None, another UFNode object, or a sort object.

    """
    def __init__(self):
        global ufidctr
        self.instance = None
        self.id = ufidctr
        ufidctr += 1
    def __str__(self):
        return str(self.id) 
    def __repr__(self):
        return str(self.id)
    def __hash__(self):
        return self.id
    def __eq__(self,other):
        return self.id == other.id


ufidctr = 0

def find(x):
    """
    Find the representative of a node
    """
    if x.instance is None:
        return x
    else:
        # collapse the path and return the root
        x.instance = find(x.instance)
        return x.instance

def unify(s1, s2):
    """
    Unify nodes s1 and s2.
    """
    if s1 is None or s2 is None:
        return

    s1 = find(s1)
    s2 = find(s2)

    if s1 != s2:
        s1.instance = s2



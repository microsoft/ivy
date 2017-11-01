import parser1 as p1

# These are the semantic classes for Python expressions

class PyArg(p1.Format):
    def __init__(self,lhs,rhs):
        if isinstance(rhs,list):
            rhs = PyList(rhs)
        elif isinstance(rhs,str):
            rhs = PyStr(rhs)
        self.lhs,self.rhs = lhs,rhs
  
class PyApply(p1.Format):
    def __init__(self,func,args = []):
        self.func,self.args = func,args
    def find(self,argname):
        return next (x.rhs for x in self.args if x.lhs == argname)

class PyList(p1.Format):
    def __init__(self,elems):
        self.elems = elems
    
class PyStr(p1.Format):
    def __init__(self,val):
        self.val = val
    def get(self,fld,default=None):
        return self.val.replace('\\','\\\\').replace("''","\\'") if fld == 'val' else p1.Format.get(self,fld,default)
    
# This is an alternative semantics that a Python expressions. The
# Python expression, when evaluated, should produce the default
# semantics.

class PyExprSemantics(p1.SemanticsContext):
    def __call__(self,cls,flds):
        return PyApply(cls,[PyArg(x,y) for x,y in flds.iteritems()])
    def isinst(self,obj,cls):
        return isinstance(obj,self.getclass(cls))
#    def isinst(self,obj,cls):
#        return obj.func == cls


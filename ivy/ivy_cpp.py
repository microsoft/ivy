#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

#
# Representations of various C++ constructs, including files, types,
# classes, statements and so on.
#


class CppFile(object):
    """ Writing code lines to a file. Keeps track of indentation. """

    def __init__(self,filename,mode='w'):
        self.filename = filename
        self.mode = mode
        self.file = open(filename,mode)
        self.indent = 0
    def close(self):
        self.file.close()
    def begin_scope():
        self.indent += 1
    def end_scope():
        self.indent += 1
    def write(self,code):
        """ Append string to file. Each line of string is indented. """
        self.write()

# Writing C++ objects the result. The objects can
# be text strings (representing code) or other C++ objects
# defined below. 

class CppText(object):
    def __init__(self):
        self.code = []
    def close(self):
        pass
    def write(self,code):
        self.code.append(code)
    def get(self,indent=0):
        return '\n'.join(indent*'    '+l for c in self.code for l in str(c).split('\n') )
    def get_file(self):
        """ Just concatenate all the code elements as strings. This is for compatibility with
        old code in ivy_to_cpp that emits partial code lines as strings """
        return ''.join(map(str,self.code))

class DeadCode(object):
    def write(self,code):
        assert False,"Cannot write code here"
    
temp_counter = 0

def get_temp():
    global temp_counter
    res = 'tmp{}'.format(temp_counter)
    temp_counter += 1
    return res

class Context(object):
    def __enter__(self):
        self.old_temp_counter = temp_counter
        self.enter()
        return self

    def __exit__(self,exc_type, exc_val, exc_tb):
        self.exit()
        global temp_counter
        temp_counter = self.old_temp_counter
        return False # don't block any exceptions
    

class CppContext(Context):
    """ A C++ context. This contains objects in various scopes:

    globals: header scope
    impls: implementation file scope
    members: class declaration scope
    locals: code local variables
    expr: current expression

    This is a conext object. To make it the current context,
    do this:

    with context_object:
       ...
    
    """

    def __init__(self):
        self.globals = CppText()
        self.impls = CppText()
        self.members = self.globals
        self.locals = DeadCode()
        self.expr = CppText()
        self.classname = None
        self.global_includes = []
        self.impl_includes = []
        self.once_globals = set()

    def enter(self):
        global context
        self.old = context
        context = self

    def exit(self):
        global context
        context = self.old

context = None  # The current C++ context

def add_global(code):
    """ Adds code to the current global (header) context. """
    context.globals.write(code)

def add_once_global(code):
    """ Adds code once to the current global (header) context. """
    if code not in context.once_globals:
        context.globals.write(code)
        context.once_globals.add(code)

def add_impl(code):
    """ Adds code to the current implementation context. """
    context.impls.write(code)

def add_member(code):
    """ Adds code to the current member context. """
    context.members.write(code)

def add_local(code):
    """ Adds code to the current local context. """
    context.locals.write(code)

def add_expr(code):
    """ Adds code to the current expression context. """
    context.expr.write(code)

def current_classname():
    """ Returns the name of the current class (i.e., the current scope
    for member declarations). """
    return context.classname

def add_header(name):
    context.global_includes.append(name)
    

class CppType(Context):
    """ This base class repressents a C++ type.
    """
    def instantiate(self,name,initializer=None):
        """ Returns a declaration for a symbol of this type """
        if initializer:
            return '{} {}={};'.format(self.short_name(),name,initializer.get())
        return '{} {};'.format(self.short_name(),name)

class CppInt64(CppType):
    """ Represents a 64-bit signed integer type """
    def short_name(self):
        return 'long'
    def long_name(self):
        return 'long'
    def declare(self):
        pass # built-in type

class CppVoid(CppType):
    """ Represents the C++ void type """
    def short_name(self):
        return 'void'
    def long_name(self):
        return 'void'
    def declare(self):
        pass # built-in type

def relname(classname,membername):
    """ Returns a name for a member of a certain class in the current context.
    If the named class *is* the current context, then this is just the member name,
    else it is the full name. """
    return membername if current_classname() == classname else fullname(classname,membername)

def fullname(classname,membername):
    """ Returns the full name of a member of a given class. If the
    classname is None (which refers to the global scope) then this is
    just the membername. """
    return (classname + '::' + membername) if classname else membername

class CppClass(CppType):
    """ Represents a C++ class with a given name. 
    
    A CppClass is a context, which you can open like this:

    with cppclass:
        ...

    Within this context, all members delcarations become members of
    the class. 
    
    """
    def __init__(self,classname,baseclass=None):
        self.members = CppText()
        self.classname = classname
        self.parent = current_classname()
        self.baseclass = baseclass
        self.declare()
    def declare(self):
        add_member(self)
    def short_name(self):
        return relname(self.parent,self.classname)
    def long_name(self):
        return fullname(self.parent,self.classname)
    def __str__(self):
        base = '' if self.baseclass is None else (' : public '+self.baseclass+' ')
        with self:
            return "class " + self.classname + base + "{\npublic:\n" + self.members.get(1) + "\n};"
    def enter(self):
        global context
        self.old_members = context.members
        self.old_classname = context.classname
        context.members = self.members
        context.classname = (context.classname + '::' + self.classname) if context.classname else self.classname
    def exit(self):
        global context
        context.members = self.old_members
        context.classname = self.old_classname

class CppClassName(Context):
    """ Conext that sets the current class name. This is just for backward compatibility.
    """
    def __init__(self,classname):
        self.classname = classname
    def enter(self):
        global context
        self.old_classname = context.classname
        context.classname = self.classname
    def exit(self):
        global context
        context.classname = self.old_classname


class CppArrFunType(CppType):
    """ Represents a C++ array or function type"""
    def short_name(self):
        return relname(self.parent,self.name) if self.name else self.long_name()
    def long_name(self):
        assert self.name, "C++ array and function types cannot be named!"
    def declare(self):
        self.parent = current_classname()
        if self.name:
            add_member(self)
    def suffix(self):
        return ''
    def prefix(self):
        return ''
    def initstr(self,initializer):
        '={};'.format(initializer) if initializer else ';'
    def instantiate_long(self,name,initializer=None):
        return '{} {}{}{}{}'.format(self.cpptype.short_name(),self.prefix(),name,self.suffix(),self.initstr(initializer))
    def __str__(self):
        return 'typedef ' + self.instantiate_long(self.name)
    def instantiate(self,name,initializer=None):
        return CppType.instantiate(self,name) if self.name and not initializer  else self.instantiate_long(name,initializer)

class CppArray(CppArrFunType):
    """ Represents and an array of cpptype of given dimensions"""
    def __init__(self,cpptype,dims,name=None):
        self.cpptype = cpptype
        self.dims = dims
        self.name = name
        self.declare()
    def suffix(self):
        return ''.join('[{}]'.format(d) for d in self.dims)
        
class CppFunction(CppArrFunType):
    """ Represents a C++ function type with argument types and an array of cpptype of given dimensions"""
    def __init__(self,cpptype,argtypes,name=None):
        self.cpptype = cpptype
        self.argtypes = argtypes
        self.name = name
        self.declare()
    def suffix(self,names = None):
        if names is None:
            names = ['arg{}'.format(idx) for idx,x in enumerate(self.argtypes)]
        return '(' + ','.join(t.instantiate(n)[:-1] for t,n in zip(self.argtypes,names)) + ')'
    def initstr(self,initializer):
        return ('{\n' + initializer.get(1) + '\n}') if initializer else ';'

class CppReference(CppArrFunType):
    """ Represents the C++ type cpptype& (i.e., a reference type)"""
    def __init__(self,cpptype,name=None,const=False):
        self.cpptype = cpptype
        self.name = name
        self.const = const
        self.declare()
    def long_name(self):
        return self.cpptype.short_name() + '&'
    def prefix(self):
        return 'const &' if self.const else '&'
    
class TypeDef(CppType):
    """ Represents typedef oldtype newname; """
    def __init__(self,oldtype,newname):
        self.oldtype = oldtype
        self.name = name
    def declare(self):
        self.parent = current_classname()
        if self.name:
            add_member(self)
    def short_name(self):
        return relname(self.parent,self.name) if self.name else self.long_name()
    def long_name(self):
        return self.oldtype.long_name()
    def __str__(self):
        return 'typedef {} {};'.format(self.long_name(),self.name)

class CppVector(TypeDef):
    """ Represents stl::vector<cpptype>"""
    def __init__(self,cpptype,name=None):
        self.cpptype = cpptype
        self.name = name
        self.declare()
    def long_name(self):
        return 'std::vector<' + self.cpptype.short_name() + '> ';
    def declare(self):
        self.parent = current_classname()
        add_header('<vector>')
        if self.name:
            add_member(self)
    
class CppMember(Context):
    """ Represents a member of a C++ class """
    def __init__(self,cpptype,name,static=False,inline=False):
        self.cpptype = cpptype
        self.name = name
        self.parent = current_classname()
        self.initializer = None
        self.scope.write(self)
    def __str__(self):
        return self.cpptype.instantiate(self.name,self.initializer)
    def ref(self):
        return relname(self.parent,self.name)
    @property
    def scope(self):
        return context.members
    def enter(self): 
        global context
        assert self.scope and self.scope.code[-1] is self
        assert self.initializer is None
        self.initializer = CppText()
        del self.scope.code[-1]
        if isinstance(self.cpptype,CppFunction):
            self.old_locals = context.locals
            context.locals = self.initializer
        else:
            self.old_expr = context.expr
            context.expr = self.initializer
    def exit(self):
        global context
        if isinstance(self.cpptype,CppFunction):
            context.locals = self.old_locals
        else:
            context.expr = self.old_expr
        self.scope.code.append(self)

class CppLocal(CppMember):
    @property
    def scope(self):
        return context.locals

class CppScope(Context):
    def __init__(self):
        self.code = CppText()
        add_local(self)
    def __str__(self):
        return '{\n' + self.code.get(1) + '\n}' 
    def ref(self):
        assert False,"cannot reference a C++ scope"
    def enter(self): 
        global context
        self.old_locals = context.locals
        context.locals = self.code
    def exit(self):
        global context
        context.locals = self.old_locals
    

if __name__ == "__main__":

    with CppContext():
        CppMember(CppInt64(),"foo")
        CppMember(CppVoid(),"bar")
        CppMember(CppArray(CppInt64(),[42]),"arr")
        arrt = CppArray(CppInt64(),[42],"baz");
        CppMember(arrt,"arr2")
        CppMember(CppFunction(CppVoid(),[CppInt64()]),"fun")
        CppMember(CppReference(CppInt64()),"intr")
        ft = CppFunction(CppReference(CppInt64()),[CppInt64()],"funtype")
        CppMember(ft,"fvar")
        with CppClass("myclass"):
            with CppMember(CppInt64(),"foo"):
                add_expr("0")
            myvec = CppVector(arrt,"myvec")
            CppMember(myvec,"bar")
            with CppMember(CppFunction(CppInt64(),[CppInt64()]),"fun"):
                loc = CppLocal(CppInt64(),get_temp())
                with CppScope():
                    loc2 = CppLocal(CppInt64(),get_temp())
                loc3 = CppLocal(CppInt64(),get_temp())

        with CppClass("other_class"):
            CppMember(myvec,"bif")
            
        print 'header:'
        print context.globals.get()
        print 'impl:'
        print context.impls.get()
        

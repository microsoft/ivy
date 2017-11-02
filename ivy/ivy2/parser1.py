#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# This file contains a set of class that implement a primitive
# parser/printer, used in the stage 1 compiler.

import re 

# This exception indicates a parsing error

class NoParse(Exception):
    pass

# This exception indicates an unparsing error

class NoSer(Exception):
    pass

# These are some primitive datatypes (currently unused)

class Class(object):
    @property
    def fields(self):
        return []

class Unit(Class):
    def __init__(self,text):
        pass

class Number(Class):
    def __init__(self,num):
        self.num = int(num)  
    def __str__(self):
        return str(self.num)

# This is the base class for all the semantic classes that the parser
# generates. The semantic classes are expected to have a constructor
# that takes a collection of keyword arguments.  These arguments can
# be queried using the "get" method. The default version of this
# method just looks up the argument in the object's dictionary.

class Format(object):
    def get(self,key,default=None):
        return self.__dict__.get(key,default)
    def fieldnames(self):
        return list(self.__dict__)
    def fields(self):
        return [y for y in ((x,self.__dict__[x]) for x in self.fieldnames()) if y is not None]
    
# This context class defines a default whitespace format.  Anything
# matching this format is ignored between tokens. The whitespace
# format should always match the empty string, unless you actually
# want to require whitespace between tokens.

# Notice that the whitespace pattern is capture at the time a format
# rule is constructed, not at parse time. This makes it possible to
# use different definitions of whitespace in different contexts.

whitespace = None

class WhiteSpace(object):
    def __init__(self,fmt):
        self.fmt = fmt
    def __enter__(self):
        global whitespace
        self.old_fmt = whitespace
        whitespace = self.fmt
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global whitespace
        whitespace = self.old_fmt
        return False # don't catch the exception

# This is the current structure we are building. Field assignments
# executed during parsing are made to this structure.

structure = None

class Structure(object):
    def __init__(self,strct):
        self.strct = strct
    def __enter__(self):
        global structure
        self.old_strct = structure
        structure = self.strct
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global structure
        structure = self.old_strct
        return False # don't catch the exception


# The Exact format matches a given string "text" exactly (possibly
# preceded by whitespace). The argument "cls" is the name of the
# corresponding semantic class, which defaults to "str". The class "cls"
# must be capable of initializing itself from a string and converting itself
# to a string with the method __str__.

# In the "text" argument, pairs of single quotes are reduced to one
# single quote. This allows single quotes to be escaped inside quoted
# strings. In addition, the sequences '\n' and '\t' are conevrted to
# newline and tab characters respectively. Exact could be expanded to
# handle more escaping conventions.

# Notice that Exact is a meta-semantic class. That is, it is a
# semantic class for the meta-grammar, i.e., the grammar of grammar
# descriptions. As such, it provides two methods:
#
# Method "des" deserializes an object using this format, reading
# tokens from an object called "rdr".
#
# Method "ser" serializes an object using this format, writing tokens
# to an object called "wtr".
#


class Exact(Format):
    def __init__(self,cls=None,text=None):
        assert text is not None
        self.cls,self.text = cls,text
        self.whitespace = whitespace
        self.rtext = text.replace("''","'").replace('\\n','\n').replace('\\t','\t')
    def fieldnames(self):
        return ['cls','text']
    def des(self,rdr):
        with rdr.chk():
            if self.whitespace is not None and not no_white:
                self.whitespace.des(rdr)
            t = rdr.read(len(self.rtext))
            if t == self.rtext:
                return self.cls(t) if self.cls is not None else t
            else:
                raise NoParse
    def ser(self,wtr,obj):
        if obj is not None and str(obj) != self.rtext:
            print obj
            raise NoSer
        wtr.write(self.rtext)
        if hasattr(self.whitespace,'dflt') and not no_white:
            wtr.write(self.whitespace.dflt)
            

# The RegEx format is similar to Exact, but matches a Python regular
# expression (possibly preceded by whitespace). 

class RegEx(Format):
    def __init__(self,cls=None,exp=None,dflt=None):
        assert exp is not None
        self.cls,self.exp,self.dflt = cls,exp,dflt
        self.whitespace = whitespace
        self.rexp = re.compile(exp.replace("''","'"),re.DOTALL)
    def fieldnames(self):
        return ['cls','exp','dflt']
    def des(self,rdr):
        with rdr.chk():
            if self.whitespace is not None and not no_white:
                self.whitespace.des(rdr)
            t = rdr.read_regex(self.rexp)
            return self.cls(t) if self.cls is not None else t
    def ser(self,wtr,obj):
        if not isinstance(obj,str):
            raise NoSer
        wtr.write(str(obj))
        if hasattr(self.whitespace,'dflt') and not no_white:
            wtr.write(self.whitespace.dflt)
            
# The format class NoWhite cancels the default whitespace in its argument. This is
# useful for defining literal formats in which space characters are
# significant. Operationally, it uses a context class to temporal set the flag "no_white"


class NoWhite(Format):
    def __init__(self,fmt):
        self.fmt = fmt
        self.whitespace = whitespace
    def fieldnames(self):
        return ['fmt']
    def des(self,rdr):
        if self.whitespace is not None:
            self.whitespace.des(rdr)
        with NoWhiteContext():
            return self.fmt.des(rdr)
    def ser(self,wtr,obj):
        with NoWhiteContext():
            self.fmt.ser(wtr,obj)
        if hasattr(self.whitespace,'dflt'):
            wtr.write(self.whitespace.dflt)

no_white = False

class NoWhiteContext(object):
    def __enter__(self):
        global no_white
        self.old_nw = no_white
        no_white = True
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global no_white
        no_white = self.old_nw
        return False # don't catch the exception

# The List format matches a list of items. Three deilimiters can optionally be
# provided: left, delim and right. The format "left", if given, is required at
# the beginning of the list. The format "delim", if given, is required between
# elements. The format 'right', if given, is required at the end of the list.

# The left and right delimiters are currently unused and could
# reasonable by removed.

class List(Format):
    def __init__(self,fmt,left=None,delim=None,right=None,min=None,max=None):
        self.fmt,self.left,self.delim,self.right,self.min,self.max = fmt,left,delim,right,min,max
    def des(self,rdr):
        res = []
        with rdr.chk():
            if self.left is not None:
                self.left.read(rdr)
            while True:
                if res != [] and self.delim is not None:
                    try:
                        self.delim.des(rdr)
                    except NoParse:
                        break
                try:
                    res.append(self.fmt.des(rdr))
                except NoParse:
                    if self.delim is not None:
                        raise NoParse
                    break
            if self.right is not None:
                self.right.read(rdr)
            if self.max is not None and len(res) < self.min or self.max is not None and len(res) > self.max:
                raise NoParse
            return res
    def ser(self,wtr,obj):
        if self.left is not None:
            self.left.ser(wtr,None)
        first = True
        for elem in obj:
            if self.delim is not None and not first:
                self.delim.ser(wtr,None)
            self.fmt.ser(wtr,elem)
            first = False
        if self.right is not None:
            self.right.ser(wtr,None)

# An Assign format assigns the value of its argument (having format
# "fmt") to a field "fld" of the current structure. This is the
# primary way in which semantic objects are created.

class Assign(Format):
    def __init__(self,fld,fmt):
        self.fld, self.fmt = fld,fmt
    def des(self,rdr):
        global structure
        assert structure is not None
        assert self.fld not in structure
        structure[self.fld] = self.fmt.des(rdr)
    def ser(self,wtr,obj):
        global structure
        val = structure.get(self.fld,None)
        if self.fld == 'fields':
            print "fields: {}".format(val)
            print structure.__dict__
        if val is not None:
            self.fmt.ser(wtr,val)

# An Option element is optional. If it is present, assignments in
# child element are applied to the current structure. If not present,
# it has no effect.

class Option(Format):
    def __init__(self,elem):
        self.elem = elem
    def des(self,rdr):
        try:
            self.elem.des(rdr)
        except NoParse:
            pass
    def ser(self,wtr,obj):
        self.elem.ser(wtr,obj)  # TODO: this is wrong

# An Alt elements provide a choice amongst a collection of
# elements. In case of ambiguity, the choice among matching child
# elements is arbitrary. In the current implementation, the first
# match is taken and no attempt is made to backtrack to alternative
# choices. This means that the order of alternatives
# matters. Generally speaking, you should put alternatives that parse
# longer strings first.

class Alt(Format):
    def __init__(self,elems):
        self.elems = elems
    def des(self,rdr):
        for elem in self.elems:
            try:
                return elem.des(rdr)
            except NoParse:
                pass
        raise NoParse
    def ser(self,wtr,obj):
        for elem in self.elems:
            try:
#                print "trying: {}".format(elem)
                elem.ser(wtr,obj)
                return
            except NoSer:
#                print "failed: {}".format(elem)
                pass
        print "cannot deser: {}".format(obj)

# A Seq element requires its child elements to be present in the given
# order. Multiple assignments to a fields are not allowed in a
# sequence.

class Seq(Format):
    def __init__(self,elems):
        self.elems = elems
    def des(self,rdr):
        flds = dict()
        with rdr.chk():
            with Structure(flds):
                for f in self.elems:
                    f.des(rdr)
        structure.update(flds)
    def ser(self,wtr,obj):
        for elem in self.elems:
            elem.ser(wtr,obj)

# A Bag element allows its child elements to be present in any order,
# or not present.  Multiple assignments are allowed to list-valued
# fields. There assignments are merged by concatenation.

class Bag(Format):
    def __init__(self,elems):
        self.elems = elems
    def des(self,rdr):
        def tryall(flds):
            for elem in self.elems:
                try:
                    with Structure(flds):
                        elem.des(rdr)
                    if all(x == [] for x in flds.values()):
                        break   # ignore an empty parse
                    return
                except NoParse:
                    pass
            raise NoParse
        flds = dict()
        def merge_fields(new_flds):
            for name,val in new_flds.iteritems():
                if isinstance(val,list) and name in flds:
                    flds[name].extend(val)
                else:
                    flds[name] = val
        with rdr.chk():
            while True:
                try:
                    new_flds = dict()
                    tryall(new_flds)
                    merge_fields(new_flds)
                except NoParse:
                    structure.update(flds)
                    return
    def ser(self,wtr,obj):
        for elem in self.elems:
            elem.ser(wtr,obj)

# This base class sets the current semantics

class SemanticsContext(object):
    def __enter__(self):
        global semantics
        self.oldsem = semantics
        semantics = self
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        global semantics
        semantics = self.oldsem
        return False # don't catch the exception

# The "semantics" is used to construct semantic objects. The default
# semantics create instance of a Pythion class in the global scope
# with the given name. The fields of the current structure are passed
# as keyword arguments to the constructor of this class.

class DefaultSemantics(SemanticsContext):
    def __init__(self,module=None):
        self.module = module
    def getclass(self,cls):
        module = globals() if self.module is None else self.module
        if isinstance(cls,str):
            assert cls in module,cls
            cls = module[cls]
        return cls
    def __call__(self,cls,flds):
        try:
            return self.getclass(cls)(**flds)
        except TypeError:
            print "wrong arguments to {}: {}".format(cls,
                 ",".join(x+':'+type(y).__name__ for x,y in flds.iteritems()))
            raise NoParse
    def isinst(self,obj,cls):
        return isinstance(obj,self.getclass(cls))

semantics = DefaultSemantics()

# A Struct format builds a semantic object. It creates a structure (a
# map from fields to values, and parses its arguemnt using this
# structure. Then it calls the current semantics to build a semantic
# object of the given class using these fields as keyword arguments.
# When serializing an object, Struct calls the method "isinst"
# provided by the current semantics to determine is the object is in
# fact an instance of the given semantic class. Note that if different
# alternative parses produce the same semantic class, there will be
# ambiguity in serializing semantics objects and a serialization error
# may occur.

class Struct(Format):
    def __init__(self,cls,fmt):
        self.cls,self.fmt = cls,fmt
    def des(self,rdr):
        flds = dict()
        with rdr.chk():
            with Structure(flds):
              self.fmt.des(rdr)
#            print self.cls
#            return self.cls(**flds)
              return semantics(self.cls,flds)
    def ser(self,wtr,obj):
#        print "struct trying: {} {}".format(self.cls,type(obj))
        if semantics.isinst(obj,self.cls):
            with Structure(obj):
                wtr.nest()
                self.fmt.ser(wtr,None)
                wtr.unnest()
        else:
#            print "struct failed"
            raise NoSer

# A meta format converts its argument to a meta value. For example, a
# meta structure (class MetaStruct) has a field "cls" that indicates
# its class, and "args" which is an association list given all the
# field names and values.  Meta formats are useful for converting to
# and from generic formats like S-expression or XML.

# A name/value pair
class MetaField(Format):
    def __init__(self,name,value):
        self.name,self.value = name,value

# An S-record
class MetaStruct(Format):
    def __init__(self,cls,args):
        self.cls,self.args = cls,args
    
# A meta list
class MetaList(Format):
    def __init__(self,elems):
        self.elems = elems

# A meta list
class MetaString(Format):
    def __init__(self,val):
        self.val = val

# A meta format
class Meta(Format):
    def __init__(self,fmt):
        self.fmt = fmt
    def des(self,rdr):
        flds = dict()
        with rdr.chk():
            with Structure(flds):
                thing = self.fmt.des(rdr)
                if isinstance(thing,MetaStr):
                    return thing.val
                if isinstance(thing,MetaList):
                    return thing.elems
                return semantics(flds['cls'],dict((x.name,x.value) for x in flds['args']))
    def ser(self,wtr,obj):
        if isinstance(obj,str):
            obj = MetaString(obj)
        elif isinstance(obj,list):
            obj = MetaList(obj)
        else:
#        print "struct trying: {} {}".format(self.cls,type(obj))
            if not hasattr(obj,'fields'):
                print 'structure: {}'.format(structure)
            obj = MetaStruct(type(obj).__name__,(MetaField(x,y) for x,y in obj.fields()))
        with Structure(obj):
            wtr.nest()
            self.fmt.ser(wtr,obj)
            wtr.unnest()


# A Rule defines non-terminal "lhs" symbol as a format "rhs".

class Rule(Format):
    def __init__(self,lhs,rhs):
        self.lhs,self.rhs = lhs,rhs


# A Grammar is a list of Rules. A grammar is also a context object, so
# you can set it as the current grammar using "with".

grammar = None

class Grammar(Format):
    def __init__(self,rules):
        self.rules = rules
        self.fmtdct = dict((r.lhs,r.rhs) for r in rules)
    def fieldnames(self):
        return ['rules']
    def __enter__(self):
        global grammar
        self.old_fmtdct = grammar
        grammar = self.fmtdct
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        grammar = self.old_fmtdct
        return False # don't catch the exception
    
# A non-terminal is a reference to a Rule by name. When serializing
# and deserializing, is just looks up the right-hand side of the rule
# and applies it.

class NonTerm(Format):
    def __init__(self,name):
        self.name = name
    def des(self,rdr):
        global grammar
        return grammar[self.name].des(rdr)
    def ser(self,wtr,obj):
        global grammar
        grammar[self.name].ser(wtr,obj)

# A ReaderContext is a context object that sets the current reader.

class ReaderContext(object):
    def __init__(self,rdr,pos):
        self.rdr, self.pos = rdr,pos
    def __enter__(self):
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        if exc_type == NoParse:
            self.rdr.setpos(self.pos)
        return False # don't catch the exception

# A StringReader reads tokens from a string

class StringReader(object):
    def __init__(self,string):
        self.pos = 0
        self.string = string
        self.stack = []
        self.highest = 0
    def chk(self):
        return ReaderContext(self,self.pos)
    def setpos(self,pos):
        self.pos = pos
    def read(self,nchars):
        if self.pos > self.highest:
            self.highest = self.pos
        res = self.string[self.pos:self.pos+nchars]
#        print "read: {} {} '{}'".format(self.pos,nchars,res)
        self.pos += nchars
        return res
    def read_regex(self,exp):
        if self.pos > self.highest:
            self.highest = self.pos
        mtch = exp.match(self.string,self.pos)
        if mtch is None:
#            print "no regex: {} '{}' {}".format(self.pos,exp.pattern,self.highest)
            raise NoParse
        res = mtch.group()
#        print "regex: {} '{}' '{}'".format(self.pos,exp.pattern,res)
        self.pos += len(res)
        return res
    def errloc(self):
        lines_read = self.string[:self.highest].split('\n')
        return (len(lines_read),len(lines_read[-1])+1)

# A StringWriter writes tokens to a string

class StringWriter(object):
    def __init__(self):
        self.strings = []
    def write(self,string):
        self.strings.append(string)
    def nest(self):
        pass
    def unnest(self):
        pass
    def __str__(self):
        return ''.join(self.strings)

# A PrettyWriter writes tokens to a string, inserting whitespace to
# make it prettier.

class Printer(object):
    def __init__(self,maxline=100,indent=4,begins=['{'],ends=['}']):
        self.maxline,self.indent,self.begins,self.ends = maxline,indent,begins,ends
        self.output = []
        self.stack = [0]
        self.pos = 0
        self.space = self.maxline
    def Indent(self):
        self.output.append('\n'+(self.maxline-self.space)*' ')
    def Print(self,token):
        if isinstance(token,list):
            self.stack.append(self.space)
            self.PrintList(token)
            del self.stack[-1]
        elif isinstance(token,tuple):
            s,l = token
            if l <= self.space or self.space == self.maxline:
                self.output.append(s)
                self.space -= len(s)
            else:
                self.space = self.stack[-1] - self.indent
                self.Indent()
        else:
            self.output.append(token)
            lines = token.split('\n')
            if len(lines) > 1:
                self.space = self.maxline - len(lines[-1])
                self.output.append('[space={}]'.format(self.space))
            else:
                self.space -= len(token)
    def PrintList(self,l):
        for t in l:
            self.Print(t)
    def __str__(self):
        return ''.join(self.output)
        

class PrettyWriter(object):
    def __init__(self,maxline=100,indent=4,whitespace=' ',begins=['{'],ends=['}']):
        self.tokens = []
        self.maxline = maxline
        self.indent=indent
        self.whitespace = whitespace
        self.begins = begins
        self.ends = ends
        self.stack = []
        self.total = 0
    def append(self,tok,l):
        if len(self.tokens) > 0:
            prev = self.tokens[-1]
            if isinstance(prev,tuple):
                self.tokens[-1] = (prev[0],prev[1]+l)
        self.tokens.append(tok)
        self.total += l
    def write(self,string):
        if string == self.whitespace:
            self.append((string,len(string)),len(string))
        else:
            l = len(string)
            self.append(string,l)
    def nest(self):
        self.stack.append((self.total,self.tokens))
        self.tokens = []
        self.total = 0
    def unnest(self):
        toks = self.tokens
        tot = self.total
        self.total,self.tokens = self.stack[-1]
        del self.stack[-1]
        # shift any terminal whitespace outsides the scope, to allow line breaking
        if len(toks) > 0 and isinstance(toks[-1],tuple):
            self.append(toks[:-1],tot - toks[-1][1])
            self.append(toks[-1],toks[-1][1])
        else:
            self.append(toks,tot)
    def __str__(self):
        p = Printer(self.maxline,self.indent,self.begins,self.ends)
        p.PrintList(self.tokens)
        return str(p)

# Functions for parsing and printing using the current grammer. In the
# following functions, the format can be specified either as a format
# object, or as the name of a non-terminal.

# Parse a given format from a reader

def report_syntax_error(rdr,filename):
    line,char = rdr.errloc()
    print (filename if filename is not None else '') + '({}): error: char {}: syntax error'.format(line,char)

def parse_reader(fmt,rdr,filename=None):
    if isinstance(fmt,str):
        fmt = grammar[fmt]
    try:
        res = fmt.des(rdr)
        if rdr.pos < len(rdr.string):
            report_syntax_error(rdr,filename)
    except NoParse:
        res = None
        print "position: {}".format(rdr.highest)
        report_syntax_error(rdr,filename)
    return res

# Parse a given formt from a string

def parse_string(fmt,string,filename=None):
    return parse_reader(fmt,StringReader(string),filename)

# Parse a given formt from a file

def parse_file(fmt,name):
    with open(name,"r") as f:
        string = f.read()
    return parse_string(fmt,string,name)

# Unparse a given object to a writer in a given format

def unparse_writer(fmt,obj,wtr):
    if isinstance(fmt,str):
        fmt = grammar[fmt]
    fmt.ser(wtr,obj)

# Unparse a given object in a given format and return result as a
# string.

def unparse_to_string(fmt,obj):
    wtr = StringWriter()
    unparse_writer(fmt,obj,wtr)
    return str(wtr)

# Pretty-print a given object in a given format and return result as a
# string.

def pretty_to_string(fmt,obj):
    wtr = PrettyWriter()
    unparse_writer(fmt,obj,wtr)
    return str(wtr)

# Pretty-print a given object in a given format and write the result to a
# file.

def pretty_to_file(fmt,obj,name):
    with open(name,"w") as f:
        f.write(pretty_to_string(fmt,obj))

# Ivy-style whitespace

ivywhite = WhiteSpace(RegEx(Unit,'([ \t\n]|(#[^\n]*))*',dflt=' '))


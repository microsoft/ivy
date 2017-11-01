from parser1 import *
from python1 import *

# This is the grammar of grammar descriptions.

SingleQuoted = RegEx(str,r"([^'']|(\''\''))*")  # Don't ignore whitespace in a quoted string!

defwhite = WhiteSpace(RegEx(Unit,'([ \t\n]|(#[^\n]*))*',dflt=' '))

with defwhite:
    ExactElem = Struct("Exact",NoWhite(Seq([Exact(Unit,"''"),Assign('text',SingleQuoted),Exact(Unit,"''")])))
    RegExElem = Struct("RegEx",NoWhite(Seq([Exact(Unit,"~"),Exact(Unit,"''"),Assign('exp',SingleQuoted),Exact(Unit,"''")])))
    NoWhiteElem = Struct("NoWhite",Seq([Exact(Unit,"nowhite"),Assign('fmt',NonTerm('Format'))]))
    Identifier = RegEx(str,r'[_a-zA-Z0-9]+')
    AssignElem = Struct("Assign",Seq([Exact(Unit,"<"),Assign('fld',Identifier),Exact(Unit,':='),Assign('fmt',NonTerm('Format')),Exact(Unit,">")]))
    ListElem = Struct("List",Seq([Exact(Unit,'['),
                                 Assign('fmt',NonTerm('Format')),
                                 Option(Assign('delim',NonTerm('Exact'))),
                                 Exact(Unit,'...'),
                                 Exact(Unit,']')]))
    SeqElem = Struct("Seq",Seq([Exact(Unit,'('),Assign('elems',List(NonTerm('Format'))),Exact(Unit,')')]))
    StructElem = Struct("Struct",Seq([Exact(Unit,'struct'),Assign('cls',Identifier),
                                     Assign('fmt',NonTerm('Format'))]))
    NonTermElem = Struct("NonTerm",Assign('name',Identifier))
    AltElem = Struct("Alt",Seq([Exact(Unit,"{"),Assign('elems',List(NonTerm('Format'))),Exact(Unit,'}')]))
    OptionElem = Struct("Option",Seq([Exact(Unit,"?"),Assign('elem',NonTerm('Format'))]))
    FormatElem = Alt([ExactElem,RegExElem,NoWhiteElem,AssignElem,ListElem,SeqElem,StructElem,NonTermElem,OptionElem,AltElem])
    RuleElem = Struct("Rule",Seq([Exact(Unit,'format'),Assign('lhs',Identifier),Exact(Unit,'='),
                                 Assign('rhs',NonTerm('Format'))]))
    GrammarElem = Struct("Grammar",Assign('rules',List(RuleElem)))
    Rules = [
        Rule("Format",FormatElem),
        Rule("Exact",ExactElem),
        Rule("Grammar",GrammarElem),
    ]
    FormatGrammar = Grammar(Rules)

# This is a grammar for Python expressions

python_expr_grammar = """
    format PyIdent = ~'[_a-zA-Z0-9]+'
    format PyArg = struct PyArg ( < lhs := PyIdent > '=' < rhs := PyExpr > )
    format PyApply = struct PyApply ( < func :=  PyIdent > ( '(' < args := [ PyArg ',' ... ] > ')' ) )
    format PyList = struct PyList ( '[' < elems := [ PyExpr ',' ... ] > ']' )
    format PyStr = struct PyStr nowhite ( '''' < val := ~'([^'']|(\''\''))*' > '''' )
    format PyExpr = { PyApply PyIdent PyList PyStr}
"""

# a few functions for testing

def test(fmt,string):
    print unparse_to_string(fmt,parse_string(fmt,string))

class testclass (object):
    def __init__(self,**kwargs):
        self.kwargs = kwargs
    def get(self,key,default=None):
        return self.kwargs.get(key,default)
    def __str__(self):
        return str(self.kwargs)

if __name__ == "__main__":

    src = "stage2.src"
    obj = "stage2.py"
    with defwhite:
        with FormatGrammar:
            thing = parse_file(GrammarElem,src)
            with PyExprSemantics():
                thing2 = parse_file(GrammarElem,src)
    with thing:
        with DefaultSemantics(globals()):
            with open(obj,"w") as f:
                f.write("""
from parser1 import *
from python1 import *

defwhite = WhiteSpace(RegEx(Unit,'([ \\t\\n]|(#[^\\n]*))*',dflt=' '))

with defwhite:
    grammar = """)
                f.write(pretty_to_string("PyExpr",thing2))
                f.write("""

class Field(Format):
    def __init__(self,name,type):
        self.name,self.type = name,type

class NamedType(Format):
    def __init__(self,name):
        self.name = name

class StructType(Format):
    def __init__(self,name):
        self.name = name

class TypeDecl(Format):
    def __init__(self,name,type):
        self.name,self.type = name,type

class Top(Format):
    def __init__(self,typedecls,grammar):
        self.typedecls,self.grammar = typedecls,grammar

src = "stage3.src"
obj = "stage3.py"
with defwhite:
    with grammar:
        with PyExprSemantics():
            thing = parse_file("Top",src)
        with DefaultSemantics(globals()):
            with open(obj,"w") as f:
                f.write("from parser1 import *\\n")
                f.write("from python1 import *\\n")
                for t in thing.find('typedecls').elems:
                    f.write("class {}(Format):\\n".format(t.find('name').val))
                    flds = t.find('type').find('fields').elems
                    f.write("    def __init__(self,{}):\\n".format(",".join(fl.find('name').val for fl in flds)))
                    for fl in flds:
                        fldnm = fl.find('name').val
                        f.write("        self.{} = {}\\n".format(fldnm,fldnm))
                f.write("grammar = ")
                f.write(pretty_to_string("PyExpr",thing.find('grammar')))
                f.write("\\n{}".format(thing.find('code').val))
""")
        
#     with FormatGrammar:
#         print "pretty = {}".format(pretty_to_string(GrammarElem,FormatGrammar))
#     with FormatGrammar:
# #        test(GrammarElem,python_expr_grammar)
#         with WhiteSpace(RegEx(Unit,'[ \t\n]*',dflt=' ')):
#             thing = parse_string(GrammarElem,python_expr_grammar)
#     with thing:
#         with DefaultSemantics(globals()):
#             foo = parse_string("PyExpr","x(a=y)")
#             print pretty_to_string("PyExpr",foo)
#     with FormatGrammar:
#         with WhiteSpace(RegEx(Unit,'[ \t\n]*',dflt=' ')):
#             with PyExprSemantics():
#                 thing2 = parse_string(GrammarElem,python_expr_grammar)
#     with thing:
#         with DefaultSemantics(globals()):
#             print pretty_to_string("PyExpr",thing2)
        

    # test(ExactElem,"  '42'")
    # test(Exact(Number,"42"),"42")
    # test(List(Exact(Number,"42"),delim=Exact(Unit,",")),"42,42")
    # test(Struct(testclass,Assign("x",Exact(int,"42"))),"42")
    # test(Struct(testclass,Alt([Assign("x",Exact(int,"41")),Assign("x",Exact(int,"42"))])),"42")
    # fmt = Struct(testclass,Alt([Assign("x",Exact(int,"41")),Assign("x",Exact(int,"42"))]))
    # print fmt.des(StringReader("42"))
    # test(Struct(testclass,Seq([Assign("x",Exact(int,"41")),Assign("y",Exact(int,"42"))])),"4142")
    # test(Struct(testclass,Bag([Assign("x",Exact(int,"41")),Assign("y",List(Exact(int,"42")))])),"424142")
    # test(Struct(testclass,Bag([Seq([Exact(Unit,'x'),Assign("x",Exact(int,"41"))]),
    #                       Seq([Exact(Unit,'y'),Assign("y",List(Exact(int,"42")))])])),
    #      "y42x41y42")
    # test(RegEx(str,'a*'),"aabb")
    # with WhiteSpace(RegEx(Unit,'[ \t\n]*',dflt=' ')):
    #     test(Exact(int,"42"),"  42")
    # print ExactElem.des(StringReader("  '42'"))
    # with FormatGrammar:
    #    test(FormatElem,"'foo'")
    #    test(FormatElem,"~'foo'")
    #    test(FormatElem," <x := 'foo'>")
    #    test(FormatElem," [ 'foo' ',' ... ]")
    #    test(FormatElem," nowhite ('foo' 'bar')")
    #    test(RuleElem,"format x = 'foo'")
    #    test(GrammarElem,"format x = 'foo' format y = ~'bar'")
    #    test(RuleElem,"format x = struct testclass { 'foo' 'bar' }")
    #    unparse_string(FormatElem,AssignElem)
    #    unparse_string(FormatElem,ExactElem)
    #    unparse_string(FormatElem,RegExElem)
    #    unparse_string(FormatElem,ListElem)
    #    unparse_string(FormatElem,AltElem)
    #    unparse_string(FormatElem,FormatElem)
    #    unparse_string(FormatElem,RuleElem)
    #    unparse_string(GrammarElem,FormatGrammar)
    #    print "pretty = {}".format(pretty_to_string(GrammarElem,FormatGrammar))
    #    thing = unparse_to_string(GrammarElem,FormatGrammar)
    #    test(GrammarElem,thing)
    #    with WhiteSpace(RegEx(Unit,'[ \t\n]*',dflt=' ')):
    #        gen2 = parse_string(GrammarElem,thing)
    # with gen2:
    #     thing2 = unparse_to_string("Grammar",gen2)
    #     print "thing2 = {}".format(thing2)
    #     with WhiteSpace(RegEx(Unit,'[ \t\n]*',dflt=' ')):
    #         gen3 = parse_string("Grammar",thing2)

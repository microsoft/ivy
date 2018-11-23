
from parser1 import *
from python1 import *

defwhite = WhiteSpace(RegEx(Unit,'([ \t\n]|(#[^\n]*))*',dflt=' '))

with defwhite:
    grammar = Grammar (
    rules =
        [ Rule ( rhs = RegEx ( exp = '[_a-zA-Z0-9]+' ) , lhs = 'Ident' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Seq (
                                elems =
                                    [ Assign ( fmt = NonTerm ( name = 'Ident' ) , fld = 'name' ) ,
                                        Exact ( text = ':' ) ,
                                        Assign ( fmt = NonTerm ( name = 'Ident' ) , fld = 'type' ) ]
                                ) , cls = 'Field' ) , lhs = 'Field' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Seq (
                                elems =
                                    [ Exact ( text = 'struct' ) , Exact ( text = '{' ) ,
                                        Assign (
                                            fmt =
                                                List ( fmt = NonTerm ( name = 'Field' ) ,
                                                    delim = Exact ( text = ',' ) ) , fld = 'fields'
                                            ) , Exact ( text = '}' ) ] ) , cls = 'StructType' ) ,
                lhs = 'Type' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Seq (
                                elems =
                                    [ Exact ( text = 'type' ) ,
                                        Assign ( fmt = NonTerm ( name = 'Ident' ) , fld = 'name' ) ,
                                        Exact ( text = '=' ) ,
                                        Assign ( fmt = NonTerm ( name = 'Type' ) , fld = 'type' ) ]
                                ) , cls = 'TypeDecl' ) , lhs = 'TypeDecl' ) ,
            Rule (
                rhs =
                    Alt (
                        elems =
                            [
                                Struct (
                                    fmt =
                                        NoWhite (
                                            fmt =
                                                Seq (
                                                    elems =
                                                        [ Exact ( text = '\'' ) ,
                                                            Assign (
                                                                fmt =
                                                                    RegEx (
                                                                        exp = '([^\']|(\\\'\\\'))*'
                                                                        ) , fld = 'text' ) ,
                                                            Exact ( text = '\'' ) ] ) ) ,
                                    cls = 'Exact' ) ,
                                Struct (
                                    fmt =
                                        NoWhite (
                                            fmt =
                                                Seq (
                                                    elems =
                                                        [ Exact ( text = '~' ) ,
                                                            Exact ( text = '\'' ) ,
                                                            Assign (
                                                                fmt =
                                                                    RegEx (
                                                                        exp = '([^\']|(\\\'\\\'))*'
                                                                        ) , fld = 'exp' ) ,
                                                            Exact ( text = '\'' ) ] ) ) ,
                                    cls = 'RegEx' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = 'nowhite' ) ,
                                                    Assign ( fmt = NonTerm ( name = 'Format' ) ,
                                                        fld = 'fmt' ) ] ) , cls = 'NoWhite' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = 'meta' ) ,
                                                    Assign ( fmt = NonTerm ( name = 'Format' ) ,
                                                        fld = 'fmt' ) ] ) , cls = 'Meta' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = 'line' ) ,
                                                    Assign ( fmt = NonTerm ( name = 'Format' ) ,
                                                        fld = 'fmt' ) ] ) , cls = 'Line' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = 'indent' ) ,
                                                    Assign ( fmt = NonTerm ( name = 'Format' ) ,
                                                        fld = 'fmt' ) ] ) , cls = 'Indent' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = 'escape' ) ,
                                                    NoWhite (
                                                        fmt =
                                                            Seq (
                                                                elems =
                                                                    [ Exact ( text = '\'' ) ,
                                                                        Assign (
                                                                            fmt =
                                                                                RegEx (
                                                                                    exp =
                                                                                        '([^\']|(\\\'\\\'))*'
                                                                                    ) , fld = 'spec'
                                                                            ) ,
                                                                        Exact ( text = '\'' ) ] ) )
                                                    ,
                                                    Assign ( fmt = NonTerm ( name = 'Format' ) ,
                                                        fld = 'fmt' ) ] ) , cls = 'Escape' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = 'breakable' ) ,
                                                    Assign ( fmt = NonTerm ( name = 'Format' ) ,
                                                        fld = 'fmt' ) ] ) , cls = 'Breakable' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = '<' ) ,
                                                    Assign ( fmt = RegEx ( exp = '[_a-zA-Z0-9]+' ) ,
                                                        fld = 'fld' ) , Exact ( text = ':=' ) ,
                                                    Assign ( fmt = NonTerm ( name = 'Format' ) ,
                                                        fld = 'fmt' ) , Exact ( text = '>' ) ] ) ,
                                    cls = 'Assign' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = '[' ) ,
                                                    Assign ( fmt = NonTerm ( name = 'Format' ) ,
                                                        fld = 'fmt' ) ,
                                                    Option (
                                                        elem =
                                                            Assign (
                                                                fmt = NonTerm ( name = 'Exact' ) ,
                                                                fld = 'delim' ) ) ,
                                                    Exact ( text = '...' ) ,
                                                    Option (
                                                        elem =
                                                            Assign ( fmt = Exact ( text = '+' ) ,
                                                                fld = 'plus' ) ) ,
                                                    Exact ( text = ']' ) ] ) , cls = 'List' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = '(' ) ,
                                                    Assign (
                                                        fmt =
                                                            List ( fmt = NonTerm ( name = 'Format' )
                                                                ) , fld = 'elems' ) ,
                                                    Exact ( text = ')' ) ] ) , cls = 'Seq' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = 'struct' ) ,
                                                    Assign ( fmt = RegEx ( exp = '[_a-zA-Z0-9]+' ) ,
                                                        fld = 'cls' ) ,
                                                    Assign ( fmt = NonTerm ( name = 'Format' ) ,
                                                        fld = 'fmt' ) ] ) , cls = 'Struct' ) ,
                                Struct (
                                    fmt =
                                        Assign ( fmt = RegEx ( exp = '[_a-zA-Z0-9]+' ) ,
                                            fld = 'name' ) , cls = 'NonTerm' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = '?' ) ,
                                                    Assign ( fmt = NonTerm ( name = 'Format' ) ,
                                                        fld = 'elem' ) ] ) , cls = 'Option' ) ,
                                Struct (
                                    fmt =
                                        Seq (
                                            elems =
                                                [ Exact ( text = '{' ) ,
                                                    Assign (
                                                        fmt =
                                                            List ( fmt = NonTerm ( name = 'Format' )
                                                                ) , fld = 'elems' ) ,
                                                    Exact ( text = '}' ) ] ) , cls = 'Alt' ) ] ) ,
                lhs = 'Format' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            NoWhite (
                                fmt =
                                    Seq (
                                        elems =
                                            [ Exact ( text = '\'' ) ,
                                                Assign ( fmt = RegEx ( exp = '([^\']|(\\\'\\\'))*' )
                                                    , fld = 'text' ) , Exact ( text = '\'' ) ] ) ) ,
                        cls = 'Exact' ) , lhs = 'Exact' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Assign (
                                fmt =
                                    List (
                                        fmt =
                                            Struct (
                                                fmt =
                                                    Seq (
                                                        elems =
                                                            [ Exact ( text = 'format' ) ,
                                                                Assign (
                                                                    fmt =
                                                                        RegEx (
                                                                            exp = '[_a-zA-Z0-9]+' )
                                                                    , fld = 'lhs' ) ,
                                                                Exact ( text = '=' ) ,
                                                                Assign (
                                                                    fmt =
                                                                        NonTerm ( name = 'Format' )
                                                                    , fld = 'rhs' ) ] ) ,
                                                cls = 'Rule' ) ) , fld = 'rules' ) , cls = 'Grammar'
                        ) , lhs = 'Grammar' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Seq (
                                elems =
                                    [
                                        Assign ( fmt = List ( fmt = NonTerm ( name = 'TypeDecl' ) )
                                            , fld = 'typedecls' ) ,
                                        Assign ( fmt = NonTerm ( name = 'Grammar' ) ,
                                            fld = 'grammar' ) , Exact ( text = '>>>' ) ,
                                        Assign ( fmt = RegEx ( exp = '.*' ) , fld = 'code' ) ] ) ,
                        cls = 'Top' ) , lhs = 'Top' ) ,
            Rule ( rhs = RegEx ( exp = '[_a-zA-Z0-9]+' ) , lhs = 'PyIdent' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Seq (
                                elems =
                                    [ Assign ( fmt = NonTerm ( name = 'PyIdent' ) , fld = 'lhs' ) ,
                                        Exact ( text = '=' ) ,
                                        Assign ( fmt = NonTerm ( name = 'PyExpr' ) , fld = 'rhs' ) ]
                                ) , cls = 'PyArg' ) , lhs = 'PyArg' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Seq (
                                elems =
                                    [ Assign ( fmt = NonTerm ( name = 'PyIdent' ) , fld = 'func' ) ,
                                        Seq (
                                            elems =
                                                [ Exact ( text = '(' ) ,
                                                    Assign (
                                                        fmt =
                                                            List ( fmt = NonTerm ( name = 'PyArg' )
                                                                , delim = Exact ( text = ',' ) ) ,
                                                        fld = 'args' ) , Exact ( text = ')' ) ] ) ]
                                ) , cls = 'PyApply' ) , lhs = 'PyApply' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Seq (
                                elems =
                                    [ Exact ( text = '[' ) ,
                                        Assign (
                                            fmt =
                                                List ( fmt = NonTerm ( name = 'PyExpr' ) ,
                                                    delim = Exact ( text = ',' ) ) , fld = 'elems' )
                                        , Exact ( text = ']' ) ] ) , cls = 'PyList' ) ,
                lhs = 'PyList' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            NoWhite (
                                fmt =
                                    Seq (
                                        elems =
                                            [ Exact ( text = '\'' ) ,
                                                Assign ( fmt = RegEx ( exp = '([^\']|(\\\'\\\'))*' )
                                                    , fld = 'val' ) , Exact ( text = '\'' ) ] ) ) ,
                        cls = 'PyStr' ) , lhs = 'PyStr' ) ,
            Rule (
                rhs =
                    Alt (
                        elems =
                            [ NonTerm ( name = 'PyApply' ) , NonTerm ( name = 'PyIdent' ) ,
                                NonTerm ( name = 'PyList' ) , NonTerm ( name = 'PyStr' ) ] ) ,
                lhs = 'PyExpr' ) ] ) 

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
                f.write("from parser1 import *\n")
                f.write("from python1 import *\n")
                for t in thing.find('typedecls').elems:
                    f.write("class {}(Format):\n".format(t.find('name').val))
                    flds = t.find('type').find('fields').elems
                    f.write("    def __init__(self,{}):\n".format(",".join(fl.find('name').val for fl in flds)))
                    for fl in flds:
                        fldnm = fl.find('name').val
                        f.write("        self.{} = {}\n".format(fldnm,fldnm))
                f.write("with ivywhite: grammar = ")
                f.write(pretty_to_string("PyExpr",thing.find('grammar')))
                f.write("\n{}".format(thing.find('code').val))

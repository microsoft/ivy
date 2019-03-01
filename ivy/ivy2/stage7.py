from parser1 import * 
class  Field (Format): 
    def __init__(self, name , type ): 
        self. name  =  name 
        self. type  =  type 
class  StructType (Format): 
    def __init__(self, fields ): 
        self. fields  =  fields 
class  TypeDecl (Format): 
    def __init__(self, name , type ): 
        self. name  =  name 
        self. type  =  type 
class  Top (Format): 
    def __init__(self, typedecls , grammar , code ): 
        self. typedecls  =  typedecls 
        self. grammar  =  grammar 
        self. code  =  code 
with ivywhite: grammar =  Grammar (
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
                                                        [ Exact ( text = '\'\'' ) ,
                                                            Assign (
                                                                fmt =
                                                                    RegEx (
                                                                        exp =
                                                                            '([^\'\']|(\\\'\'\\\'\'))*'
                                                                        ) , fld = 'text' ) ,
                                                            Exact ( text = '\'\'' ) ] ) ) ,
                                    cls = 'Exact' ) ,
                                Struct (
                                    fmt =
                                        NoWhite (
                                            fmt =
                                                Seq (
                                                    elems =
                                                        [ Exact ( text = '~' ) ,
                                                            Exact ( text = '\'\'' ) ,
                                                            Assign (
                                                                fmt =
                                                                    RegEx (
                                                                        exp =
                                                                            '([^\'\']|(\\\'\'\\\'\'))*'
                                                                        ) , fld = 'exp' ) ,
                                                            Exact ( text = '\'\'' ) ] ) ) ,
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
                                                                    [ Exact ( text = '\'\'' ) ,
                                                                        Assign (
                                                                            fmt =
                                                                                RegEx (
                                                                                    exp =
                                                                                        '([^\'\']|(\\\'\'\\\'\'))*'
                                                                                    ) , fld = 'spec'
                                                                            ) ,
                                                                        Exact ( text = '\'\'' ) ] )
                                                        ) ,
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
                                                    Exact ( text = '...' ) , Exact ( text = ']' ) ]
                                            ) , cls = 'List' ) ,
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
                                            [ Exact ( text = '\'\'' ) ,
                                                Assign (
                                                    fmt =
                                                        RegEx ( exp = '([^\'\']|(\\\'\'\\\'\'))*' )
                                                    , fld = 'text' ) , Exact ( text = '\'\'' ) ] ) )
                        , cls = 'Exact' ) , lhs = 'Exact' ) ,
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
                                    [ Assign ( fmt = NonTerm ( name = 'PyIdent' ) , fld = 'name' ) ,
                                        Exact ( text = '=' ) ,
                                        Assign ( fmt = NonTerm ( name = 'PyExpr' ) , fld = 'value' )
                                        ] ) , cls = 'MetaField' ) , lhs = 'PyArg' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Seq (
                                elems =
                                    [ Assign ( fmt = NonTerm ( name = 'PyIdent' ) , fld = 'cls' ) ,
                                        Breakable (
                                            fmt =
                                                Seq (
                                                    elems =
                                                        [ Exact ( text = '(' ) ,
                                                            Assign (
                                                                fmt =
                                                                    List (
                                                                        fmt =
                                                                            NonTerm ( name = 'PyArg'
                                                                                ) ,
                                                                        delim = Exact ( text = ',' )
                                                                        ) , fld = 'args' ) ,
                                                            Exact ( text = ')' ) ] ) ) ] ) ,
                        cls = 'MetaStruct' ) , lhs = 'PyApply' ) ,
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
                                        , Exact ( text = ']' ) ] ) , cls = 'MetaList' ) ,
                lhs = 'PyList' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            NoWhite (
                                fmt =
                                    Seq (
                                        elems =
                                            [ Exact ( text = '\'\'' ) ,
                                                Assign (
                                                    fmt =
                                                        Escape (
                                                            fmt =
                                                                RegEx (
                                                                    exp =
                                                                        '([^\'\']|(\\\'\'\\\'\'))*'
                                                                    ) , spec = '\\\\\'\'' ) ,
                                                    fld = 'val' ) , Exact ( text = '\'\'' ) ] ) ) ,
                        cls = 'MetaString' ) , lhs = 'PyStr' ) ,
            Rule (
                rhs =
                    Meta (
                        fmt =
                            Alt (
                                elems =
                                    [ NonTerm ( name = 'PyApply' ) , NonTerm ( name = 'PyList' ) ,
                                        NonTerm ( name = 'PyStr' ) ] ) ) , lhs = 'PyExpr' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Seq (
                                elems =
                                    [
                                        Line (
                                            fmt =
                                                Seq (
                                                    elems =
                                                        [ Exact ( text = 'class ' ) ,
                                                            Assign (
                                                                fmt = NonTerm ( name = 'PyIdent' ) ,
                                                                fld = 'name' ) ,
                                                            Exact ( text = '(Format):' ) ] ) ) ,
                                        Assign (
                                            fmt =
                                                Struct (
                                                    fmt =
                                                        Indent (
                                                            fmt =
                                                                Seq (
                                                                    elems =
                                                                        [
                                                                            Line (
                                                                                fmt =
                                                                                    Seq (
                                                                                        elems =
                                                                                            [
                                                                                                Exact
                                                                                                    (
                                                                                                    text
                                                                                                        =
                                                                                                        'def __init__(self,'
                                                                                                    )
                                                                                                ,
                                                                                                Assign
                                                                                                    (
                                                                                                    fmt
                                                                                                        =
                                                                                                        List
                                                                                                            (
                                                                                                            fmt
                                                                                                                =
                                                                                                                Struct
                                                                                                                    (
                                                                                                                    fmt
                                                                                                                        =
                                                                                                                        Assign
                                                                                                                            (
                                                                                                                            fmt
                                                                                                                                =
                                                                                                                                NonTerm
                                                                                                                                    (
                                                                                                                                    name
                                                                                                                                        =
                                                                                                                                        'PyIdent'
                                                                                                                                    )
                                                                                                                            ,
                                                                                                                            fld
                                                                                                                                =
                                                                                                                                'name'
                                                                                                                            )
                                                                                                                    ,
                                                                                                                    cls
                                                                                                                        =
                                                                                                                        'Field'
                                                                                                                    )
                                                                                                            ,
                                                                                                            delim
                                                                                                                =
                                                                                                                Exact
                                                                                                                    (
                                                                                                                    text
                                                                                                                        =
                                                                                                                        ','
                                                                                                                    )
                                                                                                            )
                                                                                                    ,
                                                                                                    fld
                                                                                                        =
                                                                                                        'fields'
                                                                                                    )
                                                                                                ,
                                                                                                Exact
                                                                                                    (
                                                                                                    text
                                                                                                        =
                                                                                                        '):'
                                                                                                    )
                                                                                                ] )
                                                                                ) ,
                                                                            Assign (
                                                                                fmt =
                                                                                    List (
                                                                                        fmt =
                                                                                            Struct (
                                                                                                fmt
                                                                                                    =
                                                                                                    Indent
                                                                                                        (
                                                                                                        fmt
                                                                                                            =
                                                                                                            Line
                                                                                                                (
                                                                                                                fmt
                                                                                                                    =
                                                                                                                    Seq
                                                                                                                        (
                                                                                                                        elems
                                                                                                                            =
                                                                                                                            [
                                                                                                                                Exact
                                                                                                                                    (
                                                                                                                                    text
                                                                                                                                        =
                                                                                                                                        'self.'
                                                                                                                                    )
                                                                                                                                ,
                                                                                                                                Assign
                                                                                                                                    (
                                                                                                                                    fmt
                                                                                                                                        =
                                                                                                                                        NonTerm
                                                                                                                                            (
                                                                                                                                            name
                                                                                                                                                =
                                                                                                                                                'PyIdent'
                                                                                                                                            )
                                                                                                                                    ,
                                                                                                                                    fld
                                                                                                                                        =
                                                                                                                                        'name'
                                                                                                                                    )
                                                                                                                                ,
                                                                                                                                Exact
                                                                                                                                    (
                                                                                                                                    text
                                                                                                                                        =
                                                                                                                                        ' = '
                                                                                                                                    )
                                                                                                                                ,
                                                                                                                                Assign
                                                                                                                                    (
                                                                                                                                    fmt
                                                                                                                                        =
                                                                                                                                        NonTerm
                                                                                                                                            (
                                                                                                                                            name
                                                                                                                                                =
                                                                                                                                                'PyIdent'
                                                                                                                                            )
                                                                                                                                    ,
                                                                                                                                    fld
                                                                                                                                        =
                                                                                                                                        'name'
                                                                                                                                    )
                                                                                                                                ]
                                                                                                                        )
                                                                                                                )
                                                                                                        )
                                                                                                ,
                                                                                                cls
                                                                                                    =
                                                                                                    'Field'
                                                                                                ) )
                                                                                , fld = 'fields' ) ]
                                                                    ) ) , cls = 'StructType' ) ,
                                            fld = 'type' ) ] ) , cls = 'TypeDecl' ) ,
                lhs = 'PyTypeDecl' ) ,
            Rule (
                rhs =
                    Struct (
                        fmt =
                            Seq (
                                elems =
                                    [ Line ( fmt = Exact ( text = 'from parser1 import *' ) ) ,
                                        Assign (
                                            fmt = List ( fmt = NonTerm ( name = 'PyTypeDecl' ) ) ,
                                            fld = 'typedecls' ) ,
                                        Line (
                                            fmt =
                                                Seq (
                                                    elems =
                                                        [
                                                            Exact (
                                                                text = 'with ivywhite: grammar = ' )
                                                            ,
                                                            Assign (
                                                                fmt = NonTerm ( name = 'PyExpr' ) ,
                                                                fld = 'grammar' ) ] ) ) ,
                                        Assign ( fmt = RegEx ( exp = '.*' ) , fld = 'code' ) ] ) ,
                        cls = 'Top' ) , lhs = 'PyTop' ) ] ) 
src = "stage8.src"
obj = "stage8.py"
with ivywhite:
    with grammar:
        with DefaultSemantics(globals()):
            thing = parse_file("Top",src)
            pretty_to_file("PyTop",thing,obj)
 
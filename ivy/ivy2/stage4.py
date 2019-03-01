from parser1 import * 
with ivywhite: grammar =  Grammar (
    rules =
        [
            Rule (
                rhs = List ( fmt = RegEx ( exp = '[_a-zA-Z0-9]+' ) , delim = Exact ( text = '+' ) )
                , lhs = 'inp' ) ,
            Rule (
                rhs =
                    Var (
                        fmt =
                            List (
                                fmt =
                                    EvalExpr (
                                        expr =
                                            Expr (
                                                apps =
                                                    [ Apply ( func = 'sum' ) ,
                                                        Apply (
                                                            args =
                                                                [
                                                                    Expr (
                                                                        apps =
                                                                            [
                                                                                Apply (
                                                                                    func = 'this' )
                                                                                ] ) ] , func = 'add'
                                                            ) ] ) ) ) , name = 'sum' ,
                        value =
                            Expr (
                                apps =
                                    [
                                        Apply (
                                            args = [ Expr ( apps = [ Apply ( func = 'foo' ) ] ) ] ,
                                            func = 'set' ) ] ) ) , lhs = 'out' ) ] ) 
src = "test1_inp.txt"
obj = "test1_out.txt"
with ivywhite:
    with grammar:
        with DefaultSemantics(globals()):
            thing = parse_file("inp",src)
            pretty_to_file("out",thing,obj)
 
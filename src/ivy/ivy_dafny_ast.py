#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

class AST(object):
    """
    Base class for abstract syntax.
    """
    def __init__(self,*args):
        self.args = args
    def __repr__(self):
        d = "{%s}" % ', '.join( "%s: %s" % (k,v) for k,v in self.__dict__.iteritems())
        return "%s %s" % (type(self).__name__, d)
    def clone(self,args):
        res = type(self)(*args)
        if hasattr(self,'lineno'):
            res.lineno = self.lineno
        return res
    def __eq__(self,other):
        return type(self) == type(other) and self.args == other.args

class Field(AST):
    pass

class VarDecl(Field):
    def __repr__(self):
        return 'var ' + ','.join(repr(a) for a in self.args) + ';'


def repr_args(args):
    return '(' + ','.join(repr(a) for a in args) + ')' if args else '()'

def repr_modset(args):
    return '{' + ','.join(repr(a) for a in args) + '}' if args else '{}'

class MethodDecl(Field):
    def __repr__(self):
        symbol,args,returns,requires,modifies,ensures,decreases,stmts = self.args
        res = 'method ' + repr(symbol) + repr_args(args)
        if returns: res += ' returns' + repr_args(returns)
        if requires: res += ' requires ' + repr(requires)
        if modifies: res += ' modifies ' + repr_modset(modifies)
        if ensures: res += ' ensures ' + repr(ensures)
        if decreases: res += ' decreases ' + repr(decreases)
        res += '\n{\n    '
        res += '\n    '.join(repr(s) for s in stmts)
        res += '\n}\n'
        return res

class Symbol(AST):
    def __init__(self,name):
        self.rep = name
    def __repr__(self):
        return self.rep
    def infix(self):
        return False
    def precedence(self):
        return 0

class Type(Symbol):
    pass

class InfixSymbol(Symbol):
    def infix(self):
        return True
    _type = Type('bool')

class InfixRelation(InfixSymbol):
    def infix(self):
        return True

class TypedSymbol(Symbol):
    def __init__(self,name,_type):
        self.rep,self._type = name,_type
    def __repr__(self):
        return self.rep + ':' + repr(self._type)


class Numeral(TypedSymbol):
    def __init__(self,name):
        TypedSymbol.__init__(self,name,Type('int'))

class BoolType(Type):
    def __init__(self):
        self.rep = 'bool'

class Expr(AST):
    pass

class App(Expr):
    def __init__(self,symbol,*args):
        self.symbol = symbol
        self.args = args
    def __repr__(self):
        if self.symbol.infix():
            return self.symbol.rep.join(repr(a) for a in self.args)
        res = repr(self.symbol)
        if self.args:
            ra = ','.join(repr(a) for a in self.args)
            res += '(' + ra + ')'
        return res
    def clone(self,args):
        res = App(self.symbol,*args)
        if hasattr(self,'lineno'):
            res.lineno = self.lineno
        return res

class True(Expr):
    def __repr__(self):
        return "true"

class Eq(InfixRelation):
    def __init__(self):
        self.rep = '=='
        self._type = Type('bool')

class And(InfixSymbol):
    def __init__(self):
        self.rep = '&'
        self._type = Type('bool')

class Or(InfixSymbol):
    def __init__(self):
        self.rep = '|'
        self._type = Type('bool')

class Implies(InfixSymbol):
    def __init__(self):
        self.rep = '==>'
        self._type = Type('bool')

class Iff(InfixSymbol):
    def __init__(self):
        self.rep = '<==>'
        self._type = Type('bool')

class Not(Symbol):
    def __init__(self):
        self.rep = '!'
        self._type = Type('bool')

class Stmt(AST):
    pass

class AssignStmt(Stmt):
    def __repr__(self):
        return repr(self.args[0]) + ":=" + repr(self.args[1]) + ';'

class AssertStmt(Stmt):
    def __repr__(self):
        return 'assert ' + repr(self.args[0]) + ';'

class AssumeStmt(Stmt):
    def __repr__(self):
        return 'assume ' + repr(self.args[0]) + ';'

class WhileStmt(Stmt):
    def __repr__(self):
        res = 'while (' + repr(self.args[0]) + ')\n'
        if self.args[1]:
            res+= '  invariant ' + repr(self.args[1]) + '\n'
        return res + '{\n' + repr(self.args[2]) + '\n}\n'

class IfStmt(Stmt):
    def __repr__(self):
        if_part  = 'if ' + repr(self.args[0]) + ' {' + repr(self.args[1]) + '}'
        else_part = ('\nelse {' + repr(self.args[2]) + '}') if len(self.args) >= 3 else ''
        return if_part + else_part

class VarStmt(Stmt):
    def __repr__(self):
        return 'var ' + ','.join(repr(a) for a in self.args) + ';'

class Tuple(Expr):
    def __repr__(self):
        return ','.join(repr(a) for a in self.args)

class Module(AST):
    def __init__(self):
        self.decls = []
    def __repr__(self):
        return '\n'.join(repr(d) for d in self.decls)
    def declare(self,decl):
        self.decls.append(decl)

class Call(AST):
    def __repr__(self):
        return repr(self.args[0]) + '(' + ','.join(repr(d) for d in self.args[1:]) + ')'
    
class ReturnStmt(AST):
    def __repr__(self):
        return 'return ' + ','.join(repr(d) for d in self.args) + ';'
    
    

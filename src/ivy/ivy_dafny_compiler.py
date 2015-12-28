#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy_dafny_ast as da
import ivy_parser as ip
import ivy_utils as iu

class Context(object):
    def __enter__(self):
        self.old_context = globals().get(self.name,None)
        globals()[self.name] = self
        return self
    def __exit__(self,exc_type, exc_val, exc_tb):
        globals()[self.name] = self.old_context
        return False # don't block any exceptions

class ModuleContext(Context):
    """ Context Manager for compiling dafny to ivy. """
    def __init__(self,dafny_module,ivy_module):
        self.dm, self.im = dafny_module,ivy_module
        self.types = dict()
        for decl in dafny_module.decls:
            if isinstance(decl,da.MethodDecl):
                self.types[decl.args[0].rep] = method_type(decl)
        self.name = 'context'

class MethodContext(Context):
    """ Context Manager for compiling a dafny method. """
    def __init__(self,method_name,modifies,outparams):
        self.rn = iu.UniqueRenamer(method_name + ':tmp',{})
        self.local_renamer = iu.UniqueRenamer('loc:' + method_name + ':',{})
        self.modifies = modifies
        self.outparams = outparams
        self.name = 'method_context'

class ScopeContext(Context):
    """ Context Manager for local scopes. """
    def __init__(self):
        # copy existing local variabes if any
        if 'scope_context' in globals() and scope_context:
            self.locals = dict(scope_context.locals.iteritems())
        else:
            self.locals = dict()
        self.new_locals = []
        self.name = 'scope_context'
        self.returns = False
    # tricky: if scope returns, then outer scopes also return
    def __exit__(self,exc_type, exc_val, exc_tb):
        Context.__exit__(self,exc_type, exc_val, exc_tb)
        if scope_context:
            scope_context.returns |= self.returns
        
class ExprContext(Context):
    """ Context Manager for compiling an expression. """
    def __init__(self,code):
        self.code = code
        self.name = 'expr_context'

########################################################################
# Utility function for emitting Ivy

def method_type(m):
    return [args_type(args) for args in m.args[1:3]]

def args_type(args):
    return [arg._type for arg in args]

def return_type(method_symbol):
    t = context.types.get(method_symbol.rep,None)
    return t[1] if t != None else None

def make_app(symbol,*args):
    if hasattr(symbol,'_type') and symbol._type.rep == 'bool':
        return ip.Atom(symbol.rep,args)
    return ip.App(symbol.rep,*args)

def make_seq(code):
    if len(code) == 1:
        return code[0]
    return ip.Sequence(*code)

def declare_type(sym):
    da.VarDecl(sym).to_ivy()

def make_temp(_type):
    ret = da.TypedSymbol(method_context.rn(''),_type)
    declare_type(ret)
    scope_context.new_locals.append(ret)
    return make_app(ret)

def make_dummy(pref,v):
    ret = da.TypedSymbol(pref+v.rep,v._type)
    declare_type(ret)
    return make_app(ret)

def make_arg(a,pref,nmap):
    sym = da.TypedSymbol(pref.rep + ':' + a.rep,a._type)
    if sym.rep in nmap:
        raise IvyError(a,"repeated formal parameter")
    declare_type(sym)
    nmap[a.rep] = sym
    return sym

def expect_return_vals(sym,num_vals,ast):
    ret_type = return_type(sym)
    if ret_type == None:
        raise IvyError(ast,"undefined: {}".format(sym.rep))
    if len(ret_type) != num_vals:
        raise IvyError(ast,"expected {} value(s) from {}, got {}".format(num,sym.rep,len(ret_type)))
    return ret_type
    
def assign_temp(expr):
    retval = make_temp(expr.type_infer())
    expr_context.code.append(ip.AssignAction(retval,expr.to_ivy()))
    return retval

## Dafny type inference

def type_infer_symbol(symb,args):
    global context
    dm,im = context.dm,context.im
    if args:
        raise IvyError(symb,"cannot type term")
    symb = scope_context.locals.get(symb.rep,symb) if scope_context else symb
    if isinstance(symb,da.TypedSymbol):
        return symb._type
    if symb.rep in context.types:
        return context.types[symb.rep]
    raise IvyError(symb,"cannot type term")

arith_ops = {'+','-','*'}

def type_infer_infix(symb,args):
    if symb.rep in arith_ops:
        return args[0].type_infer()
    return BoolType()

def type_infer_app(e):
    return e.symbol.type_infer(e.args)
        
def type_infer_call(c):
    sym = c.args[0]
    ret_type = expect_return_vals(sym,1,c)
    return ret_type[0]

da.Symbol.type_infer = type_infer_symbol
da.InfixSymbol.type_infer = type_infer_infix
da.Not.type_infer = type_infer_infix
da.App.type_infer = type_infer_app
da.Call.type_infer = type_infer_call

########################################################################
# Translation methods for Dafny syntactic categories

def vardecl(d):
    global context
    dm,im = context.dm,context.im
    for a in d.args:
        t = a._type
        if t.rep == 'bool':
            decl = ip.RelationDecl(ip.Atom(a.rep,[]))
        elif t.rep == 'object':
            decl = ip.ConstantDecl(ip.App(a.rep))
        else:
            thing = ip.App(a.rep)
            thing.sort = t.rep
            decl = ip.ConstantDecl(thing)
        im.declare(decl)

def asgnstmt(s):
    global context
    dm,im = context.dm,context.im
    lhs,rhs = s.args
    if len(lhs.args) != len(rhs.args):
        raise IvyError(s,"wrong number of values in assignment")
#    assert len(lhs.args) == 1
    code = []
    with ExprContext(code):
        if len(rhs.args) == 1:
            code.append(ip.AssignAction(lhs.args[0].to_ivy(),rhs.args[0].to_ivy()))
        else:
            rhss = [assign_temp(t) for t in rhs.args]
            lhss = [t.to_ivy() for t in lhs.args]
            for x,y in zip(lhss,rhss):
                code.append(ip.AssignAction(x,y))
    return make_seq(code)

def assumestmt(s):
    global context
    dm,im = context.dm,context.im
    a = s.args[0]
    return ip.AssumeAction(a.to_ivy())

def assertstmt(s):
    global context
    dm,im = context.dm,context.im
    a = s.args[0]
    return ip.AssertAction(a.to_ivy())

def check_return(x):
    global scope_context
    if x and scope_context.returns:
        raise iu.IvyError(x,"statement skipped over by return")
    return True

def block(stmts):
    with ScopeContext():
        actions = [(check_return(x) and x.to_ivy()) for x in stmts]
        actions = ip.Sequence(*[a for a in actions if a]) # squeeze out no-ops
        if scope_context.new_locals:
            actions = ip.LocalAction(*([a.rep for a in scope_context.new_locals] + [actions]))
    return actions
        

# if a while loop doesn't specify a modset, assume that loop body
# modifies all locals in scope and modset of method
def get_while_modset(mods):
    if mods:
        return [ip.Atom(s.to_ivy([]).rep,[]) for s in mods]
    elif method_context.modifies:
        return method_context.modifies + [ip.Atom(y.rep,[]) for x,y in scope_context.locals.iteritems()]
    return None

def whilestmt(s):
    global context
    dm,im = context.dm,context.im
    cond,mods,inv,body = s.args
    lineno = s.lineno
    cond,inv = cond.to_ivy(),(inv.to_ivy() if inv else ip.And())
    body = ip.Sequence(ip.AssumeAction(cond),block(body))
    mods = get_while_modset(mods)
    name = method_context.rn('while')
    body_name = name + '_body'
    act_decl = ip.ActionDecl(ip.ActionDef(body_name,body))
    im.declare(act_decl)
#    df = ip.Or(ip.entry(),ip.Atom(body_name,[ip.Atom(name,[])]))
    df = ip.Atom(body_name,[ip.Atom(name,[])])
    state_decl = ip.StateDecl(ip.StateDef(name,df))
    im.declare(state_decl)
    ass_decl = ip.AssertDecl(ip.Implies(ip.Atom(name,[]),ip.RME(inv,mods,inv)))
    ass_decl.args[0].lineno = lineno
    im.declare(ass_decl)
    return ip.Sequence(ip.CallAction(ip.Atom(name,[])),ip.AssumeAction(ip.Not(cond)))

def ifstmt(s):
    global context
    dm,im = context.dm,context.im
    return ip.IfAction(s.args[0].to_ivy(),block(s.args[1]),block(s.args[2]))

def do_varstmt(a):
        # make up a fresh name for local variable
        name = method_context.local_renamer(a.rep)
        local = da.TypedSymbol(name,a._type)
        vardecl(da.VarDecl(local))
        scope_context.locals[a.rep] = local
        scope_context.new_locals.append(local)
    

def varstmt(s):
    global context
    dm,im = context.dm,context.im
    for a in s.args:
        if isinstance(a,da.AssignStmt):
            vn,vv = a.args
            if len(vn.args) == len(vv.args): # if false, we'll throw error compiling assignment
                for x,y in zip(vn.args,vv.args):
                    do_varstmt(da.TypedSymbol(x.symbol.rep,y.type_infer()))
            return a.to_ivy()
        else:
            do_varstmt(a)
        
opmap = {'==' : '='}

def returnstmt(s):
    outparams = da.Tuple(*[da.App(p) for p in method_context.outparams])
    values = da.Tuple(*s.args)
    opa = da.AssignStmt(outparams,values)
    opa.lineno = s.lineno
    res = opa.to_ivy()
    scope_context.returns = True
    return res

def symbol(symb,args):
    global context
    dm,im = context.dm,context.im
    symb = scope_context.locals.get(symb.rep,symb) if scope_context else symb
    res = make_app(symb,*[a.to_ivy() for a in args])
    rep = symb.rep
    res.rep = opmap.get(rep,rep)
    return res
    
def infixrelation(symb,args):
    if isinstance(args[0].symbol,da.InfixRelation):
        c1 = args[0].to_ivy()
        c2 = make_app(symb,c1.args[1],args[1].to_ivy())
        c2.rep = opmap.get(symb.rep,symb.rep)
        return ip.And(c1,c2)
    return symbol(symb,args)

def _and(symb,args):
    return ip.And(*[a.to_ivy() for a in args])

def _or(symb,args):
    return ip.Or(*[a.to_ivy() for a in args])

def implies(symb,args):
    return ip.Or(ip.Not(args[0].to_ivy()), args[1].to_ivy())

def iff(symb,args):
    ia = [a.to_ivy() for a in args]
    return ip.Or(ip.And(*ia),ip.And(*[ip.Not(a) for a in ia]))

def _not(symb,args):
    return ip.Not(*[a.to_ivy() for a in args])

def app(e):
    return e.symbol.to_ivy(e.args)

def methoddecl(d):
    global context
    dm,im = context.dm,context.im
    symbol,args,returns,requires,modifies,ensures,decreases,stmts = d.args
    nmap = dict()
    inps = [make_arg(a,symbol,nmap) for a in args]
    outs = [make_arg(a,symbol,nmap) for a in returns] if returns else []

    # do the copying for call-by-value
    ma = [ip.App('__arg'+str(i)) for i in range(0,len(inps))]
    pa = [ip.App(a.rep) for a in inps]
    pad = [ip.App(make_dummy('cbv:',a).rep) for a in inps]
    mb = [ip.AssignAction(a,b) for a,b in zip(pad,ma)]
    mr = [ip.App('__arg'+str(i)) for i in range(len(inps),len(inps)+len(outs))]
    pr = [ip.App(a.rep) for a in outs]
    prd = [ip.App(make_dummy('cbv:',a).rep) for a in outs]
    ca = ip.CallAction(ip.Atom(symbol.rep,[]))
    mb += [ip.LetAction(*([ip.Atom('=',[x,y]) for x,y in zip(pa+pr,pad+prd)] + [ca]))]
    mb += [ip.AssignAction(b,a) for a,b in zip(prd,mr)]    
    ls = [s.rep for s in (pad+prd)]
    mb = ip.LocalAction(*(ls+[ip.Sequence(*mb)]))

    # rename all the parameters
    ds = d.subst_symbols(nmap)
    symbol,args,returns,requires,modifies,ensures,decreases,stmts = ds.args

    # translate the spec
    modifies = ([ip.Atom(s.rep,[]) for s in modifies] + pr) if modifies != None else pr

    # output an action
    with MethodContext(symbol.rep, modifies, returns):
        body = block(stmts)
    decl = ip.ActionDecl(ip.ActionDef(symbol.rep,body))
    im.declare(decl)

    # output a macro for call-by value
    df = ip.Definition(ip.Atom('cbv:'+symbol.rep,ma+mr),mb)
    im.declare(ip.MacroDecl(df))
    im.macros[df.defines()] = df

    # output a specification
 #   if ensures or modifies or requires:
#        requires = lut.rename_ast(requires,dict((inp.rep,tr.old(inp.rep)) for inp in inps))
    ensures = ensures.to_ivy() if ensures else ip.And()
    requires = requires.to_ivy() if requires else ip.And()
    spec = ip.RME(requires,modifies,ensures)
    thing = ip.Implies(ip.Atom(symbol.rep,[]),spec)
    decl = ip.AssertDecl(thing)
    if hasattr(d,'lineno'):
        thing.lineno = d.lineno
    im.declare(decl)

def call(c):
    sym = c.args[0]
    args = [a.to_ivy() for a in c.args[1:]]
    ret_type = expect_return_vals(sym,1,c)
    retval = make_temp(ret_type[0])
    atom = ip.Atom('cbv:'+sym.rep, args + [retval])
    expr_context.code.append(ip.InstantiateAction(atom))
    return retval

def _module(m):
    for d in m.decls:
        d.to_ivy()

###############################################################################
# Add aspects to Dafny AST classes for translation to ivy

da.VarDecl.to_ivy = vardecl
da.AssignStmt.to_ivy = asgnstmt
da.AssumeStmt.to_ivy = assumestmt
da.AssertStmt.to_ivy = assertstmt
da.WhileStmt.to_ivy = whilestmt
da.IfStmt.to_ivy = ifstmt
da.ReturnStmt.to_ivy = returnstmt
da.App.to_ivy = app
da.MethodDecl.to_ivy = methoddecl
da.Module.to_ivy = _module
da.Call.to_ivy = call
da.VarStmt.to_ivy = varstmt
da.Symbol.to_ivy = symbol
da.InfixRelation.to_ivy = infixrelation
da.And.to_ivy = _and
da.Or.to_ivy = _or
da.Not.to_ivy = _not
da.Implies.to_ivy = implies
da.Iff.to_ivy = iff

def subst_symbols_symbol(s,m):
    return m[s.rep] if s.rep in m else s

da.Symbol.subst_symbols = subst_symbols_symbol

def subst_symbols_list(l,m):
    if isinstance(l,list):
        return [subst_symbols_list(a,m) for a in l]
    if l == None: return None
    if isinstance(l,da.AST):
        return l.subst_symbols(m)
    assert False

def subst_symbols_ast(s,m):
    return s.clone([subst_symbols_list(a,m) for a in s.args])

da.AST.subst_symbols = subst_symbols_ast

def subst_symbols_app(s,m):
    return da.App(s.symbol.subst_symbols(m),
                  *[subst_symbols_list(a,m) for a in s.args])

da.App.subst_symbols = subst_symbols_app

import ivy_dafny_parser as dp

preamble = """
type int
interpret int -> Int
relation (X:int <= Y:int)
relation (X:int < Y:int)
relation (X:int >= Y:int)
relation (X:int > Y:int)
individual (X:int + Y:int) : int
individual (X:int * Y:int) : int
individual (X:int - Y:int) : int
interpret <= -> <=
interpret < -> <
interpret >= -> >=
interpret > -> >
interpret + -> +
interpret - -> -
interpret * -> *
"""

def parse_to_ivy(s):
    dm = dp.parse(s)
    im = ip.parse(preamble)
    with ModuleContext(dm,im):
        dm.to_ivy()
        print im
        return im

if __name__ == "__main__":
    with iu.ErrorPrinter():
        dm = dp.parse("""
            // a comment
            var x : bool;
            var y : object;
            method P(y:object) returns (x:object)
                modifies x;
                ensures x == y;
                {
                     x := y;
                     assume x == y;
                }""")
        im = ip.Ivy()
        with ModuleContext(dm,im):
            dm.to_ivy()
            print im

    

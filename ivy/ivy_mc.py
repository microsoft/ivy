#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy_module as im
import ivy_actions as ia
import ivy_logic as il
import ivy_transrel as tr
import ivy_logic_utils as ilu
import ivy_utils as iu
import ivy_art as art
import ivy_interp as itp
import ivy_theory as thy
import ivy_ast
import ivy_proof
import ivy_trace

import tempfile
import subprocess
from collections import defaultdict
import itertools
import sys

logfile = None

def get_truth(digits,idx,syms):
    if (len(digits) != len(syms)):
        badwit()
    digit = digits[idx]
    if digit == '0':
        return il.Or()
    elif digit == '1':
        return il.And()
    elif digit != 'x':
        badwit()
    return None


class Aiger(object):
    def __init__(self,inputs,latches,outputs):
#        iu.dbg('inputs')
#        iu.dbg('latches')
#        iu.dbg('outputs')
        inputs = inputs + [il.Symbol('%%bogus%%',il.find_sort('bool'))] # work around abc bug
        self.inputs = inputs
        self.latches = latches
        self.outputs = outputs
        self.gates = []
        self.map = dict()
        self.next_id = 1
        self.values = dict()
        for x in inputs + latches:
            self.map[x] = self.next_id * 2
#            print 'var: {} = {}'.format(x,self.next_id * 2)
            self.next_id += 1
        
    def true(self):
        return 1

    def false(self):
        return 0

    def lit(self,sym):
        return self.map[sym]

    def define(self,sym,val):
#        print 'define: {} = {}'.format(sym,val)
        self.map[sym] = val
        
    def andl(self,*args):
        if not args:
            return self.true()
        res = args[0]
        for x in args[1:]:
            tmp = self.next_id * 2
            self.gates.append((tmp,res,x))
            self.next_id += 1
            res = tmp
        return res

    def notl(self,arg):
        return 2*(arg/2) + (1 - arg%2)
    
    def orl(self,*args):
        return self.notl(self.andl(*map(self.notl,args)))

    def ite(self,x,y,z):
        return self.orl(self.andl(x,y),self.andl(self.notl(x),z))

    def iff(self,x,y):
        return self.orl(self.andl(x,y),self.andl(self.notl(x),self.notl(y)))

    def implies(self,x,y):
        return self.orl(self.notl(x),y)

    def xor(self,x,y):
        return self.notl(self.iff(x,y))

    def eval(self,expr,getdef=None):
        def recur(expr):
            if il.is_app(expr):
                sym = expr.rep
                assert il.is_boolean_sort(sym.sort),"non-boolean sym in aiger output: {}".format(sym)
                try:
                    return self.lit(sym)
                except KeyError:
                    assert getdef is not None, "no definition for {} in aiger output".format(sym)
                    return getdef(sym)
            else:
                args = map(recur,expr.args)
                if isinstance(expr,il.And):
                    return self.andl(*args)
                if isinstance(expr,il.Or):
                    return self.orl(*args)
                if isinstance(expr,il.Not):
                    return self.notl(*args)
                assert False,"non-boolean op in aiger output: {}".format(type(expr))
        return recur(expr)


    def deflist(self,defs):
        dmap = dict((df.defines(),df.args[1]) for df in defs)
        def getdef(sym):
            if sym not in dmap:
                assert getdef is not None, "no definition for {} in aiger output".format(sym)
            val = self.eval(dmap[sym],getdef)
            self.define(sym,val)
            return val
        for df in defs:
            sym = df.defines()
            assert il.is_boolean_sort(sym.sort),"non-boolean sym in aiger output: {}".format(sym)
            self.define(sym,self.eval(df.args[1],getdef))
    
    def set(self,sym,val):
        self.values[sym] = val

    def get_state(self,post):
        res = dict()
        for i,v in enumerate(self.latches):
            res[v] = get_truth(post,i,self.latches)
        return res

    def __str__(self):
        strings = []
        strings.append('aag {} {} {} {} {}'.format(self.next_id - 1,len(self.inputs),
                                                   len(self.latches),len(self.outputs),
                                                   self.next_id - 1 - (len(self.inputs) + len(self.latches))))
        for x in self.inputs:
            strings.append(str(self.map[x]))
        for x in self.latches:
            strings.append(str('{} {}'.format(self.map[x],self.values[x])))
        for x in self.outputs:
            strings.append(str(self.values[x]))
        for x,y,z in self.gates:
            strings.append(str('{} {} {}'.format(x,y,z)))
        return '\n'.join(strings)+'\n'
                                          
    def sym_vals(self,syms):
        for sym in syms:
            assert sym in self.map, sym
        return ''.join(self.getin(self.map[x]) for x in syms)

    def sym_next_vals(self,syms):
        return ''.join(self.getin(self.values[x]) for x in syms)

    def latch_vals(self):
        return self.sym_vals(self.latches)

    def input_vals(self):
        return self.sym_vals(self.inputs)

    def show_state(self):
        print 'state: {}'.format(self.latch_vals())
        
    def reset(self):
        self.state = dict((self.map[x],'0') for x in self.latches)

    def getin(self,gi):
        if gi == 0:
            return '0'
        if gi == 1:
            return '1'
        v = self.state[gi & ~1]
        return ('0' if v == '1' else '1') if (gi & 1) else v

    def step(self,inp):
        assert len(inp) == len(self.inputs)
        for x,y in zip(self.inputs,inp):
            self.state[self.map[x]] = y
#        print 'input: {}'.format(self.sym_vals(self.inputs))
        for out,in0,in1 in self.gates:
            res = '1' if (self.getin(in0) == '1' and self.getin(in1) == '1') else '0'
            self.state[out] = res
#            print 'gate {}: {}'.format(out,res)
#        print 'outputs: {}'.format(''.join(self.getin(self.values[x]) for x in self.outputs))

    def next(self):
        for lt in self.latches:
            self.state[self.map[lt]] = self.getin(self.values[lt])
#        self.show_state()


    def debug(self):
        print 'inputs: {}'.format([str(x) for x in self.inputs])
        print 'latches: {}'.format([str(x) for x in self.latches])
        print 'outputs: {}'.format([str(x) for x in self.outputs])
        print 'map:'
        for x,y in self.map.iteritems():
            print '{} = {}'.format(x,y)
        print 'values:'
        for x,y in self.values.iteritems():
            print '{} = {}'.format(x,y)
        print 'self:'
        print self

        
            
# functions for binary encoding of finite sorts

def ceillog2(n):
    bits,vals = 0,1
    while vals < n:
        bits += 1
        vals *= 2
    return bits

def get_encoding_bits(sort):
    interp = thy.get_sort_theory(sort)
    if il.is_enumerated_sort(interp):
        n = ceillog2(len(interp.defines()))
    elif isinstance(interp,thy.BitVectorTheory):
        n = interp.bits
    elif il.is_boolean_sort(interp):
        n = 1
    else:
        msg = 'model checking cannot handle sort {}'.format(sort)
        if interp is not sort:
            msg += '(interpreted as {})'.format(interp)
        raise iu.IvyError(None,msg)
    return n
                                  

def encode_vars(syms,encoding):
    res = []
    for sym in syms:
        n = get_encoding_bits(sym.sort)
        vs = [sym.suffix('[{}]'.format(i)) for i in range(n)]
        encoding[sym] = vs
        res.extend(vs)
    return res

class Encoder(object):
    def __init__(self,inputs,latches,outputs):
#        iu.dbg('[(str(inp),str(inp.sort)) for inp in inputs]')
#        iu.dbg('latches')
#        iu.dbg('outputs')
        self.inputs = inputs
        self.latches = latches
        self.outputs = outputs
        self.encoding = dict()
        self.pos = dict()
        subinputs = encode_vars(inputs,self.encoding)
        sublatches = encode_vars(latches,self.encoding)
        suboutputs = encode_vars(outputs,self.encoding)
        self.sub = Aiger(subinputs,sublatches,suboutputs)
        self.ops = {
            '+' : self.encode_plus,
            '-' : self.encode_minus,
            '*' : self.encode_times,
            '/' : self.encode_div,
            '%' : self.encode_mod,
            '<' : self.encode_le,
            }
        
    def true(self):
        return [self.sub.true()]

    def false(self):
        return [self.sub.false()]

    def lit(self,sym):
        return map(self.sub.lit,self.encoding[sym])

    def define(self,sym,val):
        vs = encode_vars([sym],self.encoding)
        for s,v in zip(vs,val):
            self.sub.define(s,v )
        
    def andl(self,*args):
        if len(args) == 0:
            return self.true()
        return [self.sub.andl(*v) for v in zip(*args)]

    def orl(self,*args):
        if len(args) == 0:
            return self.false()
        return [self.sub.orl(*v) for v in zip(*args)]

    def notl(self,arg):
        return map(self.sub.notl,arg)
    
    def implies(self,x,y):
        return [self.sub.implies(a,b) for a,b in zip(x,y)]

    def iff(self,x,y):
        return [self.sub.iff(a,b) for a,b in zip(x,y)]

    def eval(self,expr,getdef=None):
        def recur(expr):
            if isinstance(expr,il.Ite):
                cond = recur(expr.args[0])
                thenterm = recur(expr.args[1])
                elseterm = recur(expr.args[2])
                res = [self.sub.ite(cond[0],x,y) for x,y in zip(thenterm,elseterm)]
            elif il.is_app(expr):
                sym = expr.rep 
                if sym in il.sig.constructors:
                    m = sym.sort.defines().index(sym.name)
                    res = self.binenc(m,ceillog2(len(sym.sort.defines())))
                elif sym.is_numeral() and il.is_interpreted_sort(sym.sort):
                    n = get_encoding_bits(sym.sort)
                    res = self.binenc(int(sym.name),n)
                elif sym.name in self.ops and il.is_interpreted_sort(sym.sort.dom[0]):
                    args = map(recur,expr.args)
                    res = self.ops[sym.name](expr.args[0].sort,*args)
                else:
                    assert len(expr.args) == 0
                    try:
                        res = self.lit(sym)
                    except KeyError:
                        assert getdef is not None, "no definition for {} in aiger output".format(sym)
                        res = getdef(sym)
            else:
                args = map(recur,expr.args)
                if isinstance(expr,il.And):
                    res = self.andl(*args)
                elif isinstance(expr,il.Or):
                    res = self.orl(*args)
                elif isinstance(expr,il.Not):
                    res = self.notl(*args)
                elif isinstance(expr,il.Implies):
                    res = self.implies(*args)
                elif isinstance(expr,il.Iff):
                    res = self.iff(*args)
                elif il.is_eq(expr):
                    res = self.encode_equality(expr.args[0].sort,*args)
                else:
                    assert False,"unimplemented op in aiger output: {}".format(type(expr))
#            iu.dbg('expr')
#            iu.dbg('res')
            return res
        res = recur(expr)
        assert len(res) > 0
        return res

    def deflist(self,defs):
        dmap = dict((df.defines(),df.args[1]) for df in defs)
        def getdef(sym):
            if sym not in dmap:
                assert getdef is not None, "no definition for {} in aiger output".format(sym)
            val = self.eval(dmap[sym],getdef)
            self.define(sym,val)
            return val
        for df in defs:
            sym = df.defines()
            self.define(sym,self.eval(df.args[1],getdef))
    
    def set(self,sym,val):
#        iu.dbg('sym')
#        iu.dbg('val')
        assert len(val) > 0
        for x,y in zip(self.encoding[sym],val):
            self.sub.set(x,y)

    def __str__(self):
        return str(self.sub)

    def gebin(self,bits,n):
        if n == 0:
            return self.sub.true()
        if n >= 2**len(bits):
            return self.sub.false()
        hval = 2**(len(bits)-1)
        if hval <= n:
            return self.sub.andl(bits[0],self.gebin(bits[1:],n-hval))
        return self.sub.orl(bits[0],self.gebin(bits[1:],n))

    def binenc(self,m,n):
        return [(self.sub.true() if m & (1 << (n-1-i)) else self.sub.false())
                for i in range(n)]
        
    def bindec(self,bits):
        res = 0
        n = len(bits)
        for i,v in enumerate(bits):
            if isinstance(v,il.And):
                res += 1 << (n - 1 - i)
        return res

    def encode_equality(self,sort,*eterms):
        interp = thy.get_sort_theory(sort)
        n = len(interp.defines()) if il.is_enumerated_sort(interp) else 2**len(eterms[0])
        bits = ceillog2(n)
        eqs = self.sub.andl(*[self.sub.iff(x,y) for x,y in zip(*eterms)])
        alt = self.sub.andl(*[self.gebin(e,n-1) for e in eterms])
        res =  [self.sub.orl(eqs,alt)]
        return res

    def encode_plus(self,sort,x,y,cy=None):
        res = []
        if cy is None:
            cy = self.sub.false()
        for i in range(len(x)-1,-1,-1):
            res.append(self.sub.xor(self.sub.xor(x[i],y[i]),cy))
            cy = self.sub.orl(self.sub.andl(x[i],y[i]),self.sub.andl(x[i],cy),self.sub.andl(y[i],cy))
        res.reverse()
        return res

    def encode_minus(self,sort,x,y):
        ycom = self.notl(y)
        return self.encode_plus(sort,x,ycom,self.sub.true())

    def encode_times(self,sort,x,y):
        res = [self.sub.false() for _ in x]
        for i in range(0,len(x)):
            res = res[1:] + [self.sub.false()]
            res = self.encode_ite(sort,x[i],self.encode_plus(sort,res,y),res)
        return res

    def encode_lt(self,sort,x,y,cy=None):
        if cy is None:
            cy = self.sub.false()
        for i in range(len(x)-1,-1,-1):
            cy = self.sub.orl(self.sub.andl(self.sub.notl(x[i]),y[i]),self.sub.andl(self.sub.iff(x[i],y[i]),cy))
        return [cy]
            
    def encode_le(self,sort,x,y):
        return self.encode_lt(sort,x,y,cy=self.sub.true())
        
    def encode_div(self,sort,x,y):
        thing = [self.sub.false() for _ in x]
        res = []
        for i in range(0,len(x)):
            thing = thing[1:] + [x[i]]
            le = encode_le(y,thing)
            thing = self.encode_ite(sort,ls,self.encode_minus(sort,thing,y),thing)
            res.append(le)
        return res

    def encode_mod(self,sort,x,y):
        return self.encode_sub(x,self.encode_div(x,y))

    def decode_val(self,bits,v):
        interp = thy.get_sort_theory(v.sort)
        if il.is_enumerated_sort(interp):
            num = self.bindec(bits)
            vals = interp.defines()
            val = vals[num] if num < len(vals) else vals[-1]
            val = il.Symbol(val,v.sort)
        elif isinstance(interp,thy.BitVectorTheory):
            num = self.bindec(bits)
            val = il.Symbol(str(num),v.sort)
        elif il.is_boolean_sort(interp):
            val = bits[0]
        else:
            assert False,'variable has unexpected sort: {} {}'.format(v,s.sort)
        return val
        

    def get_state(self,post):
        subres = self.sub.get_state(post)
        res = dict()
        for v in self.latches:
            bits = [subres[s] for s in self.encoding[v]]
            val = self.decode_val(bits,v)
            res[v] = val
        return res

    def get_sym(self,v):
        enc = self.encoding[v]
        abits = self.sub.sym_vals(enc)
        bits = [il.And() if b == '1' else il.Or() for b in abits]
        return self.decode_val(bits,v)
        
    def get_next_sym(self,v):
        enc = self.encoding[v]
        abits = self.sub.sym_next_vals(enc)
        bits = [il.And() if b == '1' else il.Or() for b in abits]
        return self.decode_val(bits,v)

def is_finite_sort(sort):
    if il.is_function_sort(sort):
        return False
    interp = thy.get_sort_theory(sort)
    return (il.is_enumerated_sort(interp) or 
            isinstance(interp,thy.BitVectorTheory) or
            il.is_boolean_sort(interp))

def sort_values(sort):
    interp = thy.get_sort_theory(sort)
    if il.is_enumerated_sort(interp):
        return [il.Symbol(s,sort) for s in interp.extension]
    if isinstance(interp,thy.BitVectorTheory):
        if interp.bits > 8:
            raise iu.IvyError(None,'Cowardly refusing to enumerate the type bv[{}]'.format(interp.bits))
        return [il.Symbol(str(i),sort) for i in range(2**interp.bits)]  
    if il.is_boolean_sort(interp):
        return [il.Or(),il.And()]
    assert False,sort
    

# Expand the axiom schemata into axioms, for a given collection of
# function and constant symbols.

class Match(object):
    def __init__(self):
        self.stack = [[]]
        self.map = dict()
    def add(self,x,y):
        self.map[x] = y
        self.stack[-1].append(x)
    def push(self):
        self.stack.append([])
    def pop(self):
        for x in self.stack.pop():
            del self.map[x]
    def unify(self,x,y):
        if x not in self.map:
            if x.name.endswith('_finite') and not is_finite_sort(y):
                return False  # 
            self.add(x,y)
            return True
        return self.map[x] == y
    def unify_lists(self,xl,yl):
        if len(xl) != len(yl):
            return False
        for x,y in zip(xl,yl):
            if not self.unify(x,y):
                return False
        return True
    

def str_map(map):
    return '{' + ','.join('{}:{}'.format(x,y) for x,y in map.iteritems()) + '}'

def match_schema_prems(prems,sort_constants,funs,match):
    if len(prems) == 0:
        yield match.map.copy()
    else:
        prem = prems.pop()
        if isinstance(prem,ivy_ast.ConstantDecl):
            sym = prem.args[0]
            if il.is_function_sort(sym.sort):
                sorts = sym.sort.dom + (sym.sort.rng,)
                for f in funs:
                    fsorts = f.sort.dom + (f.sort.rng,)
                    match.push()
                    if match.unify_lists(sorts,fsorts):
                        match.add(sym,f)
                        for m in match_schema_prems(prems,sort_constants,funs,match):
                            yield m
                    match.pop()
            else:
                if sym.sort in match.map:
                    cands = sort_constants[match.map[sym.sort]]
                else:
                    cands = [s for v in sort_constants.values() for s in v]
                for cand in cands:
                    match.push()
                    if match.unify(sym.sort,cand.sort):
                        match.add(sym,cand)
                        for m in match_schema_prems(prems,sort_constants,funs,match):
                            yield m
                    match.pop()
        elif isinstance(prem,il.UninterpretedSort):
            for m in match_schema_prems(prems,sort_constants,funs,match):
                yield m
        prems.append(prem)
            
def apply_match(match,fmla):
    """ apply a match to a formula. 

    In effect, substitute all symbols in the match with the
    corresponding lambda terms and apply beta reduction
    """

    args = [apply_match(match,f) for f in fmla.args]
    if il.is_app(fmla):
        if fmla.rep in match:
            func = match[fmla.rep]
            return func(*args)
    elif il.is_binder(fmla):
        vs = [apply_match(match,v) for v in fmla.variables]
        return fmla.clone_binder(vs,apply_match(match,fmla.body))
    elif il.is_variable(fmla):
        return il.Variable(fmla.name,match.get(fmla.sort,fmla.sort))
    return fmla.clone(args)

def expand_schemata(mod,sort_constants,funs):
    match = Match()
    res = []
    for s in mod.sig.sorts.values():
        if not il.is_function_sort(s):
            match.add(s,s)
    for name,lf in mod.schemata.iteritems():
        schema = lf.formula
        if any(name.startswith(pref) for pref in ['rec[','lep[','ind[']):
            continue
        conc = schema.args[-1]
        for m in match_schema_prems(list(schema.args[:-1]),sort_constants,funs,match):
#            iu.dbg('str_map(m)')
#            iu.dbg('conc')
            inst = apply_match(m,conc)
            res.append(ivy_ast.LabeledFormula(ivy_ast.Atom(name),inst))
    return res
                
# This is where we do pattern-based eager instantiation of the axioms

def instantiate_axioms(mod,stvars,trans,invariant,sort_constants,funs):

    # Expand the axioms schemata into axioms

    print 'Expanding schemata...'
    axioms = mod.labeled_axioms + expand_schemata(mod,sort_constants,funs)
    for a in axioms:
        logfile.write('axiom {}\n'.format(a))

    print 'Instantiating axioms...'

    # Get all the triggers. For now only automatic triggers

    def get_trigger(expr,vs):
        if il.is_quantifier(expr) or il.is_variable(expr):
            return None
        for a in expr.args:
            r = get_trigger(a,vs)
            if r is not None:
                return r
        if il.is_app(expr) or il.is_eq(expr):
            evs = ilu.used_variables_ast(expr)
            if all(v in evs for v in vs):
                return expr

    triggers = []
    for ax in axioms:
        fmla = ax.formula
        vs = list(ilu.used_variables_ast(fmla))
        if vs:
            trig = get_trigger(fmla,vs)
            if trig is not None:
#                iu.dbg('trig')
#                iu.dbg('ax')
                triggers.append((trig,ax))

    insts = set()
    global inst_list # python lamemess -- should be local but inner function cannot access
    inst_list = []

    def match(pat,expr,mp):
        if il.is_variable(pat):
            if pat in mp:
                return expr == mp[pat]
            mp[pat] = expr
            return True
        if il.is_app(pat):
            return (il.is_app(expr) and pat.rep == expr.rep
                    and all(match(x,y,mp) for x,y in zip(pat.args,expr.args)))
        if il.is_quantifier(pat):
            return False
        if type(pat) is not type(expr):
            return False
        if il.is_eq(expr):
            px,py = pat.args
            ex,ey = expr.args
            if px.sort != ex.sort:
                return False
            save = mp.copy()
            if match(px,ex,mp) and match(py,ey,mp):
                return True
            mp.clear()
            mp.update(save)
            return match(px,ey,mp) and match(py,ex,mp)
        return all(match(x,y,mp) for x,y in zip(pat.args,expr.args))
                                                                
    # TODO: make sure matches are ground
    def recur(expr):
        for e in expr.args:
            recur(e)
        for trig,ax in triggers:
            mp = dict()
            if match(trig,expr,mp):
                fmla = normalize(il.substitute(ax.formula,mp))
                if fmla not in insts:
                    insts.add(fmla)
                    inst_list.append(fmla)

    # match triggers against the defs and fmlas and invariant
    for f in trans.defs + trans.fmlas + [invariant]:
        recur(f)
                    
    for f in inst_list:
        logfile.write('    {}\n'.format(f))
    return inst_list


# This eliminates ite's over non-finite sorts by translating (x if c
# else y) to a fresh variable v with an added constraint (v = x if c
# else v = y). As an optimization, (z = x if c else y) is converted to
# (z = x if c else z = y) to avoid introducing a constraint.
#
# This lowering is useful, since we avoid having to introduce axioms
# for ite.

ite_ctr = 0
def elim_ite(expr,cnsts):
    if isinstance(expr,il.Ite):
        global ite_ctr
        c,x,y = expr.args
        if not is_finite_sort(x.sort):
            v = il.Symbol('__ite[{}]'.format(ite_ctr),x.sort)
            ite_ctr += 1
            cnsts.append(il.Ite(elim_ite(c,cnsts),elim_ite(il.Equals(v,x),cnsts),elim_ite(il.Equals(v,y),cnsts)))
            return v
    if il.is_eq(expr):
        v,e = expr.args
        if isinstance(e,il.Ite):
            c,x,y = e.args
            if not is_finite_sort(x.sort):
                return il.Ite(elim_ite(c,cnsts),elim_ite(il.Equals(v,x),cnsts),elim_ite(il.Equals(v,y),cnsts))
    return expr.clone([elim_ite(e,cnsts) for e in expr.args])


# Here we get the constants over which to instantiate universal quantifiers. For now,
# we are just using the ones that occur in the invariant

def mine_constants(mod,trans,invariant):
    res = defaultdict(list)
    for c in ilu.used_symbols_ast(invariant):
        if not il.is_function_sort(c.sort) and tr.is_skolem(c):
            res[c.sort].append(c)
#    iu.dbg('res')
    return res

def mine_constants2(mod,trans,invariant):
    defnd = set(dfn.defines() for dfn in trans.defs)
    res = defaultdict(list)
    syms = ilu.used_symbols_ast(invariant)
    syms.update(ilu.used_symbols_clauses(trans))
    for c in syms:
        if not il.is_function_sort(c.sort):
            res[c.sort].append(c)
#    iu.dbg('res')
    return res

# Tricky: if an atomic proposition has a next variable in it, but no curremnt versions of state
# variables, it is a candidate to become an abstract state variable. THis function computes the
# current state version of such an express from its next state version, or returns None if the expression
# does not qualify.
# 

def prev_expr(stvarset,expr,sort_constants):
    if any(sym in stvarset or tr.is_skolem(sym) and not sym in sort_constants[sym.sort]
           for sym in ilu.symbols_ast(expr)):
        return None
    news = [sym for sym in ilu.used_symbols_ast(expr) if tr.is_new(sym)]
    if news:
        rn = dict((sym,tr.new_of(sym)) for sym in news)
        return ilu.rename_ast(expr,rn)
    return None        

# Here we deal with normalizing of terms. In particular, we order the
# equalities and convert x = x to true. This means we don't have to
# axiomatize symmetry and reflexivity. We assume terms we normalize
# are ground.

def term_ord(x,y):
    t1,t2 = str(type(x)),str(type(y))
    if t1 < t2:
        return -1
    if t1 > t2:
        return 1
    if il.is_app(x):
        if x.rep.name < y.rep.name:
            return -1
        if x.rep.name > y.rep.name:
            return 1
    l1,l2 = len(x.args),len(y.args)
    if l1 < l2:
        return -1
    if l1 > l2:
        return 1
    for x1,y1 in zip(x.args,y.args):
        res = term_ord(x1,y1)
        if res != 0:
            return res
    return 0

def clone_normal(expr,args):
    if il.is_eq(expr):
        x,y = args
        if x == y:
            return il.And()
        to = term_ord(x,y)
#        print 'term_ord({},{}) = {}'.format(x,y,to)
        if to == 1:
            x,y = y,x
        return expr.clone([x,y])
    return expr.clone(args)

def normalize(expr):
    if il.is_macro(expr):
        return normalize(il.expand_macro(expr))
    return clone_normal(expr,map(normalize,expr.args))
    

# Class for eliminating quantifiers by finite instantiate. Here,
# sort_constants is a map from each sort to a list of the grounds
# terms used to instantiate it.  For each quantified subformula, we
# generate a collection of constraints that are instances of the
# quantifier instantion axiom. As a side effect, we replace each
# quantified subformula by a definition, to avoid many copies of the
# subformula.

class Qelim(object):
    def __init__(self,sort_constants,sort_constants2):
        self.syms = dict()     # map from quantified formulas to proposition variables
        self.syms_ctr = 0      # counter for fresh symbols
        self.fmlas = []        # constraints added
        self.sort_constants = sort_constants
        self.sort_constants2 = sort_constants2
    def fresh(self,expr):
        res = il.Symbol('__qe[{}]'.format(self.syms_ctr),expr.sort)
        self.syms[expr] = res
        self.syms_ctr += 1
        return res
    def get_consts(self,sort,sort_constants):
        if is_finite_sort(sort):   # enumerate quantifiers over finite sorts
            return sort_values(sort)
        return sort_constants[sort]
    def qe(self,expr,sort_constants):
        if il.is_quantifier(expr):
            old = self.syms.get(expr,None)
            if old is not None:
                return old
            res = self.fresh(expr)
            consts = [self.get_consts(x.sort,sort_constants) for x in expr.variables]
            values = itertools.product(*consts)
            maps = [dict(zip(expr.variables,v)) for v in values]
            insts = [normalize(il.substitute(expr.body,m)) for m in maps]
#            for i in insts:
#                print '    {}'.format(i)
            for inst in insts:
                c = il.Implies(res,inst) if il.is_forall(expr) else il.Implies(inst,res)
                self.fmlas.append(c)
            return res
        if il.is_macro(expr):
            return self.qe(il.expand_macro(expr),sort_constants)
        return clone_normal(expr,[self.qe(e,sort_constants) for e in expr.args])
    def __call__(self,trans,invariant,indhyps):
        # apply to the transition relation
        new_defs = [self.qe(defn,self.sort_constants) for defn in trans.defs]
        new_fmlas = [self.qe(il.close_formula(fmla),self.sort_constants) for fmla in trans.fmlas]
        # apply to the invariant
        invariant = self.qe(invariant,self.sort_constants)
        # apply to inductive hyps
        indhyps = [self.qe(fmla,self.sort_constants2) for fmla in indhyps]
        # add the transition constraints to the new trans
        trans = ilu.Clauses(new_fmlas+indhyps+self.fmlas,new_defs)
        return trans,invariant
        

def uncompose_annot(annot):
    if not isinstance(annot,ia.ComposeAnnotation):
        return []
    res = uncompose_annot(annot.args[0])
    res.append(annot.args[1])
    return res
    
def unite_annot(annot):
    if isinstance(annot,ia.RenameAnnotation):
        return [(annot.map.get(x,x),ia.RenameAnnotation(y,annot.map)) for (x,y) in unite_annot(annot.arg)]
    if not isinstance(annot,ia.IteAnnotation):
        return []
    res = unite_annot(annot.elseb)
    res.append((annot.cond,annot.thenb))
    return res

class MatchHandler(object):
    def eval(self,cond):
        if il.is_false(cond):
            return False
        if il.is_true(cond):
            return True
        print 'assuming: {}'.format(cond)
        return True
    def handle(self,action,env):
        print '{}{}'.format(action.lineno,action)
        print 'env: {}'.format('{'+','.join('{}:{}'.format(x,y) for x,y in env.iteritems())+'}')
        
    
def match_annotation(action,annot,handler):
    def recur(action,annot,env,pos=None):
        if isinstance(annot,ia.RenameAnnotation):
            save = dict()
            for x,y in annot.map.iteritems():
                if x in env:
                    save[x] = env[x]
                env[x] = env.get(y,y)
            recur(action,annot.arg,env,pos)
            env.update(save)
            return
        if isinstance(action,ia.Sequence):
            if pos is None:
                pos = len(action.args)
            if pos == 0:
                assert isinstance(annot,ia.EmptyAnnotation),annot
                return
            if not isinstance(annot,ia.ComposeAnnotation):
                iu.dbg('len(action.args)')
                iu.dbg('pos')
                iu.dbg('annot')
            assert isinstance(annot,ia.ComposeAnnotation)
            recur(action,annot.args[0],env,pos-1)
            recur(action.args[pos-1],annot.args[1],env)
            return
        if isinstance(action,ia.IfAction):
            assert isinstance(annot,ia.IteAnnotation),annot
            rncond = env.get(annot.cond,annot.cond)
            try:
                cond = handler.eval(rncond)
            except KeyError:
                print '{}skipping conditional'.format(action.lineno)
#                exit(1)
#                iu.dbg('str_map(env)')
#                iu.dbg('env.get(annot.cond,annot.cond)')
                return
            if cond:
                recur(action.args[1],annot.thenb,env)
            else:
                if len(action.args) > 2:
                    recur(action.args[2],annot.elseb,env)
            return
        if isinstance(action,ia.ChoiceAction):
            assert isinstance(annot,ia.IteAnnotation)
            
            annots = unite_annot(annot)
            assert len(annots) == len(action.args)
            for act,(cond,ann) in reversed(zip(action.args,annots)):
                if handler.eval(cond):
                    recur(act,ann,env)
                    return
            assert False,'problem in match_annotation'
        if isinstance(action,ia.CallAction):
            callee = im.module.actions[action.args[0].rep]
            seq = ia.Sequence(ia.IgnoreAction(),callee,ia.ReturnAction())
#            seq = ia.Sequence(*([ia.Sequence() for x in callee.formal_params]
#                             + [callee] 
#                             + [ia.Sequence() for x in callee.formal_returns]))
            recur(seq,annot,env)
            return
        if isinstance(action,ia.ReturnAction):
            handler.do_return(action,env)
            return
        if isinstance(action,ia.IgnoreAction):
                return
        if isinstance(action,ia.LocalAction):
            recur(action.args[-1],annot,env)
            return
        handler.handle(action,env)
    recur(action,annot,dict())
    
def checked(thing):
    return ia.checked_assert.value in ["",thing.lineno]

def add_err_flag(action,erf,errconds):
    if isinstance(action,ia.AssertAction):
        if checked(action):
            print "{}Model checking guarantee".format(action.lineno)
            errcond = ilu.dual_formula(il.drop_universals(action.args[0]))
            res = ia.AssignAction(erf,il.Or(erf,errcond))
            errconds.append(errcond)
            res.lineno = action.lineno
            return res
        if isinstance(action,ia.SubgoalAction):
#            print "skipping subgoal at line {}".format(action.lineno)
            return ia.Sequence()
    if isinstance(action,ia.AssumeAction) or isinstance(action,ia.AssertAction):
        if isinstance(action,ia.AssertAction):
            print "assuming assertion at line {}".format(action.lineno)
        res = ia.AssumeAction(il.Or(erf,action.args[0])) 
        res.lineno = action.lineno
        return res
    if isinstance(action,(ia.Sequence,ia.ChoiceAction,ia.EnvAction,ia.BindOldsAction)):
        return action.clone([add_err_flag(a,erf,errconds) for a in action.args])
    if isinstance(action,ia.IfAction):
        return action.clone([action.args[0]] + [add_err_flag(a,erf,errconds) for a in action.args[1:]])
    if isinstance(action,ia.LocalAction):
        return action.clone(action.args[:-1] + [add_err_flag(action.args[-1],erf,errconds)])
    return action

def add_err_flag_mod(mod,erf,errconds):
    for actname in list(mod.actions):
        action = mod.actions[actname]
        new_action = add_err_flag(action,erf,errconds)
        new_action.formal_params = action.formal_params
        new_action.formal_returns = action.formal_returns
        mod.actions[actname] = new_action
       
# This translates finite function applications to table lookups.  This
# is preferable to using axioms if the argument types are large, since
# it prevents copying the argument expressions. Also, the result is a
# circuit (as opposed to a set of constraints) which might be helpful
# to ABC.


def to_table_lookup(trans,invariant):
    new_defs = []
    global to_table_lookup_counter
    to_table_lookup_counter = 0
    
    def arg_sym(sort):
        global to_table_lookup_counter
        res = il.Symbol('__arg[{}]'.format(to_table_lookup_counter),sort)
        to_table_lookup_counter += 1
        return res

    def recur(expr):
        if (il.is_app(expr) and len(expr.args) > 0 and
            not il.is_interpreted_symbol(expr.func) and
            all(is_finite_sort(a.sort) for a in expr.args)):
            
            argsyms = []
            consts = []
            for x in expr.args:
                cs = sort_values(x.sort)
                if x in cs:
                    argsyms.append(x)
                    consts.append([x])
                else:
                    consts.append(cs)
                    if il.is_constant(x):
                        argsyms.append(x)
                    else:
                        sym = arg_sym(x.sort)
                        argsyms.append(sym)
                        new_defs.append(il.Definition(sym,recur(x)))
            values = list(itertools.product(*consts))
            res = (expr.rep)(*values[0])
            for v in values[1:]:
                res = il.Ite(il.And(*[il.Equals(x,y) for x,y in zip(argsyms,v)]),(expr.rep)(*v),res)
            return res
        return expr.clone(map(recur,expr.args))


    # skip this step if there aren't any finite-domain functions
    if not any(il.is_function_sort(func.sort) and len(func.sort.dom) > 0 and not il.is_interpreted_symbol(func) and
               all(is_finite_sort(sort) for sort in func.sort.dom) for func in il.all_symbols()):
        return trans,invariant

    defs = [recur(df) for df in trans.defs]
    fmlas = [recur(fmla) for fmla in trans.fmlas]
    trans = ilu.Clauses(fmlas,defs + new_defs)
    new_defs = []
    invariant = recur(invariant)
    if new_defs:
        invariant = il.Implies(il.And(*[df.to_constraint() for df in new_defs]),invariant)
    return trans,invariant


def to_aiger(mod,ext_act):

    erf = il.Symbol('err_flag',il.find_sort('bool'))
    errconds = []
    add_err_flag_mod(mod,erf,errconds)

    # we use a special state variable __init to indicate the initial state

    ext_acts = [mod.actions[x].add_label(x) for x in sorted(mod.public_actions)]
    ext_act = ia.EnvAction(*ext_acts)

    init_var = il.Symbol('__init',il.find_sort('bool')) 
    init = add_err_flag(ia.Sequence(*([a for n,a in mod.initializers]+[ia.AssignAction(init_var,il.And())])),erf,errconds)
    action = ia.Sequence(ia.AssignAction(erf,il.Or()),ia.IfAction(init_var,ext_act,init))
    
    # get the invariant to be proved, replacing free variables with
    # skolems. First, we apply any proof tactics.

    pc = ivy_proof.ProofChecker(mod.labeled_axioms,mod.definitions,mod.schemata)
    pmap = dict((lf.id,p) for lf,p in mod.proofs)
    conjs = []
    for lf in mod.labeled_conjs:
        if not checked(lf):
#            print 'skipping {}'.format(lf)
            continue
        print "{}Model checking invariant".format(lf.lineno)
        if lf.id in pmap:
            proof = pmap[lf.id]
            subgoals = pc.admit_proposition(lf,proof)
            conjs.extend(subgoals)
        else:
            conjs.append(lf)

    invariant = il.And(*[il.drop_universals(lf.formula) for lf in conjs])
#    iu.dbg('invariant')
    skolemizer = lambda v: ilu.var_to_skolem('__',il.Variable(v.rep,v.sort))
    vs = ilu.used_variables_in_order_ast(invariant)
    sksubs = dict((v.rep,skolemizer(v)) for v in vs)
    invariant = ilu.substitute_ast(invariant,sksubs)
    invar_syms = ilu.used_symbols_ast(invariant)
    
    # compute the transition relation

    stvars,trans,error = action.update(mod,None)
#    iu.dbg('trans')
    

#    print 'action : {}'.format(action)
#    print 'annotation: {}'.format(trans.annot)
    annot = trans.annot
#    match_annotation(action,annot,MatchHandler())
    
    indhyps = [il.close_formula(il.Implies(init_var,lf.formula)) for lf in mod.labeled_conjs]
#    trans = ilu.and_clauses(trans,indhyps)

    # save the original symbols for trace
    orig_syms = ilu.used_symbols_clauses(trans)
    orig_syms.update(ilu.used_symbols_ast(invariant))
                     
    # TODO: get the axioms (or maybe only the ground ones?)

    # axioms = mod.background_theory()

    # rn = dict((sym,tr.new(sym)) for sym in stvars)
    # next_axioms = ilu.rename_clauses(axioms,rn)
    # return ilu.and_clauses(axioms,next_axioms)

    funs = set()
    for df in trans.defs:
        funs.update(ilu.used_symbols_ast(df.args[1]))
    for fmla in trans.fmlas:
        funs.update(ilu.used_symbols_ast(fmla))
#   funs = ilu.used_symbols_clauses(trans)
    funs.update(ilu.used_symbols_ast(invariant))
    funs = set(sym for sym in funs if  il.is_function_sort(sym.sort))

    # Propositionally abstract

    # step 1: get rid of definitions of non-finite symbols by turning
    # them into constraints

    new_defs = []
    new_fmlas = []
    for df in trans.defs:
        if len(df.args[0].args) == 0 and is_finite_sort(df.args[0].sort):
            new_defs.append(df)
        else:
            fmla = df.to_constraint()
            new_fmlas.append(fmla)
    trans = ilu.Clauses(new_fmlas+trans.fmlas,new_defs)

    # step 2: get rid of ite's over non-finite sorts, by introducing constraints

    cnsts = []
    new_defs = [elim_ite(df,cnsts) for df in trans.defs]
    new_fmlas = [elim_ite(fmla,cnsts) for fmla in trans.fmlas]
    trans = ilu.Clauses(new_fmlas+cnsts,new_defs)
    
    # step 3: eliminate quantfiers using finite instantiations

    from_asserts = il.And(*[il.Equals(x,x) for x in ilu.used_symbols_ast(il.And(*errconds)) if
                            tr.is_skolem(x) and not il.is_function_sort(x.sort)])
#    iu.dbg('from_asserts')
    invar_syms.update(ilu.used_symbols_ast(from_asserts))
    sort_constants = mine_constants(mod,trans,il.And(invariant,from_asserts))
    sort_constants2 = mine_constants2(mod,trans,invariant)
    print '\nInstantiating quantifiers (see {} for instantiations)...'.format(logfile_name)
    logfile.write('\ninstantiations:\n')
    trans,invariant = Qelim(sort_constants,sort_constants2)(trans,invariant,indhyps)
    
    
#    print 'after qe:'
#    print 'trans: {}'.format(trans)
#    print 'invariant: {}'.format(invariant)

    # step 4: instantiate the axioms using patterns

    # We have to condition both the transition relation and the
    # invariant on the axioms, so we define a boolean symbol '__axioms'
    # to represent the axioms.

    axs = instantiate_axioms(mod,stvars,trans,invariant,sort_constants,funs)
    ax_conj = il.And(*axs)
    ax_var = il.Symbol('__axioms',ax_conj.sort)
    ax_def = il.Definition(ax_var,ax_conj)
    invariant = il.Implies(ax_var,invariant)
    trans = ilu.Clauses(trans.fmlas+[ax_var],trans.defs+[ax_def])

    # step 4b: handle the finite-domain functions specially

    trans,invariant= to_table_lookup(trans,invariant)
    
    # step 5: eliminate all non-propositional atoms by replacing with fresh booleans
    # An atom with next-state symbols is converted to a next-state symbol if possible

    stvarset = set(stvars)
    prop_abs = dict()  # map from atoms to proposition variables
    global prop_abs_ctr  # sigh -- python lameness
    prop_abs_ctr = 0   # counter for fresh symbols
    new_stvars = []    # list of fresh symbols
    finite_syms = []   # list of symbols not abstracted
    finite_syms_set = set()

    # get the propositional abstraction of an atom
    def new_prop(expr):
        res = prop_abs.get(expr,None)
        if res is None:
            prev = prev_expr(stvarset,expr,sort_constants)
            if prev is not None:
#                print 'stvar: old: {} new: {}'.format(prev,expr)
                pva = new_prop(prev)
                res = tr.new(pva)
                new_stvars.append(pva)
                prop_abs[expr] = res  # prevent adding this again to new_stvars
            else:
                global prop_abs_ctr
                res = il.Symbol('__abs[{}]'.format(prop_abs_ctr),expr.sort)
#                print '{} = {}'.format(res,expr)
                prop_abs[expr] = res
                prop_abs_ctr += 1
        return res

    # propositionally abstract an expression
    global mk_prop_fmlas
    mk_prop_fmlas = []
    def mk_prop_abs(expr):
        if (il.is_quantifier(expr) or
            len(expr.args) > 0 and (
                any(not is_finite_sort(a.sort) for a in expr.args)
                or il.is_app(expr) and not il.is_interpreted_symbol(expr.func))):
            return new_prop(expr)
        if (il.is_constant(expr) and not il.is_numeral(expr)
            and expr not in il.sig.constructors and expr not in finite_syms_set and not tr.is_skolem(expr)):
            finite_syms_set.add(expr)
            finite_syms.append(expr)
        return expr.clone(map(mk_prop_abs,expr.args))
    
    # apply propositional abstraction to the transition relation
    new_defs = map(mk_prop_abs,trans.defs)
    new_fmlas = [mk_prop_abs(il.close_formula(fmla)) for fmla in trans.fmlas]

    # find any immutable abstract variables, and give them a next definition

    def my_is_skolem(x):
        res = tr.is_skolem(x) and x not in invar_syms
        return res    
    def is_immutable_expr(expr):
        res = not any(my_is_skolem(sym) or tr.is_new(sym) or sym in stvarset for sym in ilu.used_symbols_ast(expr))
        return res
    for expr,v in itertools.chain(prop_abs.iteritems(),((x,x) for x in finite_syms)):
        if is_immutable_expr(expr):
            new_stvars.append(v)
            logfile.write('new state: {}\n'.format(expr))
            new_defs.append(il.Definition(tr.new(v),v))

    trans = ilu.Clauses(new_fmlas+mk_prop_fmlas,new_defs)

    # apply propositional abstraction to the invariant
    invariant = mk_prop_abs(invariant)

    # create next-state symbols for atoms in the invariant (is this needed?)
    rn = dict((sym,tr.new(sym)) for sym in stvars)
    mk_prop_abs(ilu.rename_ast(invariant,rn))  # this is to pick up state variables from invariant

    # update the state variables by removing the non-finite ones and adding the fresh state booleans
    stvars = [sym for sym in stvars if is_finite_sort(sym.sort)] + new_stvars

#    iu.dbg('trans')
#    iu.dbg('stvars')
#    iu.dbg('invariant')
#    exit(0)

    # For each state var, create a variable that corresponds to the input of its latch
    # Also, havoc all the state bits except the init flag at the initial time. This
    # is needed because in aiger, all latches start at 0!

    def fix(v):
        return v.prefix('nondet')
    def curval(v):
        return v.prefix('curval')
    def initchoice(v):
        return v.prefix('initchoice')
    stvars_fix_map = dict((tr.new(v),fix(v)) for v in stvars)
    stvars_fix_map.update((v,curval(v)) for v in stvars if v != init_var)
    trans = ilu.rename_clauses(trans,stvars_fix_map)
#    iu.dbg('trans')
    new_defs = trans.defs + [il.Definition(ilu.sym_inst(tr.new(v)),ilu.sym_inst(fix(v))) for v in stvars]
    new_defs.extend(il.Definition(curval(v),il.Ite(init_var,v,initchoice(v))) for v in stvars if  v != init_var)
    trans = ilu.Clauses(trans.fmlas,new_defs)
    
    # Turn the transition constraint into a definition
    
    cnst_var = il.Symbol('__cnst',il.find_sort('bool'))
    new_defs = list(trans.defs)
    new_defs.append(il.Definition(tr.new(cnst_var),fix(cnst_var)))
    new_defs.append(il.Definition(fix(cnst_var),il.Or(cnst_var,il.Not(il.And(*trans.fmlas)))))
    stvars.append(cnst_var)
    trans = ilu.Clauses([],new_defs)
    
    # Input are all the non-defined symbols. Output indicates invariant is false.

#    iu.dbg('trans')
    def_set = set(df.defines() for df in trans.defs)
    def_set.update(stvars)
#    iu.dbg('def_set')
    used = ilu.used_symbols_clauses(trans)
    used.update(ilu.symbols_ast(invariant))
    inputs = [sym for sym in used if
              sym not in def_set and not il.is_interpreted_symbol(sym)]
    fail = il.Symbol('__fail',il.find_sort('bool'))
    outputs = [fail]
    

#    iu.dbg('trans')
    
    # make an aiger

    aiger = Encoder(inputs,stvars,outputs)
    comb_defs = [df for df in trans.defs if not tr.is_new(df.defines())]

    invar_fail = il.Symbol('invar__fail',il.find_sort('bool'))  # make a name for invariant fail cond
    comb_defs.append(il.Definition(invar_fail,il.Not(invariant)))

    aiger.deflist(comb_defs)
    for df in trans.defs:
        if tr.is_new(df.defines()):
            aiger.set(tr.new_of(df.defines()),aiger.eval(df.args[1]))
    miter = il.And(init_var,il.Not(cnst_var),il.Or(invar_fail,il.And(fix(erf),il.Not(fix(cnst_var)))))
    aiger.set(fail,aiger.eval(miter))

#    aiger.sub.debug()

    # make a decoder for the abstract propositions

    decoder = dict((y,x) for x,y in prop_abs.iteritems())
    for sym in aiger.inputs + aiger.latches:
        if sym not in decoder and sym in orig_syms:
            decoder[sym] = sym

    cnsts = set(sym for syms in sort_constants.values() for sym in syms)
    return aiger,decoder,annot,cnsts,action,stvarset

def badwit():
    raise iu.IvyError(None,'model checker returned mis-formated witness')

# This is an adaptor to create a trace as an ART. 

class IvyMCTrace(art.AnalysisGraph):
    def __init__(self,stvals):
#        iu.dbg('stvals')
        def abstractor(state):
            state.clauses = ilu.Clauses(stvals)
            state.universes = dict() # indicates this is a singleton state
        art.AnalysisGraph.__init__(self,initializer=abstractor)
    def add_state(self,stvals,action):
#        iu.dbg('stvals')
        self.add(itp.State(value=ilu.Clauses(stvals),expr=itp.action_app(action,self.states[-1]),label='ext'))

class AigerMatchHandler(object):
    def __init__(self,aiger,decoder,cnsts,stvarset,current):
        self.aiger,self.decoder,self.cnsts,self.stvarset = aiger,decoder,cnsts,stvarset
        self.current = current
    def eval(self,cond):
        if il.is_false(cond):
            res = False
        elif il.is_true(cond):
            res =  True
        else:
            res = il.is_true(self.aiger.get_sym(cond))
#        print 'eval: {} = {}'.format(cond,res)
        return res

    def do_return(self,action,env):
        pass

    def handle(self,action,env):

        def my_is_skolem(x):
            return tr.is_skolem(x) and x not in self.cnsts

        def show_sym(v,decd,val):
            iu.dbg('decd')
            iu.dbg('val')
            if all(x in inv_env or not my_is_skolem(x) and
                   not tr.is_new(x) and x not in env for x in ilu.used_symbols_ast(decd)):
                expr = ilu.rename_ast(decd,inv_env)
                if not tr.is_new(expr.rep):
                    if il.is_constant(expr) and expr in il.sig.constructors:
                        return
                    if not (expr in self.current and self.current[expr] == val):
                        print '        {} = {}'.format(expr,val)
                        self.current[expr] = val

        if hasattr(action,'lineno'):
#            print '        env: {}'.format('{'+','.join('{}:{}'.format(x,y) for x,y in env.iteritems())+'}')
            inv_env = dict((y,x) for x,y in env.iteritems() if not my_is_skolem(x))
            for v in self.aiger.inputs:
                iu.dbg('v')
                if v in self.decoder:
                    show_sym(v,self.decoder[v],self.aiger.get_sym(v))
            rn = dict((x,tr.new(x)) for x in self.stvarset)
            for v in self.aiger.latches:
                if v in self.decoder:
                    decd = self.decoder[v]
                    show_sym(v,ilu.rename_ast(decd,rn),self.aiger.get_next_sym(v))

            print '    {}{}'.format(action.lineno,action)
        
class AigerMatchHandler2(ivy_trace.TraceBase):
    def __init__(self,aiger,decoder,cnsts,stvarset,current):
        ivy_trace.TraceBase.__init__(self)
        self.aiger,self.decoder,self.cnsts,self.stvarset = aiger,decoder,cnsts,stvarset
        self.current = current
    def eval(self,cond):
        if il.is_false(cond):
            res = False
        elif il.is_true(cond):
            res =  True
        else:
            res = il.is_true(self.aiger.get_sym(cond))
#        print 'eval: {} = {}'.format(cond,res)
        return res

    def clone(self):
        return AigerMatchHandler2(self.aiger,self.decoder,self.cnsts,self.stvarset,self.current)

    def get_universes(self):
        return None
        
    def do_return(self,action,env):
        pass

    def new_state(self,env):

        def my_is_skolem(x):
            return tr.is_skolem(x) and x not in self.cnsts

        def show_sym(v,decd,val,eqns):
            if all(x in inv_env or not my_is_skolem(x) and
                   not tr.is_new(x) and x not in env for x in ilu.used_symbols_ast(decd)):
                expr = ilu.rename_ast(decd,inv_env)
                if not tr.is_new(expr.rep):
                    if il.is_constant(expr) and expr in il.sig.constructors:
                        return
                    eqns.append(il.Equals(expr,val))

        inv_env = dict((y,x) for x,y in env.iteritems() if not my_is_skolem(x))
        eqns = []
        for v in self.aiger.inputs:
            if v in self.decoder:
                show_sym(v,self.decoder[v],self.aiger.get_sym(v),eqns)
        rn = dict((x,tr.new(x)) for x in self.stvarset)
        for v in self.aiger.latches:
            if v in self.decoder:
                decd = self.decoder[v]
                show_sym(v,ilu.rename_ast(decd,rn),self.aiger.get_next_sym(v),eqns)

        self.add_state(eqns)
        
    def final_state(self):
        self.aiger.sub.next()

        post = self.aiger.sub.latch_vals()  # use this, since file can be wrong!
        stvals = []
        stmap = self.aiger.get_state(post)                     
#            iu.dbg('stmap')
        for v in self.aiger.latches: # last two are used for encoding
            if v in self.decoder and v.name != '__init':
                val = stmap[v]
                if val is not None:
                    stvals.append(il.Equals(self.decoder[v],val))
        self.add_state(stvals)


def aiger_witness_to_ivy_trace(aiger,witnessfilename,action,stvarset,ext_act,annot,consts,decoder):
    with open(witnessfilename,'r') as f:
        res = f.readline().strip()
        if res != '1':
            badwit()
        tr = None
        aiger.sub.reset()
        lines = []
        for line in f:
            if line.endswith('\n'):
                line = line[:-1]
            lines.append(line)
        print '\nCounterexample follows:'
        print 80*'-'
        current = dict()
        count = 0
        for line in lines:
            if tr:
                print ''
            cols = line.split(' ')
#            iu.dbg('cols')
            if len(cols) != 4:
                badwit()
            pre,inp,out,post = cols
            aiger.sub.step(inp)
            count += 1
            if count == len(lines):
                invar_fail = il.Symbol('invar__fail',il.find_sort('bool'))
                if il.is_true(aiger.get_sym(invar_fail)):
                    break
            # print 'inputs:'
            # for v in aiger.inputs:
            #     if v in decoder:
            #         print '    {} = {}'.format(decoder[v],aiger.get_sym(v))
            print 'path:'
            match_annotation(action,annot,AigerMatchHandler(aiger,decoder,consts,stvarset,current))
            aiger.sub.next()
            post = aiger.sub.latch_vals()  # use this, since file can be wrong!
            stvals = []
            stmap = aiger.get_state(post)                     
#            iu.dbg('stmap')
            current = dict()
            for v in aiger.latches: # last two are used for encoding
                if v in decoder and v.name != '__init':
                    val = stmap[v]
                    if val is not None:
                        stvals.append(il.Equals(decoder[v],val))
                        current[decoder[v]] = val
            print 'state:'
            for stval in stvals:
                print '    {}'.format(stval)
            if not tr:
                tr = IvyMCTrace(stvals) # first transition is initialization
            else:
                tr.add_state(stvals,ext_act) # remainder are exported actions
        print 80*'-'
        if tr is None:
            badwit()
        return tr

def aiger_witness_to_ivy_trace2(aiger,witnessfilename,action,stvarset,ext_act,annot,consts,decoder):
    with open(witnessfilename,'r') as f:
        res = f.readline().strip()
        if res != '1':
            badwit()
        aiger.sub.reset()
        lines = []
        for line in f:
            if line.endswith('\n'):
                line = line[:-1]
            lines.append(line)
        print '\nCounterexample follows:'
        print 80*'-'
        current = dict()
        count = 0
        handler = AigerMatchHandler2(aiger,decoder,consts,stvarset,current)
        for line in lines:
            cols = line.split(' ')
#            iu.dbg('cols')
            if len(cols) != 4:
                badwit()
            pre,inp,out,post = cols
            aiger.sub.step(inp)
            count += 1
            if count == len(lines):
                invar_fail = il.Symbol('invar__fail',il.find_sort('bool'))
                if il.is_true(aiger.get_sym(invar_fail)):
                    break
            # print 'inputs:'
            # for v in aiger.inputs:
            #     if v in decoder:
            #         print '    {} = {}'.format(decoder[v],aiger.get_sym(v))
            ia.match_annotation(action,annot,handler)
            handler.end()
        print str(handler)
        print 80*'-'
        if tr is None:
            badwit()
        return tr

class ModelChecker(object):
    pass

class ABCModelChecker(ModelChecker):
    def cmd(self,aigfilename,outfilename):
        return ['abc','-c','read_aiger {}; pdr; write_aiger_cex  {}'.format(aigfilename,outfilename)]
    def scrape(self,alltext):
        return 'Property proved' in alltext


def check_isolate():
    
    print
    print 80*'*'
    print

    global logfile,logfile_name
    if logfile is None:
        logfile_name = 'ivy_mc.log'
        logfile = open(logfile_name,'w')

    mod = im.module

    # build up a single action that does both initialization and all external actions

    ext_acts = [mod.actions[x] for x in sorted(mod.public_actions)]
    ext_act = ia.EnvAction(*ext_acts)
    
    # convert to aiger

    aiger,decoder,annot,cnsts,action,stvarset = to_aiger(mod,ext_act)
#    print aiger

    # output aiger to temp file

    with tempfile.NamedTemporaryFile(suffix='.aag',delete=False) as f:
        name = f.name
#        print 'file name: {}'.format(name)
        f.write(str(aiger))
    
    # convert aag to aig format

    aigfilename = name.replace('.aag','.aig')
    try:
        ret = subprocess.call(['aigtoaig',name,aigfilename])
    except:
        raise iu.IvyError(None,'failed to run aigtoaig')
    if ret != 0:
        raise iu.IvyError(None,'aigtoaig returned non-zero status')
        
    # run model checker

    outfilename = name.replace('.aag','.out')
    mc = ABCModelChecker() # TODO: make a command-line option
    cmd = mc.cmd(aigfilename,outfilename)
#    print cmd
    try:
        p = subprocess.Popen(cmd,stdout=subprocess.PIPE)
    except:
        raise iu.IvyError(None,'failed to run model checker')

    # pass through the stdout and collect it in texts

    print '\nModel checker output:'
    print 80*'-'
    texts = []
    while True:
        text = p.stdout.read(256)
        sys.stdout.write(text)
        texts.append(text)
        if len(text) < 256:
            break
    alltext = ''.join(texts)
    print 80*'-'
    
    # get the model checker status

    ret = p.wait()
    if ret != 0:
        raise iu.IvyError(None,'model checker returned non-zero status')

    # scrape the output to get the answer

    if mc.scrape(alltext):
        print '\nPASS'
    else:
        print '\nFAIL'
        print
        print 'Counterexample trace follows...'
        print 80*'*'
        tr = aiger_witness_to_ivy_trace2(aiger,outfilename,action,stvarset,ext_act,annot,cnsts,decoder)        
        print
        print 80*'*'
        exit(0)
        
    


    

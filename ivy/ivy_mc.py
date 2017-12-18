import ivy_module as im
import ivy_actions as ia
import ivy_logic as il
import ivy_transrel as tr
import ivy_logic_utils as ilu
import ivy_utils as iu
import ivy_art as art
import ivy_interp as itp

import tempfile
import subprocess


class Aiger(object):
    def __init__(self,inputs,latches,outputs):
        iu.dbg('inputs')
        iu.dbg('latches')
        iu.dbg('outputs')
        self.inputs = inputs
        self.latches = latches
        self.outputs = outputs
        self.gates = []
        self.map = dict()
        self.next_id = 1
        self.values = dict()
        for x in inputs + latches:
            self.map[x] = self.next_id * 2
            self.next_id += 1
        
    def true(self):
        return 1

    def false(self):
        return 0

    def lit(self,sym):
        return self.map[sym]

    def define(self,sym,val):
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

    def get_truth(digits,idx,syms):
        if (len(digits) != len(syms)):
            badwit()
        digit = digits[i]
        if digit == '0':
            return il.Or()
        elif digit == '1':
            return il.And()
        elif digit != 'x':
            badwit()
        return None

    def get_state(post):
        res = dict()
        for i,v in enumerate(self.latches):
            res[v] = self.get_truth(post,i,self.latches)
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
                                          
# functions for binary encoding of finite sorts

def ceillog2(n):
    bits,vals = 0,1
    while vals < n:
        bits += 1
        vals *= 2
    return bits


def encode_vars(syms,encoding):
    res = []
    for sym in syms:
        if il.is_enumerated(sym):
            n = ceillog2(sym.sort.defines())
        else:
            n = 1
        vs = [sym.suffix('__{}'.format(i)) for i in range(n)]
        encoding[sym] = vs
        res.extend(vs)
    return res

class Encoder(object):
    def __init__(self,inputs,latches,outputs):
        iu.dbg('inputs')
        iu.dbg('latches')
        iu.dbg('outputs')
        self.inputs = inputs
        self.latches = latches
        self.outputs = outputs
        self.encoding = dict()
        self.pos = dict()
        subinputs = encode_vars(inputs,self.encoding)
        sublatches = encode_vars(latches,self.encoding)
        suboutputs = encode_vars(outputs,self.encoding)
        self.sub = Aiger(subinputs,sublatches,suboutputs)
        
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
        return [self.sub.andl(*v) for v in zip(*args)]

    def orl(self,*args):
        return [self.sub.orl(*v) for v in zip(*args)]

    def notl(self,arg):
        return map(self.sub.notl,arg)
    

    def eval(self,expr,getdef=None):
        def recur(expr):
            if isinstance(expr,il.Ite):
                cond = self.eval(expr.args[0])
                thenterm = self.eval(expr.args[1],n,sort)
                elseterm = self.eval(expr.args[2],n,sort)
                return [self.sub.ite(cond,x,y) for x,y in zip(thenterm,elseterm)]
            if il.is_app(expr):
                sym = expr.rep 
                if sym in il.sig.constructors:
                    m = sort.defines().index(sym.name)
                    return self.binenc(m,ceillog2(len(sort.defines())))
                assert len(expr.args) == 0
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
                if is_eq(expr):
                    return self.encode_equality(*args)
                assert False,"unimplemented op in aiger output: {}".format(type(expr))
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
        for x,y in zip(self.encoding[sym],val):
            self.sub.set(x,y)

    def __str__(self):
        return str(self.sub)

    def gebin(bits,n):
        if n == 0:
            return self.true()
        if n >= 2**len(bits):
            return self.false()
        hval = 2**(len(bits)-1)
        if hval <= n:
            return self.andl(bits[0],self.gebin(bits[1:],n-hval))
        return self.orl(bits[0],self.gebin(bits[1:],n))

    def binenc(m,n):
        return [(self.true() if m & (1 << (n-1-i)) else self.false())
                for i in range(n)]
        
    def bindec(bits):
        res = 0
        n = len(bits)
        for i,v in enumerate(bits):
            if isinstance(v,il.And()):
                res += 1 << (n - 1 - i)

    def encode_equality(*terms):
        sort = terms[0].sort
        n = len(sort.defines())
        bits = ceillog2(n)
        eterms = [self.encode_term(t,bits,sort) for t in terms]
        eqs = self.andl(*[self.iff(x,y) for x,y in zip(*eterms)])
        alt = self.andl(*[self.gebin(e,n-1) for e in eterms])
        res =  self.orl(eqs,alt)
        return res

    def get_state(post):
        subres = self.sub.get_state(post)
        res = dict()
        for v in self.latches:
            bits = [subres[s] for s in self.encoding[v]]
            if il.is_enumerated(v):
                num = self.bindec(bits)
                vals = v.sort.defines()
                val = vals[num] if num < len(vals) else vals[-1]
            else:
                val = bits[0]
            res[v] = val
        return res


def to_aiger(mod,ext_act):

    # we use a special state variable __init to indicate the initial state

    ext_acts = [mod.actions[x] for x in sorted(mod.public_actions)]
    ext_act = ia.EnvAction(*ext_acts)
    init_var = il.Symbol('__init',il.find_sort('bool')) 
    init = ia.Sequence(*([a for n,a in mod.initializers]+[ia.AssignAction(init_var,il.And())]))
    action = ia.IfAction(init_var,ext_act,init)

    # get the invariant to be proved:

    invariant = il.And(*[lf.formula for lf in mod.labeled_conjs])

    # compute the transition relation

    stvars,trans,error = action.update(mod,None)
    
    # For each state var, create a variable that corresponds to the input of its latch

    def fix(v):
        return v.prefix('nondet')
    stvars_fix_map = dict((tr.new(v),fix(v)) for v in stvars)
    trans = ilu.rename_clauses(trans,stvars_fix_map)
    iu.dbg('trans')
    new_defs = trans.defs + [il.Definition(ilu.sym_inst(tr.new(v)),ilu.sym_inst(fix(v))) for v in stvars]
    trans = ilu.Clauses(trans.fmlas,new_defs)
    
    # Turn the transition constraint into a definition
    
    cnst_var = il.Symbol('__cnst',il.find_sort('bool'))
    new_defs = trans.defs + [il.Definition(tr.new(cnst_var),il.Not(il.And(*trans.fmlas)))]
    stvars.append(cnst_var)
    trans = ilu.Clauses([],new_defs)
    
    # Input are all the non-defined symbols. Output indicates invariant is false.

    iu.dbg('trans')
    def_set = set(df.defines() for df in trans.defs)
    def_set.update(stvars)
    iu.dbg('def_set')
    inputs = [sym for sym in ilu.used_symbols_clauses(trans) if sym not in def_set]
    fail = il.Symbol('__fail',il.find_sort('bool'))
    outputs = [fail]
    
    # make an aiger

    aiger = Encoder(inputs,stvars,outputs)
    comb_defs = [df for df in trans.defs if not tr.is_new(df.defines())]
    aiger.deflist(comb_defs)
    for df in trans.defs:
        if tr.is_new(df.defines()):
            aiger.set(tr.new_of(df.defines()),aiger.eval(df.args[1]))
    aiger.set(fail,aiger.eval(il.And(init_var,il.Not(cnst_var),il.Not(invariant))))

    return aiger

def badwit():
    raise iu.IvyError(None,'model checker returned mis-formated witness')

# This is an adaptor to create a trace as an ART. 

class IvyMCTrace(art.AnalysisGraph):
    def __init__(self,stvals):
        def abstractor(state):
            state.clauses = ilu.Clauses(stvals)
            state.universes = dict() # indicates this is a singleton state
        art.AnalysisGraph.__init__(self,initializer=abstractor)
    def add_state(self,stvals,action):
        self.add(itp.State(value=ilu.Clauses(stvals),expr=itp.action_app(action,self.states[-1]),label='ext'))

def aiger_witness_to_ivy_trace(aiger,witnessfilename,ext_act):
    with open(witnessfilename,'r') as f:
        res = f.readline().strip()
        iu.dbg('res')
        if res != '1':
            badwit()
        tr = None
        for line in f:
            if line.endswith('\n'):
                line = line[:-1]
            cols = line.split(' ')
            iu.dbg('cols')
            if len(cols) != 4:
                badwit()
            pre,inp,out,post = cols
            stvals = []
            stmap = aiger.get_state(post)                     
            for v in aiger.latches[:-2]: # last two are used for encoding
                val = stmap[v]
                if val is not None:
                    stvals.append(il.Equals(v,val))
            if not tr:
                tr = IvyMCTrace(stvals) # first transition is initialization
            else:
                tr.add_state(stvals,ext_act) # remainder are exported actions
        if tr is None:
            badwit()
        return tr

class ModelChecker(object):
    pass

class ABCModelChecker(ModelChecker):
    def cmd(self,aigfilename,outfilename):
        return ['abc','-c','read_aiger {}; dprove; write_aiger_cex  {}'.format(aigfilename,outfilename)]
    def scrape(self,alltext):
        return 'Property proved' in alltext


def check_isolate():
    
    mod = im.module

    # build up a single action that does both initialization and all external actions

    ext_acts = [mod.actions[x] for x in sorted(mod.public_actions)]
    ext_act = ia.EnvAction(*ext_acts)
    
    # convert to aiger

    aiger = to_aiger(mod,ext_act)
    print aiger

    # output aiger to temp file

    with tempfile.NamedTemporaryFile(suffix='.aag',delete=False) as f:
        name = f.name
        print 'file name: {}'.format(name)
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
    print cmd
    try:
        p = subprocess.Popen(cmd,stdout=subprocess.PIPE)
    except:
        raise iu.IvyError(None,'failed to run model checker')

    # pass through the stdout and collect it in texts

    texts = []
    while True:
        text = p.stdout.read(256)
        print text,
        texts.append(text)
        if len(text) < 256:
            break
    alltext = ''.join(texts)
    
    # get the model checker status

    ret = p.wait()
    if ret != 0:
        raise iu.IvyError(None,'model checker returned non-zero status')

    # scrape the output to get the answer

    if mc.scrape(alltext):
        print 'PASS'
    else:
        print 'FAIL'
        tr = aiger_witness_to_ivy_trace(aiger,outfilename,ext_act)        
        import tk_ui as ui
        iu.set_parameters({'mode':'induction'})
        gui = ui.new_ui()
        agui = gui.add(tr)
        gui.tk.update_idletasks() # so that dialog is on top of main window
        gui.tk.mainloop()
        exit(1)

        
    exit(0)


    

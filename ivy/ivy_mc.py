import ivy_module as im
import ivy_actions as ia
import ivy_logic as il
import ivy_transrel as tr
import ivy_logic_utils as ilu
import ivy_utils as iu

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
                                          
        

def to_aiger(mod):

    # build up a single action that does both initialization and all external actions
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

    aiger = Aiger(inputs,stvars,outputs)
    comb_defs = [df for df in trans.defs if not tr.is_new(df.defines())]
    aiger.deflist(comb_defs)
    for df in trans.defs:
        if tr.is_new(df.defines()):
            aiger.set(tr.new_of(df.defines()),aiger.eval(df.args[1]))
    aiger.set(fail,aiger.eval(il.And(init_var,il.Not(cnst_var),il.Not(invariant))))

    return aiger

def check_isolate():
    
    mod = im.module
    aiger = to_aiger(mod)
    print aiger

    with tempfile.NamedTemporaryFile(suffix='.aag',delete=False) as f:
        name = f.name
        print 'file name: {}'.format(name)
        f.write(str(aiger))
    
    aigfilename = name.replace('.aag','.aig')
    outfilename = name.replace('.aag','.out')
    try:
        ret = subprocess.call(['aigtoaig',name,aigfilename])
        if ret == 0:
            try:
                p = subprocess.Popen(['abc','-c','read_aiger {}; pdr; write_aiger_cex  {}'.format(aigfilename,outfilename)],stdout=subprocess.PIPE)
                texts = []
                while True:
                    text = p.stdout.read(256)
                    print text,
                    texts.append(text)
                    if len(text) < 256:
                        break
                ret = p.wait()
                if ret == 0:
                    print 'success'
                alltext = ''.join(texts)
                if 'Property proved' in alltext:
                    print 'verified!'
            finally:
                pass
    finally:
        pass
    #         except:
    #             raise IvyError(None,'failed to run abc')
    # except:
    #     raise IvyError(None,'failed to run aigtoaig')

        
    exit(0)


    

#! /usr/bin/env python
#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy
import ivy_logic as il
import ivy_module as im
import ivy_utils as iu
import ivy_actions as ia
import logic as lg
import logic_util as lu
import ivy_solver as slv
import ivy_transrel as tr
import ivy_logic_utils as ilu
import ivy_compiler as ic

def all_state_symbols():
    return [s for s in il.all_symbols() if s not in il.sig.constructors]

def sort_card(sort):
    if hasattr(sort,'card'):
        return sort.card
    if sort.is_relational():
        return 2
    return slv.sort_card(sort)
    if hasattr(sort,'name'):
        name = sort.name
        if name in il.sig.interp:
            sort = il.sig.interp[name]
            if isinstance(sort,il.EnumeratedSort):
                return sort.card
            card = slv.sort_card(sort)
            if card != None:
                return card
    raise iu.IvyError(None,'sort {} has no finite interpretation'.format(sort))
    
indent_level = 0

def indent(header):
    header.append(indent_level * '    ')

def declare_symbol(header,sym):
    if slv.solver_name(sym) == None:
        return # skip interpreted symbols
    name, sort = sym.name,sym.sort
    header.append('    bool ' if sort.is_relational() else '    int ')
    header.append(varname(sym.name))
    if hasattr(sort,'dom'):
        for d in sort.dom:
            header.append('[' + str(sort_card(d)) + ']')
    header.append(';\n')

special_names = {
    '<' : '__lt',
    '<=' : '__le',
    '>' : '__gt',
    '>=' : '__ge',
}

def varname(name):
    global special_names
    if name in special_names:
        return special_names[name]
    name = name.replace('loc:','loc__').replace('ext:','ext__').replace('___branch:','__branch__').replace('.','__')
    return name.split(':')[-1]

def mk_nondet(code,v,rng,name,unique_id):
    global nondet_cnt
    indent(code)
    code.append(varname(v) + ' = ___ivy_choose(' + str(rng) + ',"' + name + '",' + str(unique_id) + ');\n')

def emit_sorts(header):
    for name,sort in il.sig.sorts.iteritems():
        if name == "bool":
            continue
        if name in il.sig.interp:
            sort = il.sig.interp[name]
        if not isinstance(sort,il.EnumeratedSort):
            sortname = str(sort)
#            print "sortname: {}".format(sortname)
            if sortname.startswith('bv[') and sortname.endswith(']'):
                width = int(sortname[3:-1])
                indent(header)
                header.append('mk_bv("{}",{});\n'.format(name,width))
                continue
            raise iu.IvyError(None,'sort {} has no finite interpretation'.format(name))
        card = sort.card
        cname = varname(name)
        indent(header)
        header.append("const char *{}_values[{}]".format(cname,card) +
                      " = {" + ','.join('"{}"'.format(x) for x in sort.extension) + "};\n");
        indent(header)
        header.append('mk_enum("{}",{},{}_values);\n'.format(name,card,cname))

def emit_decl(header,symbol):
    name = symbol.name
    sname = slv.solver_name(symbol)
    if sname == None:  # this means the symbol is interpreted in some theory
        return 
    cname = varname(name)
    sort = symbol.sort
    rng_name = "Bool" if sort.is_relational() else sort.rng.name
    domain = sort_domain(sort)
    if len(domain) == 0:
        indent(header)
        header.append('mk_const("{}","{}");\n'.format(sname,rng_name))
    else:
        card = len(domain)
        indent(header)
        header.append("const char *{}_domain[{}]".format(cname,card) + " = {"
                      + ','.join('"{}"'.format(s.name) for s in domain) + "};\n");
        indent(header)
        header.append('mk_decl("{}",{},{}_domain,"{}");\n'.format(sname,card,cname,rng_name))
        
def emit_sig(header):
    emit_sorts(header)
    for symbol in all_state_symbols():
        emit_decl(header,symbol)

def sort_domain(sort):
    if hasattr(sort,"domain"):
        return sort.domain
    return []

def emit_eval(header,symbol,obj=None): 
    global indent_level
    name = symbol.name
    sname = slv.solver_name(symbol)
    cname = varname(name)
    sort = symbol.sort
    domain = sort_domain(sort)
    for idx,dsort in enumerate(domain):
        dcard = sort_card(dsort)
        indent(header)
        header.append("for (int X{} = 0; X{} < {}; X{}++)\n".format(idx,idx,dcard,idx))
        indent_level += 1
    indent(header)
    header.append((obj + '.' if obj else '')
                  + cname + ''.join("[X{}]".format(idx) for idx in range(len(domain)))
                  + ' = eval_apply("{}"'.format(sname)
                  + ''.join(",X{}".format(idx) for idx in range(len(domain)))
                  + ");\n")
    for idx,dsort in enumerate(domain):
        indent_level -= 1    

def emit_set(header,symbol): 
    global indent_level
    name = symbol.name
    sname = slv.solver_name(symbol)
    cname = varname(name)
    sort = symbol.sort
    domain = sort_domain(sort)
    for idx,dsort in enumerate(domain):
        dcard = sort_card(dsort)
        indent(header)
        header.append("for (int X{} = 0; X{} < {}; X{}++)\n".format(idx,idx,dcard,idx))
        indent_level += 1
    indent(header)
    header.append('set("{}"'.format(sname)
                  + ''.join(",X{}".format(idx) for idx in range(len(domain)))
                  + ",obj.{}".format(cname)+ ''.join("[X{}]".format(idx) for idx in range(len(domain)))
                  + ");\n")
    for idx,dsort in enumerate(domain):
        indent_level -= 1    

def emit_eval_sig(header,obj=None):
    for symbol in all_state_symbols():
        if slv.solver_name(symbol) != None: # skip interpreted symbols
            emit_eval(header,symbol,obj)

def emit_init_gen(header,impl,classname):
    global indent_level
    header.append("""
class init_gen : public gen {
public:
    init_gen();
""")
    impl.append("init_gen::init_gen(){\n");
    indent_level += 1
    emit_sig(impl)
    indent(impl)
    impl.append('add("(assert (and\\\n')
    constraints = [im.module.init_cond.to_formula()]
    for a in im.module.axioms:
        constraints.append(a.to_formula())
    for c in constraints:
        fmla = slv.formula_to_z3(c).sexpr().replace('\n',' ')
        indent(impl)
        impl.append("  {}\\\n".format(fmla))
    indent(impl)
    impl.append('))");\n')
    indent_level -= 1
    impl.append("}\n");
    header.append("    bool generate(" + classname + "&);\n};\n")
    impl.append("bool init_gen::generate(" + classname + "& obj) {\n")
    impl.append("""
    bool res = solve();
    if (res) {
""")
    indent_level += 2
    emit_eval_sig(impl,'obj')
    indent_level -= 2
    impl.append("""
    }
    return res;
}
""")
    
def emit_randomize(header,symbol):
    indent(header)
    header.append('randomize("{}");\n'.format(slv.solver_name(symbol)))

def emit_action_gen(header,impl,name,action):
    global indent_level
    caname = varname(name)
    upd = action.update(im.module,None)
    pre = tr.reverse_image(ilu.true_clauses(),ilu.true_clauses(),upd)
    pre_clauses = ilu.trim_clauses(pre)
    pre = pre_clauses.to_formula()
    syms = [x for x in ilu.used_symbols_ast(pre) if x.name not in il.sig.symbols]
    header.append("class " + caname + "_gen : public gen {\n  public:\n")
    for sym in syms:
        if not sym.name.startswith('__ts') and sym not in pre_clauses.defidx:
            declare_symbol(header,sym)
    header.append("    {}_gen();\n".format(caname))
    impl.append(caname + "_gen::" + caname + "_gen(){\n");
    indent_level += 1
    emit_sig(impl)
    for sym in syms:
        emit_decl(impl,sym)
    
    indent(impl)
    impl.append('add("(assert {})");\n'.format(slv.formula_to_z3(pre).sexpr().replace('\n','\\\n')))
    indent_level -= 1
    impl.append("}\n");
    header.append("    bool generate(" + classname + "&);\n};\n");
    impl.append("bool " + caname + "_gen::generate(" + classname + "& obj) {\n    push();\n")
    indent_level += 1
    pre_used = ilu.used_symbols_ast(pre)
    for sym in all_state_symbols():
        if sym in pre_used and sym not in pre_clauses.defidx: # skip symbols not used in constraint
            if slv.solver_name(sym) != None: # skip interpreted symbols
                emit_set(impl,sym)
    for sym in syms:
        if not sym.name.startswith('__ts') and sym not in pre_clauses.defidx:
            emit_randomize(impl,sym)
    impl.append("""
    bool res = solve();
    if (res) {
""")
    indent_level += 1
    for sym in syms:
        if not sym.name.startswith('__ts') and sym not in pre_clauses.defidx:
            emit_eval(impl,sym)
    indent_level -= 2
    impl.append("""
    }
    pop();
    obj.___ivy_gen = this;
    return res;
}
""")


def emit_method_decl(header,name,action,body=False,classname=None):
    if not hasattr(action,"formal_returns"):
        print "bad name: {}".format(name)
        print "bad action: {}".format(action)
    rs = action.formal_returns
    if not body:
        header.append('    ')
    if len(rs) == 0:
        header.append('void ')
    elif len(rs) == 1:
        header.append('int ')
    else:
        raise iu.IvyError(action,'cannot handle multiple output values')
    if body:
        header.append(classname + '::')
    header.append(varname(name) + '(')
    first = True
    for p in action.formal_params:
        header.append(('' if first else ', ') + 'int ' + varname(p.name))
        first = False
    header.append(')')
    
def emit_action(header,impl,name,classname):
    global indent_level
    action = im.module.actions[name]
    emit_method_decl(header,name,action)
    header.append(';\n')
    emit_method_decl(impl,name,action,body=True,classname=classname)
    impl.append('{\n')
    indent_level += 1
    if len(action.formal_returns) == 1:
        indent(impl)
        impl.append('int ' + varname(action.formal_returns[0].name) + ';\n')
    action.emit(impl)
    if len(action.formal_returns) == 1:
        indent(impl)
        impl.append('return ' + varname(action.formal_returns[0].name) + ';\n')
    indent_level -= 1
    impl.append('}\n')

def init_method():
    asserts = [ia.AssertAction(im.module.init_cond.to_formula())]
    for a in im.module.axioms:
        asserts.append(ia.AssertAction(a.to_formula()))
    res = ia.Sequence(*asserts)
    res.formal_params = []
    res.formal_returns = []
    return res

def module_to_cpp_class(classname):
    header = []
    header.append('extern void ivy_assert(bool);\n')
    header.append('extern void ivy_assume(bool);\n')
    header.append('extern int choose(int,int);\n')
    header.append('struct ivy_gen {virtual int choose(int rng,const char *name) = 0;};\n')
    header.append('#include <vector>\n')
    header.append('class ' + classname + ' {\n  public:\n')
    header.append('    std::vector<int> ___ivy_stack;\n')
    header.append('    ivy_gen *___ivy_gen;\n')
    header.append('    int ___ivy_choose(int rng,const char *name,int id);\n')
    
    impl = ['#include "' + classname + '.h"\n\n']
    impl.append("#include <sstream>\n")
    impl.append("int " + classname)
    impl.append(
"""::___ivy_choose(int rng,const char *name,int id) {
        std::ostringstream ss;
        ss << name << ':' << id;;
        for (unsigned i = 0; i < ___ivy_stack.size(); i++)
            ss << ':' << ___ivy_stack[i];
        return ___ivy_gen->choose(rng,ss.str().c_str());
    }
""")
    for sym in all_state_symbols():
        declare_symbol(header,sym)
    for sym in il.sig.constructors:
        declare_symbol(header,sym)
    for sname in il.sig.interp:
        header.append('    int __CARD__' + varname(sname) + ';\n')

    header.append('    ' + classname + '();\n');
    im.module.actions['.init'] = init_method()
    for a in im.module.actions:
        emit_action(header,impl,a,classname)
    header.append('};\n')

    impl.append(classname + '::' + classname + '(){\n')
    enums = set(sym.sort.name for sym in il.sig.constructors)  
    for sortname in enums:
        for i,n in enumerate(il.sig.sorts[sortname].extension):
            impl.append('    {} = {};\n'.format(varname(n),i))
    for sortname in il.sig.interp:
        impl.append('    __CARD__{} = {};\n'.format(varname(sortname),sort_card(il.sig.sorts[sortname])))
    impl.append('}\n')

    
    emit_boilerplate1(header,impl)
    emit_init_gen(header,impl,classname)
    for name,action in im.module.actions.iteritems():
        if name in im.module.public_actions:
            emit_action_gen(header,impl,name,action)
    return ''.join(header) , ''.join(impl)

def emit_constant(self,header,code):
    code.append(varname(self.name))

il.Symbol.emit = emit_constant
il.Variable.emit = emit_constant

def emit_app(self,header,code):
    # handle interpreted ops
    if slv.solver_name(self.func) == None:
        assert len(self.args) == 2 # handle only binary ops for now
        code.append('(')
        self.args[0].emit(header,code)
        code.append(' {} '.format(self.func.name))
        self.args[1].emit(header,code)
        code.append(')')
        return 
    # handle uninterpreted ops
    code.append(varname(self.func.name))
    for a in self.args:
        code.append('[')
        a.emit(header,code)
        code.append(']')

lg.Apply.emit = emit_app

temp_ctr = 0

def new_temp(header):
    global temp_ctr
    name = '__tmp' + str(temp_ctr)
    temp_ctr += 1
    indent(header)
    header.append('int ' + name + ';\n')
    return name

def emit_quant(variables,body,header,code,exists=False):
    global indent_level
    if len(variables) == 0:
        body.emit(header,code)
        return
    v0 = variables[0]
    variables = variables[1:]
    res = new_temp(header)
    idx = v0.name
    indent(header)
    header.append(res + ' = ' + str(0 if exists else 1) + ';\n')
    indent(header)
    header.append('for (int ' + idx + ' = 0; ' + idx + ' < ' + str(sort_card(v0.sort)) + '; ' + idx + '++) {\n')
    indent_level += 1
    subcode = []
    emit_quant(variables,body,header,subcode,exists)
    indent(header)
    header.append('if (' + ('!' if not exists else ''))
    header.extend(subcode)
    header.append(') '+ res + ' = ' + str(1 if exists else 0) + ';\n')
    indent_level -= 1
    indent(header)
    header.append('}\n')
    code.append(res)    

lg.ForAll.emit = lambda self,header,code: emit_quant(list(self.variables),self.body,header,code,False)
lg.Exists.emit = lambda self,header,code: emit_quant(list(self.variables),self.body,header,code,True)

def emit_unop(self,header,code,op):
    code.append(op)
    self.args[0].emit(header,code)

lg.Not.emit = lambda self,header,code: emit_unop(self,header,code,'!')

def emit_binop(self,header,code,op,ident=None):
    if len(self.args) == 0:
        assert ident != None
        code.append(ident)
        return
    code.append('(')
    self.args[0].emit(header,code)
    for a in self.args[1:]:
        code.append(' ' + op + ' ')
        a.emit(header,code)
    code.append(')')
    
def emit_implies(self,header,code):
    code.append('(')
    code.append('!')
    self.args[0].emit(header,code)
    code.append(' || ')
    self.args[1].emit(header,code)
    code.append(')')
    

lg.Eq.emit = lambda self,header,code: emit_binop(self,header,code,'==')
lg.Iff.emit = lambda self,header,code: emit_binop(self,header,code,'==')
lg.Implies.emit = emit_implies
lg.And.emit = lambda self,header,code: emit_binop(self,header,code,'&&','true')
lg.Or.emit = lambda self,header,code: emit_binop(self,header,code,'||','false')

def emit_assign_simple(self,header):
    code = []
    indent(code)
    self.args[0].emit(header,code)
    code.append(' = ')
    self.args[1].emit(header,code)
    code.append(';\n')    
    header.extend(code)

def emit_assign(self,header):
    global indent_level
    vs = list(lu.free_variables(self.args[0]))
    if len(vs) == 0:
        emit_assign_simple(self,header)
        return
    global temp_ctr
    tmp = '__tmp' + str(temp_ctr)
    temp_ctr += 1
    indent(header)
    header.append('int ' + tmp)
    for v in vs:
        header.append('[' + str(sort_card(v.sort)) + ']')
    header.append(';\n')
    for idx in vs:
        indent(header)
        header.append('for (int ' + str(idx) + ' = 0; ' + str(idx) + ' < ' + str(sort_card(idx.sort)) + '; ' + str(idx) + '++) {\n')
        indent_level += 1
    code = []
    indent(code)
    code.append(tmp + ''.join('['+varname(v.name)+']' for v in vs) + ' = ')
    self.args[1].emit(header,code)
    code.append(';\n')    
    header.extend(code)
    for idx in vs:
        indent_level -= 1
        indent(header)
        header.append('}\n')
    for idx in vs:
        indent(header)
        header.append('for (int ' + str(idx) + ' = 0; ' + str(idx) + ' < ' + str(sort_card(idx.sort)) + '; ' + str(idx) + '++) {\n')
        indent_level += 1
    code = []
    indent(code)
    self.args[0].emit(header,code)
    code.append(' = ' + tmp + ''.join('['+varname(v.name)+']' for v in vs) + ';\n')
    header.extend(code)
    for idx in vs:
        indent_level -= 1
        indent(header)
        header.append('}\n')
    
ia.AssignAction.emit = emit_assign

def emit_havoc(self,header):
    print self
    print self.lineno
    assert False

ia.HavocAction.emit = emit_havoc

def emit_sequence(self,header):
    global indent_level
    indent(header)
    header.append('{\n')
    indent_level += 1
    for a in self.args:
        a.emit(header)
    indent_level -= 1 
    indent(header)
    header.append('}\n')

ia.Sequence.emit = emit_sequence

def emit_assert(self,header):
    code = []
    indent(code)
    code.append('ivy_assert(')
    il.close_formula(self.args[0]).emit(header,code)
    code.append(');\n')    
    header.extend(code)

ia.AssertAction.emit = emit_assert

def emit_assume(self,header):
    code = []
    indent(code)
    code.append('ivy_assume(')
    il.close_formula(self.args[0]).emit(header,code)
    code.append(');\n')    
    header.extend(code)

ia.AssumeAction.emit = emit_assume


def emit_call(self,header):
    indent(header)
    header.append('___ivy_stack.push_back(' + str(self.unique_id) + ');\n')
    code = []
    indent(code)
    if len(self.args) == 2:
        self.args[1].emit(header,code)
        code.append(' = ')
    code.append(varname(str(self.args[0].rep)) + '(')
    first = True
    for p in self.args[0].args:
        if not first:
            code.append(', ')
        p.emit(header,code)
        first = False
    code.append(');\n')    
    header.extend(code)
    indent(header)
    header.append('___ivy_stack.pop_back();\n')

ia.CallAction.emit = emit_call

def emit_local(self,header):
    global indent_level
    indent(header)
    header.append('{\n')
    indent_level += 1
    for p in self.args[0:-1]:
        indent(header)
        header.append('int ' + varname(p.name) + ';\n')
        mk_nondet(header,p.name,sort_card(p.sort),p.name,self.unique_id)
    self.args[-1].emit(header)
    indent_level -= 1
    indent(header)
    header.append('}\n')

ia.LocalAction.emit = emit_local

def emit_if(self,header):
    global indent_level
    code = []
    indent(code)
    code.append('if(');
    self.args[0].emit(header,code)
    header.extend(code)
    header.append('){\n')
    indent_level += 1
    self.args[1].emit(header)
    indent_level -= 1
    indent(header)
    header.append('}\n')
    if len(self.args) == 3:
        indent(header)
        header.append('else {\n')
        indent_level += 1
        self.args[2].emit(header)
        indent_level -= 1
        indent(header)
        header.append('}\n')

ia.IfAction.emit = emit_if

def emit_choice(self,header):
    global indent_level
    if len(self.args) == 1:
        self.args[0].emit(header)
        return
    tmp = new_temp(header)
    mk_nondet(header,tmp,len(self.args),"___branch",self.unique_id)
    for idx,arg in enumerate(self.args):
        indent(header)
        if idx != 0:
            header.append('else ')
        if idx != len(self.args)-1:
            header.append('if(' + tmp + ' == ' + str(idx) + ')');
        header.append('{\n')
        indent_level += 1
        arg.emit(header)
        indent_level -= 1
        indent(header)
        header.append('}\n')

ia.ChoiceAction.emit = emit_choice

def emit_boilerplate1(header,impl):
    header.append("""
#include <string>
#include <vector>
#include <sstream>
#include <cstdlib>
#include "z3++.h"
#include "hash.h"

using namespace hash_space;

class gen : public ivy_gen {

protected:
    z3::context ctx;
    z3::solver slvr;
    z3::model model;

    gen(): slvr(ctx), model(ctx,(Z3_model)0) {}

    hash_map<std::string, z3::sort> enum_sorts;
    hash_map<Z3_sort, z3::func_decl_vector> enum_values;
    hash_map<std::string, z3::func_decl> decls_by_name;
    hash_map<Z3_symbol,int> enum_to_int;
    std::vector<Z3_symbol> sort_names;
    std::vector<Z3_sort> sorts;
    std::vector<Z3_symbol> decl_names;
    std::vector<Z3_func_decl> decls;
    std::vector<z3::expr> alits;


public:
    int eval_apply(const char *decl_name, unsigned num_args, const int *args) {
        z3::func_decl decl = decls_by_name.find(decl_name)->second;
        std::vector<z3::expr> expr_args;
        unsigned arity = decl.arity();
        assert(arity == num_args);
        for(unsigned i = 0; i < arity; i ++) {
            z3::sort sort = decl.domain(i);
            expr_args.push_back(int_to_z3(sort,args[i]));
        }
        z3::expr apply_expr = decl(arity,&expr_args[0]);
        //        std::cout << "apply_expr: " << apply_expr << std::endl;
        try {
            z3::expr foo = model.eval(apply_expr,true);
            if (foo.is_bv()) {
                assert(foo.is_numeral());
                int v;
                if (Z3_get_numeral_int(ctx,foo,&v) != Z3_TRUE)
                    assert(false && "bit vector value too large for machine int");
                return v;
            }
            assert(foo.is_app());
            if (foo.is_bool())
                return (foo.decl().decl_kind() == Z3_OP_TRUE) ? 1 : 0;
            return enum_to_int[foo.decl().name()];
        }
        catch (const z3::exception &e) {
            std::cout << e << std::endl;
            throw e;
        }
    }

    int eval_apply(const char *decl_name) {
        return eval_apply(decl_name,0,(int *)0);
    }

    int eval_apply(const char *decl_name, int arg0) {
        return eval_apply(decl_name,1,&arg0);
    }
    
    int eval_apply(const char *decl_name, int arg0, int arg1) {
        int args[2] = {arg0,arg1};
        return eval_apply(decl_name,2,args);
    }

    int eval_apply(const char *decl_name, int arg0, int arg1, int arg2) {
        int args[3] = {arg0,arg1,arg2};
        return eval_apply(decl_name,3,args);
    }

    z3::expr int_to_z3(const z3::sort &range, int value) {
        if (range.is_bool())
            return ctx.bool_val(value);
        if (range.is_bv())
            return ctx.bv_val(value,range.bv_size());
        return enum_values.find(range)->second[value]();
    }

    unsigned sort_card(const z3::sort &range) {
        if (range.is_bool())
            return 2;
        if (range.is_bv())
            return 1 << range.bv_size();
        return enum_values.find(range)->second.size();
    }

    int set(const char *decl_name, unsigned num_args, const int *args, int value) {
        z3::func_decl decl = decls_by_name.find(decl_name)->second;
        std::vector<z3::expr> expr_args;
        unsigned arity = decl.arity();
        assert(arity == num_args);
        for(unsigned i = 0; i < arity; i ++) {
            z3::sort sort = decl.domain(i);
            expr_args.push_back(int_to_z3(sort,args[i]));
        }
        z3::expr apply_expr = decl(arity,&expr_args[0]);
        z3::sort range = decl.range();
        z3::expr val_expr = int_to_z3(range,value);
        z3::expr pred = apply_expr == val_expr;
        //        std::cout << "pred: " << pred << std::endl;
        slvr.add(pred);
    }

    int set(const char *decl_name, int value) {
        return set(decl_name,0,(int *)0,value);
    }

    int set(const char *decl_name, int arg0, int value) {
        return set(decl_name,1,&arg0,value);
    }
    
    int set(const char *decl_name, int arg0, int arg1, int value) {
        int args[2] = {arg0,arg1};
        return set(decl_name,2,args,value);
    }

    int set(const char *decl_name, int arg0, int arg1, int arg2, int value) {
        int args[3] = {arg0,arg1,arg2};
        return set(decl_name,3,args,value);
    }

    void randomize(const char *decl_name) {
        z3::func_decl decl = decls_by_name.find(decl_name)->second;
        unsigned arity = decl.arity();
        assert(arity == 0);
        z3::expr apply_expr = decl();
        z3::sort range = decl.range();
        unsigned card = sort_card(range);
        int value = rand() % card;
        z3::expr val_expr = int_to_z3(range,value);
        z3::expr pred = apply_expr == val_expr;
        // std::cout << "pred: " << pred << std::endl;
        std::ostringstream ss;
        ss << "alit:" << alits.size();
        z3::expr alit = ctx.bool_const(ss.str().c_str());
        alits.push_back(alit);
        slvr.add(!alit || pred);
    }

    void push(){
        slvr.push();
    }

    void pop(){
        slvr.pop();
    }

    void mk_enum(const char *sort_name, unsigned num_values, char const * const * value_names) {
        z3::func_decl_vector cs(ctx), ts(ctx);
        z3::sort sort = ctx.enumeration_sort(sort_name, num_values, value_names, cs, ts);
        // can't use operator[] here because the value classes don't have nullary constructors
        enum_sorts.insert(std::pair<std::string, z3::sort>(sort_name,sort));
        enum_values.insert(std::pair<Z3_sort, z3::func_decl_vector>(sort,cs));
        sort_names.push_back(Z3_mk_string_symbol(ctx,sort_name));
        sorts.push_back(sort);
        for(unsigned i = 0; i < num_values; i++){
            Z3_symbol sym = Z3_mk_string_symbol(ctx,value_names[i]);
            decl_names.push_back(sym);
            decls.push_back(cs[i]);
            enum_to_int[sym] = i;
        }
    }

    void mk_bv(const char *sort_name, unsigned width) {
        z3::sort sort = ctx.bv_sort(width);
        // can't use operator[] here because the value classes don't have nullary constructors
        enum_sorts.insert(std::pair<std::string, z3::sort>(sort_name,sort));
    }

    void mk_decl(const char *decl_name, unsigned arity, const char **domain_names, const char *range_name) {
        std::vector<z3::sort> domain;
        for (unsigned i = 0; i < arity; i++)
            domain.push_back(enum_sorts.find(domain_names[i])->second);
        std::string bool_name("Bool");
        z3::sort range = (range_name == bool_name) ? ctx.bool_sort() : enum_sorts.find(range_name)->second;   
        z3::func_decl decl = ctx.function(decl_name,arity,&domain[0],range);
        decl_names.push_back(Z3_mk_string_symbol(ctx,decl_name));
        decls.push_back(decl);
        decls_by_name.insert(std::pair<std::string, z3::func_decl>(decl_name,decl));
    }

    void mk_const(const char *const_name, const char *sort_name) {
        mk_decl(const_name,0,0,sort_name);
    }

    void add(const std::string &z3inp) {
        z3::expr fmla(ctx,Z3_parse_smtlib2_string(ctx, z3inp.c_str(), sort_names.size(), &sort_names[0], &sorts[0], decl_names.size(), &decl_names[0], &decls[0]));
        ctx.check_error();

        slvr.add(fmla);
    }

    bool solve() {
        // std::cout << alits.size();
        while(true){
            z3::check_result res = slvr.check(alits.size(),&alits[0]);
            if (res != z3::unsat)
                break;
            z3::expr_vector core = slvr.unsat_core();
            if (core.size() == 0)
                return false;
            unsigned idx = rand() % core.size();
            z3::expr to_delete = core[idx];
            for (unsigned i = 0; i < alits.size(); i++)
                if (z3::eq(alits[i],to_delete)) {
                    alits[i] = alits.back();
                    alits.pop_back();
                    break;
                }
        }
        model = slvr.get_model();
        alits.clear();
        //        std::cout << model;
        return true;
    }

    int choose(int rng, const char *name){
        if (decls_by_name.find(name) == decls_by_name.end())
            return 0;
        return eval_apply(name);
    }
};
""")


if __name__ == "__main__":
    ia.set_determinize(True)
    slv.set_use_native_enums(True)
    ic.set_create_big_action(False)
    with im.Module():
        ivy.ivy_init()

        classname = im.module.name
        header,impl = module_to_cpp_class(classname)
#        print header
#        print impl
        f = open(classname+'.h','w')
        f.write(header)
        f.close()
        f = open(classname+'.cpp','w')
        f.write(impl)
        f.close()
        

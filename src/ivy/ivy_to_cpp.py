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

def sort_card(sort):
    if hasattr(sort,'name'):
        name = sort.name
        if name in il.sig.interp:
            sort = il.sig.interp[name]
    if not hasattr(sort,'card'):
        raise iu.IvyError(None,'sort {} has no finite interpretation'.format(sort))
    return sort.card
    
indent_level = 0

def indent(header):
    header.append(indent_level * '    ')

def declare_symbol(header,sym):
    name, sort = sym.name,sym.sort
    header.append('    bool ' if sort.is_relational() else '    int ')
    header.append(sym.name)
    if hasattr(sort,'dom'):
        for d in sort.dom:
            header.append('[' + str(sort_card(d)) + ']')
    header.append(';\n')

def varname(name):
    name = name.replace('loc:','loc__')
    return name.split(':')[-1]

def emit_method_decl(header,name,action,body=False,classname=None):
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
    header.append(name + '(')
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

def module_to_cpp_class(classname):
    header = []
    header.append('extern void assert(bool);\n')
    header.append('extern void assume(bool);\n')
    header.append('class ' + classname + ' {\n  public:\n')
    impl = ['#include "' + classname + '.h"\n\n']
    for sym in il.all_symbols():
        declare_symbol(header,sym)
    for a in im.module.actions:
        emit_action(header,impl,a,classname)
    header.append('};\n')
    return ''.join(header) , ''.join(impl)

def emit_constant(self,header,code):
    code.append(varname(self.name))

il.Symbol.emit = emit_constant
il.Variable.emit = emit_constant

def emit_app(self,header,code):
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

def emit_binop(self,header,code,op):
    code.append('(')
    self.args[0].emit(header,code)
    code.append(' ' + op + ' ')
    self.args[1].emit(header,code)
    code.append(')')
    
lg.Eq.emit = lambda self,header,code: emit_binop(self,header,code,'==')
lg.And.emit = lambda self,header,code: emit_binop(self,header,code,'&&')
lg.Or.emit = lambda self,header,code: emit_binop(self,header,code,'||')

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
    code.append('assert(')
    il.close_formula(self.args[0]).emit(header,code)
    code.append(');\n')    
    header.extend(code)

ia.AssertAction.emit = emit_assert

def emit_assume(self,header):
    code = []
    indent(code)
    code.append('assume(')
    il.close_formula(self.args[0]).emit(header,code)
    code.append(');\n')    
    header.extend(code)

ia.AssumeAction.emit = emit_assume


def emit_call(self,header):
    code = []
    indent(code)
    if len(self.args) == 2:
        self.args[1].emit(header,code)
        code.append(' = ')
    code.append(str(self.args[0].rep) + '(')
    first = True
    for p in self.args[0].args:
        if not first:
            code.append(', ')
        p.emit(header,code)
        first = False
    code.append(');\n')    
    header.extend(code)

ia.CallAction.emit = emit_call

def emit_local(self,header):
    global indent_level
    indent(header)
    header.append('{\n')
    indent_level += 1
    for p in self.args[0:-1]:
        indent(header)
        header.append('int ' + varname(p.name) + ';\n')
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


if __name__ == "__main__":
    with im.Module():
        ivy.ivy_init()

        classname = 'ivy_test'
        header,impl = module_to_cpp_class(classname)
        print header
        print impl
        f = open(classname+'.h','w')
        f.write(header)
        f.close()
        f = open(classname+'.cpp','w')
        f.write(impl)
        f.close()
        

# coding: utf-8
import ivy_init
import ivy_logic as il
import ivy_module as im
import ivy_utils as iu
import ivy_actions as ia
import logic as lg
import logic_util as lu
import ivy_logic_utils as ilu
import ivy_compiler as ic
import ivy_isolate as iso
import ivy_ast
import itertools
import ivy_theory as ith

things = []

preamble = """
import .ivy_pl
namespace ivy
open ivy_logic

"""

postamble = """

end ivy
"""

def emit(str):
    things.append(str)

def emit_eol():
    emit("\n")

def sort_to_string(sort):
    if isinstance(sort,lg.UninterpretedSort):
        return '(sort.ui "' + sort.name + '")'
    elif isinstance(sort,lg.BooleanSort):
        return "sort.bool"
    elif isinstance(sort,lg.FunctionSort):
        return ('(' + ' × '.join(sort_to_string(s) for s in sort.domain) + ' ↦ ' +
                   sort_to_string(sort.range) + ')')
    else:
        raise iu.IvyError(None,"enumerated sorts not supported yet")

def emit_symbol_def(sym):
    emit('def ' + sym.name + ' := mk_cnst "' + sym.name + '" ' + sort_to_string(sym.sort))
    emit_eol()
    
def emit_expr(f):
    if isinstance(f,lg.Var):
        emit('("'+f.name+'",'+sort_to_string(f.sort)+')')
    elif isinstance(f,lg.Const):
        emit(f.name)
    elif isinstance(f,lg.Apply):
        emit(f.name + '(')
        first = True
        for x in f.terms:
            if not first:
                emit(',')
            emit_expr(x)
            first = False
        emit(')')
    elif isinstance(f,lg.Eq) or isinstance(f,lg.Iff):
        emit('(fmla.eq ')
        emit_expr(f.terms[0])
        emit(' ')
        emit_expr(f.terms[1])
        emit(')')
    elif isinstance(f,lg.Ite):
        emit('(ite_fmla ')
        for idx in range(3):
            emit(' ')
            emit_expr(f.terms[idx])
        emit(')')
    elif isinstance(f,lg.Not):
        emit('¬')
        emit_expr(f.body)
    elif isinstance(f,lg.And) or isinstance(f,lg.Or):
        if len(f.terms) == 0:
            emit('ltrue' if isinstance(f,lg.And) else 'lfalse')
        else:
            emit ('(')
            first = True
            for x in f.terms:
                if not first:
                    emit('∧' if isinstance(f,lg.And) else '∨')
                emit_expr(x)
                first = False
            emit (')')
    elif isinstance(f,lg.Implies):
        emit('(')
        emit_expr(f.terms[0])
        emit(' ⇒ ')
        emit_expr(f.terms[1])
        emit(')')
    elif isinstance(f,lg.Forall):
        emit('¬')
        for v in f.variables:
            emit('(fmla.proj ')
            emit_expr(v)
            emit(' ')
        emit('¬')
        emit_expr(f.body)
        for v in f.variables:
            emit(')')
    elif isinstance(f,lg.Exists):
        for v in f.variables:
            emit('(fmla.proj ')
            emit_expr(v)
            emit(' ')
        emit_expr(f.body)
        for v in f.variables:
            emit(')')
    elif isinstance(f,lg.Lambda):
        for v in f.variables:
            emit('(fmla.lambda ')
            emit_expr(v)
            emit(' ')
        emit_expr(f.body)
        for v in f.variables:
            emit(')')
    
def emit_action(a):
    if isinstance(a,ia.AssignAction):
        vars = [(x if isinstance(x,lg.Variable) else lg.Variable('$V'+ str(idx)))
                for x,idx in enumerate(a.args[0].args)]
        emit('    ' + a.args[0].rep.name + ' ::= ')
        rhs = a.args[1]
        if len(vars) != 0:
            cond = lg.And(*[lg.Eq(v,w) for v,w in zip(vars,a.args[0].args) if v != w])
            rhs = lg.Ite(cond,rhs,lg.Apply(a.func,vars))
        emit_expr(rhs)
    elif isinstance(a,ia.Sequence):
        emit('(')
        first = True
        for x in a.args:
            if not first:
                emit(';\n')
                emit_action(x)
            first = False
        emit (')')
    elif isinstance(a,ia.IfAction):
        emit('(PL.pterm.ite ')
        emit_expr(a.args[0])
        emit_action(a.args[1])
        if len(a.args) > 2:
            emit_action(a.args[1])
        else:
            emit('PL.pterm.skip')
    else:
        raise iu.IvyError(a,'action not supported yet')
        
            
def main():
    with im.Module():
        ivy_init.ivy_init(create_isolate=False)
        emit(preamble)
        for sym in il.all_symbols():
            emit_symbol_def(sym)
        emit('def P := (PL.prog.letrec')
        emit_eol()
        for name,act in im.module.actions.iteritems():
            emit('  (@bndng.cons PL.pterm ("'+name+'",\n')
            emit_action(act)
            emit_eol()
            emit('    ) ')
            emit_eol()
        emit('  (bndng.default PL.pterm.skip)')
        for name,act in im.module.actions.iteritems():
            emit(')')
        emit_eol()
        exports = sorted(list(im.module.public_actions))
        if len(exports) == 0:
            emit('PL.pterm.skip')
        else:
            emit('(('+ ' + '.join('(PL.pterm.call "'+x+'")' for x in exports) + ')**))')
        emit(postamble)
        basename = im.module.name
        f = open(basename+'.lean','w')
        f.write("".join(things))
        f.close()

        

if __name__ == "__main__":
    main()
        
        

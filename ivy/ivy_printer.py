import ivy_logic
import ivy_utils as iu
import ivy_actions as ia

def labeled_fmlas_to_str(kwd,lfmlas):
    res = ''
    for f in lfmlas:
        res += kwd + ' '
        if f.label:
            res += '[{}] '.format(f.label)
        res += str(f.formula) + '\n'
    return res

def print_module(mod):
    print ivy_logic.sig
    thing = ''
    for kwd,lst in [('axiom',mod.labeled_axioms),
                    ('property',mod.labeled_props),
                    ('init',mod.labeled_inits),
                    ('conjecture',mod.labeled_conjs),
                    ('definition',mod.definitions),
                    ('definition',mod.native_definitions),]:
        
        thing += labeled_fmlas_to_str(kwd,lst)

    for tn in sorted(mod.sig.interp):
        thing += "interp {} -> {}\n".format(tn,mod.sig.interp[tn])
    print thing

    for name,action in mod.initializers:
        print iu.pretty("after init {" + str(action) + "}")

    for x,y in mod.actions.iteritems():
        print iu.pretty(ia.action_def_to_str(x,y))

    for x in sorted(mod.public_actions):
        print 'export {}'.format(x)


#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

#
# We define structures for temporal proof goals.
#
# A temporal proof goal is of the form `M |= phi` where
# `M` is a progam term and phi is a temporal formula.
#
# A normal program is of the form:
#
#     let
#         name1 = action1
#         ...
#         namen = procn
#     in
#         init;
#         while *
#         invariant inv1;
#         ...
#         invariant invm;
#         {
#             diverge;
#             if * { call1 }
#             else if * {call2}
#             ...
#             else {callk}
#         }
#
#
# where
#
# - `namei` is an action name,
# - `actioni` is an action term,
# - `init` is an initial progam statement
# - `calli` is a call term
# - `diverge` is a statment that skips or diverges
# - `invi` is a non-temporal formula.
#
# An action term is of the form:
#
#     action (inputs) returns (outputs)
#
# where inputs and outputs are lists of symbols.
#
# A call term is of the form:
#
#     {
#         var inp1 : inptype1;
#         ...
#         var inpn : inptype1;
#
#         var out1 : outtype1;
#         ...
#         var outm : outtypem;
#
#         call (out1,...outm) := name (inp1,...,inpn)
#     }
#
# That is, it calls the action bound to name `name` with
# non-deterministic arguments;
#
# The `diverge` statement models the fact the the environement
# may cease to call program actions at any time.
#
#
# We say `M` is failure-free if it has no execution leading to failure
# of an assertion (equivalently if `wlp(M,true)` is valid).
#
# We say `M |= phi` is true if `M` is failure-free and it every
# infinite trace of `M` satisfies phi. If `phi=true` this is
# equivalent to validity `wlp(M,true)`. In this case we say the goal
# is "reduced". A liveness-to-safety transformation is a tactic that
# reduces `phi` to `true`.
# 
# To more easily manipluate normal programs, we introduce a special
# syntax node for them. We introduce the following classes for this purpose:
#
# - ActionTerm is an action term
# - ActionTermBinding is a name/action term pair
# - NormalProgram is consists of:
#       - a list of ActionTermBindings `namei = actioni`
#       - an initial statement `init`
#       - a list of named loop invariants `invi`
#       - as list of action names of the call terms
#

import ivy_logic as il
import ivy_ast as ia
import ivy_proof as ipr
import ivy_utils as iu
import ivy_actions as iact

class ActionTerm(ia.AST):
    """ Class representing action terms """
    def __init__(self,inputs,outputs,stmt):
        self.inputs,self.outputs,self.stmt = inputs,outputs,stmt;
    @property
    def args(self):
        """ the only subterm is the statement """
        return [self.stmt]
    def clone(self,args):
        """ clone relaces the statement in an action """
        res = ActionTerm(self.inputs,self.outputs,args[0])
        copy_attributes(self,res)
        return res
    def __str__(self):
        res = 'action'
        def params(ps,text):
            return (text + '(' + ','.join(il.typed_sym_to_str(x) for x in ps) + ')'
                    if len(ps) > 0 else '')
        res += params(self.inputs,'')
        res += params(self.outputs,' returns')
        res += '{' + str(self.stmt) + '}'
        return res
    
def clone_action(self,inputs,outputs,stmt):
    """ replace the inputs, output and statement in an action,
    but keep other attributes. """
    res = ActionTerm(inputs,outputs,stmt)
    copy_attributes(self,res)
    return res

class ActionTermBinding(ia.AST):
    """ Class representing a binding of action term to name """
    def __init__(self,name,action):
        self.name,self.action = name,action
    @property
    def args(self):
        """ the only subterm is the statement """
        return [self.stmt]
    def clone(self,args):
        """ clone relaces the statement in an action """
        res = ActionTerm(self.inputs,self.outputs,args[0])
        copy_attributes(self,res)
        return res
    def __str__(self):
        return '{} = {}'.format(self.name,self.action)

class NormalProgram(ia.AST):
    """ a normal program. bindings should be list of bindings """
    def __init__(self,bindings,init,invars,calls):
        self.bindings,self.init,self.invars,self.calls = bindings,init,invars,calls
    @property
    def args(self):
        """ There are no subterms """
        return []
    def clone(self,args):
        """ clone just copies this node """
        res = NormalProgram(self.bindings,self.init,self.invars,self.calls)
        ia.copy_attrs(self,res)
        return res
    @property
    def binding_map(self):
        return dict((x.name,new_action_to_old(x.action)) for x in self.bindings)
    def __str__(self):
        res = ['let\n']
        for b in self.bindings:
            res.append('    ' + str(b) + '\n')
        res.append('in\n')
        res.append(str(self.init) + '\n')
        res.append('while *\n')
        for invar in self.invars:
            res.append('    invariant ' + str(invar) + '\n')
        res.append('{\n')
        res.append('diverge;\n')
        res.append('    call one of {' + ','.join(str(n) for n in self.calls) + '}\n')
        res.append('}\n')
        return ''.join(res)

class TemporalModels(ia.AST):    
    """ A predicate of the form M |= phi where M is a NormalProgram
    and phi is a temporal formula """
    def __init__(self,model,fmla):
        self.model,self.fmla = model,fmla
    @property
    def args(self):
        """ The fmla is the only subterm """
        return [self.fmla]
    def clone(self,args):
        """ clone just copies this node """
        res = TemporalModels(self.model,args[0])
        ia.copy_attrs(self,res)
        return res
    def __str__(self):
        return str(self.model) + ' |= ' + str(self.fmla)

def old_action_to_new(act):
    return ActionTerm(act.formal_params,act.formal_returns,act)

def new_action_to_old(act):
    return act.stmt

def normal_program_from_module(mod):
    bindings = [ActionTermBinding(name,old_action_to_new(act)) for name,act in mod.actions.iteritems()]
    init = iact.Sequence(*[action for actname,action in mod.initializers])
    invars = mod.conjs
    calls = sorted(mod.public_actions)
    return NormalProgram(bindings,init,invars,calls)

#
# This is a test tactic for temporal properties that proves a "globally" formula using
# the invariance rule.
#
# The tactic apply to a conclusion of the form "globally phi" where phi is non-temporal
# and is used like this:
#
#     tactic invariance with
#         invariant [inv1] aux1
#         ...
#
# The formula phi and the auxiliary invariants auxi are added to the model as invariants,
# and the conclusion is converted to "true".

def invariance_tactic(goals,proof):
    goal = goals[0]                  # pick up the first proof goal
    conc = ipr.goal_conc(goal)       # get its conclusion
    if not isinstance(conc,TemporalModels):
        raise iu.IvyError(proof,'proof goal is not temporal')
    model = conc.model
    fmla = conc.fmla
    if not isinstance(fmla,il.Globally):
        raise iu.IvyError(proof,'invariance tactic applies only to globally formulas')
    if not isinstance(fmla,il.Globally):
        raise iu.IvyError(proof,'invariance tactic applies only to globally formulas')
    invar = fmla.args[0]
    if il.is_temporal(invar):
        raise iu.IvyError(proof,'invariance tactic applies only formulas "globally p"' +
                       ' where p is non-temporal')

    # Collect the auxiliary invariants
    invars = [inv.compile() for inv in proof.tactic_decls]

    # Add the invariant phi to the list
    invars.append(ipr.make_goal(goal.lineno,goal.label,[],invar))

    # Add the invariant list to the model
    model = model.clone([])
    model.invars = model.invars + invars
    
    # Change the conclusion formula to M |= true
    conc = TemporalModels(model,il.And())

    # Build the new goal
    goal = ipr.make_goal(goal.lineno,goal.label,ipr.goal_prems(goal),conc)

    # Return the new goal stack

    return [goal] + goals[1:]

# Register the invariance tactic

ipr.register_tactic('invariance',invariance_tactic)

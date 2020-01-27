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
#             assume asm1;
#             ...
#             assume asmp;
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
# - `invi` is a non-temporal formula
# -  `asmi` is a non-temporal formula.
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
#       - a list of named loop assumptions `asmi`
#       - as list of action names of the call terms
#
# Modular temporal semantics
# --------------------------
#
# Each temporal operator has an 'environment', which roughly
# corresponds to an isolate (to be more precise, the actions of an
# isolate and all of the actions of the isolates it depends
# on). Environments overlap, so at any moment the program is
# executing in some set of environments. To a temporal operator,
# program execution within its environment appears to be
# instantaneous or to diverge. In other words from the operator's
# point of view there are no intermediate states inside the code
# of its environment, so actions in the environment appear atomic.
#
# In the current implementation, the set of environments in which a
# given action executes is determined statically, and is provided by a
# list of environment labels attached to the action. This makes it
# relatively easy to determine at which program execution points the
# tableau automaton for a given operator must be synchronized. That
# is, steps of the tableau automaton never occur within the operator's
# environment. Outside of the environment, they occur either when some
# symbol that the formula depends on is mutated (i.e., when a non-stutter
# step occurs) or upon exit from the operator's environment (i.e., after a
# call statement into the environment from the outside.

import ivy_logic as il
import ivy_ast as ia
import ivy_proof as ipr
import ivy_utils as iu
import ivy_actions as iact
import ivy_logic_utils as ilu
from collections import defaultdict

class ActionTerm(ia.AST):
    """ Class representing action terms """
    def __init__(self,inputs,outputs,labels,stmt):
        self.inputs,self.outputs,self.labels,self.stmt = inputs,outputs,labels,stmt;
    @property
    def args(self):
        """ the only subterm is the statement """
        return [self.stmt]
    def clone(self,args):
        """ clone relaces the statement in an action """
        res = ActionTerm(self.inputs,self.outputs,self.labels,args[0])
        ia.copy_attrs(self,res)
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
    
def clone_action(self,inputs,outputs,labels,stmt):
    """ replace the inputs, output, labels and statement in an action,
    but keep other attributes. """
    res = ActionTerm(inputs,outputs,labels,stmt)
    copy_attrs(self,res)
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
        """ clone relaces the action in a binding """
        res = ActionTermBinding(self.name,args[0])
        ia.copy_attrs(self,res)
        return res
    def __str__(self):
        return '{} = {}'.format(self.name,self.action)

class NormalProgram(ia.AST):
    """ a normal program. bindings should be list of bindings """
    def __init__(self,bindings,init,invars,asms,calls):
        self.bindings,self.init,self.invars,self.asms,self.calls = bindings,init,invars,asms,calls
    @property
    def args(self):
        """ There are no subterms """
        return []
    def clone(self,args):
        """ clone just copies this node """
        res = NormalProgram(self.bindings,self.init,self.invars,self.asms,self.calls)
        ia.copy_attrs(self,res)
        return res
    @property
    def binding_map(self):
        return dict((x.name,new_action_to_old(x.action)) for x in self.bindings)
    def __str__(self):
        res = ['\nlet\n']
        for b in self.bindings:
            res.append('    ' + str(b) + '\n')
        res.append('in\n')
        res.append('    ' + str(self.init) + '\n')
        res.append('    while *\n')
        for invar in self.invars:
            res.append('        invariant ' + str(invar) + '\n')
        res.append('    {\n')
        res.append('        diverge;\n')
        for asm in self.asms:
            res.append('        assume ' + str(asm) + ';\n')
        res.append('        call one of {' + ','.join(str(n) for n in self.calls) + '}\n')
        res.append('    }\n')
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
    return ActionTerm(act.formal_params,act.formal_returns,act.labels,act)

def new_action_to_old(act):
    return act.stmt

def normal_program_from_module(mod):
    bindings = [ActionTermBinding(name,old_action_to_new(act)) for name,act in mod.actions.iteritems()]
    init = iact.Sequence(*[action for actname,action in mod.initializers])
    invars = mod.labeled_conjs
    asms = mod.assumed_invariants
    calls = sorted(mod.public_actions)
    return NormalProgram(bindings,init,invars,asms,calls)

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

def invariance_tactic(prover,goals,proof):
    goal = goals[0]                  # pick up the first proof goal
    conc = ipr.goal_conc(goal)       # get its conclusion
    if not isinstance(conc,TemporalModels):
        raise iu.IvyError(proof,'proof goal is not temporal')
    model = conc.model
    fmla = conc.fmla
    if not isinstance(fmla,il.Globally):
        raise iu.IvyError(proof,'invariance tactic applies only to globally formulas')
    invar = fmla.args[0]
    if il.is_temporal(invar):
        raise iu.IvyError(proof,'invariance tactic applies only formulas "globally p"' +
                       ' where p is non-temporal')

    # Collect the auxiliary invariants
    invars = [inv.compile() for inv in proof.tactic_decls]

    # Add the invariant phi to the list
    invars.append(ipr.clone_goal(goal,[],invar))

    # Add the invariant list to the model
    model = model.clone([])
    model.invars = model.invars + invars
    
    # Get all the implicit globally properties from the proof
    # environment. Each temporal operator has an 'environment'. The
    # operator applies to states *not* in actions labeled with this
    # environment. This has several consequences:
    #
    # 1) The operator's semantic constraint is an assumed invariant (i.e.,
    # it holds outside of any action)
    #
    # 2) An 'event' for the temporal operator occurs when (a) we return
    # from an execution context inside its environment to one outside,
    # or (b) we are outside the environment of the operator and some symbol
    # occurring in it's body is mutated.
    #
    # 3) At any event for the operator, we update its truth value and
    # and re-establish its senatic constraint.
    #
    #
    # The following procedure instruments a statement with operator events for
    # both the property to be proved and the invariant assumptions (all G properties here).
    # This depends on the statement's environment, that is, current set of environment
    # labels.
    #
    # Currently, the environment labels of a statement have to be
    # statically determined, but this could change, i.e., the labels
    # could be represented by boolean variables. 
    #
    # TODO: there is something a bit inelegant here, because when we return from
    # an exported action to the external environment, we need to update the operator
    # states, however, we do *not* want to do this when returning to in internal caller.
    # The best solution currently for this is to duplication the actions so there
    # is one version for internal callers and one for external callers. This issue doesn't
    # affect this simple invariance tactic, because it doesn't need to update the truth
    # values of the operators.
    
    # Get all the G properties from the prover environment as assumptions
    
    assumed_gprops = [x for x in prover.axioms if not x.explicit and x.temporal and il.is_gprop(x.formula)]
    gprops = [x.formula for x in assumed_gprops]
    gproplines = [x.lineno for x in assumed_gprops]
    
    # We represent the property G phi to be proved by its negation F ~phi.
    gprops.append(il.Eventually(fmla.environ,il.Not(invar)))
    gproplines.append(goal.lineno)

    # Make some memo tables

    envprops = defaultdict(list)
    symprops = defaultdict(list)
    for prop in gprops:
        envprops[prop.environ].append(prop)
        for sym in ilu.symbols_ast(prop):
            symprops[sym].append(prop)
    actions = dict((b.name,b.action) for b in model.bindings)
    lines = dict(zip(gprops,gproplines))
            
    def instr_stmt(stmt,labels):

        # first, recur on the sub-statements
        args = [instr_stmt(a,labels) if isinstance(a,iact.Action) else a for a in stmt.args]
        res = stmt.clone(args)

        # now add any needed temporal events after this statement
        event_props = set()

        # first, if it is a call, we must consider any events associated with
        # the return
        
        if isinstance(stmt,iact.CallAction):
            callee = actions[stmt.callee()]  # get the called action
            exiting = [l for l in callee.labels if l not in labels] # environments we exit on return
            for label in exiting:
                for prop in envprops[label]:
                    event_props.add(prop)

        # Second, if a symbol is modified, we must add events for every property that
        # depends on the symbol, but only if we are not in the environment of that property. 
                    
        for sym in stmt.modifies():
            for prop in symprops[sym]:
                if prop.environ not in labels:
                    event_props.add(prop)
                    
        # Now, for every property event, we update the property state (none in this case)
        # and also assert the property semantic constraint. 

        events = [prop_event(prop,lines[prop]) for prop in event_props]
        res =  iact.postfix_action(res,events)
        stmt.copy_formals(res) # HACK: This shouldn't be needed
        return res

    # Add property events to all of the actions:

    model.bindings = [b.clone([b.action.clone([instr_stmt(b.action.stmt,b.action.labels)])])
                      for b in model.bindings]
    
    # Add all the assumed invariants to the model

    model.asms.extend([p.clone([p.label,p.formula.args[0]]) for p in assumed_gprops])
    
    # if len(gprops) > 0:
    #     assumes = [gprop_to_assume(x) for x in gprops]
    #     model.bindings = [b.clone([prefix_action(b.action,assumes)]) for b in model.bindings]

    # Change the conclusion formula to M |= true
    conc = TemporalModels(model,il.And())

    # Build the new goal
    goal = ipr.clone_goal(goal,ipr.goal_prems(goal),conc)

    # Return the new goal stack

    goals = [goal] + goals[1:]
    return goals

#    return implicit_tactic(prover,goals,None)

# Here, we compute the events for properties of the for G phi and F ~phi.
# There is no state needed for these properties. For G phi we use "assume phi"
# and for F ~phi we use "assert phi".

def prop_event(gprop,lineno):
    if isinstance(gprop,il.Eventually):
        # Formula of the form F ~phi translates to "assert phi"
        res = iact.AssertAction(gprop.args[0].args[0])
    else:
        # Formula of the form G phi translates to "assume phi"
        res = iact.AssumeAction(gprop.args[0])
    res.lineno = lineno
    return res

# def gprop_to_assume(gprop):
#     res = iact.AssumeAction(gprop.formula.args[0])
#     res.lineno = gprop.lineno
#     return res

def prefix_action(self,stmts):
    return self.clone([iact.prefix_action(self.stmt,stmts)])

# Register the invariance tactic

ipr.register_tactic('invariance',invariance_tactic)


# This tactic brings in all of the implicit properties from the proof environment
# into the current goal.

# TODO: pull in implicit definitions

def implicit_tactic(prover,goals,proof):
    implicit_axioms = [x for x in prover.axioms if not x.explicit]
    print 'temporal axioms: {}'.format([x.temporal for x in implicit_axioms])
    goal,goals = goals[0],goals[1:]
    goal = ipr.goal_prefix_prems(goal,implicit_axioms,goal.lineno)
    return [goal]+goals

    

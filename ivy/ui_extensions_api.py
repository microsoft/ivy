#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This file contains the API used to create Ivy UI extensions.

Ivy UI extensions can be used to add buttons and menu options to the
Ivy UI, and to bind them with user interaction functions.

Extension points have string identifiers.

"""

from textwrap import dedent
from inspect import isgeneratorfunction
from functools import wraps
from collections import OrderedDict

from IPython import get_ipython
from IPython.display import display
import IPython.html.widgets as widgets

from widget_modal import ModalWidget
from ivy_logic_utils import and_clauses, Clauses, close_epr
from z3_utils import z3_implies



def set_context(analysis_session_widget):
    """
    This module provides global context access to the UI instance
    """
    global _analysis_session_widget
    global _concept_session_widget
    global _analysis_session
    global _concept_session
    _analysis_session_widget = analysis_session_widget
    _analysis_session = _analysis_session_widget.session
    _concept_session_widget = _analysis_session_widget.concept
    _concept_session = _concept_session_widget.concept_session


class ExtensionPoint(object):
    """
    A list of callbacks, with register, unregister, and __call__.

    The prototype field serves for documentation.

    Note that this class can be used as a decorator to declare
    extension points from their prototypes.
    """

    def __init__(self, prototype=None):
        self.callbacks = []
        self.prototype = prototype

    def register(self, function):
        if not callable(function):
            raise TypeError('Need a callable, got {}'.format(function))
        self.callbacks.append(function)
        return function # for use as a decorator

    def action(self, label=None):
        """
        A decorator that easily lets you register a single function as a
        UI action.

        Note that this also applies interaction to the function.
        """
        def decorator(function):
            _label = (label if label is not None else
                      function.__name__.replace('_', ' '))
            self.register(lambda *args, **kwargs: [(_label, interaction(function))])
            return function
        return decorator

    def unregister(self, function):
        self.callbacks.remove(function)

    def __call__(self, context, *args, **kwargs):
        """
        Run all callbacks, return a list with results.

        Exceptions in callbacks are printed using IPython's
        showtraceback, and their result is ignored.

        If not running under IPython, exceptions are raised.
        """
        set_context(context)
        results = []
        for function in self.callbacks:
            try:
                result = function(*args, **kwargs)
            except Exception:
                ip = get_ipython()
                if ip is None or True: # always raise, for development
                    raise
                else:
                    ip.showtraceback()
            else:
                results.append(result)
        return results

# Extension point declerations using ExtensionPoint as a decorator
# with prototype functions for documentation

@ExtensionPoint
def arg_node_actions(node):
    """
    Add options to the ARG node context menu.
    node is an ivy_interp.State

    Returns a list of tuples of the form (action_name, callback, *args) for possible node actions
    the callback is called like this: callback(node, *args)
    """

@ExtensionPoint
def goal_node_actions(node):
    """
    Add options to the proof goal node context menu.
    node is a ProofGoal

    Returns a list of tuples of the form (action_name, callback, *args) for possible node actions
    the callback is called like this: callback(node, *args)
    """


@arg_node_actions.register
def execute_actions(s):
    return [
        (action, execute_arg_action, action)
        for action in sorted(_analysis_session.analysis_state.ivy_ag.actions.keys())
    ]

@arg_node_actions.register
def try_conjectures(s):
    axioms = _analysis_session.analysis_state.ivy_interp.background_theory()
    premise = (and_clauses(axioms, s.clauses)).to_formula()
    return [
        ('conj: {}'.format(conj), try_conjecture, conj)
        for conj in _analysis_session.analysis_state.ivy_interp.conjs
        if not z3_implies(premise, conj.to_formula())
    ]


def run_interaction(f, args, kwargs):
    """
    Run an interaction function, which may yield FrontEndOperation
    objects to interact with the front end.
    """
    g = f(*args, **kwargs)

    def advance(to_send=None):
        try:
            op = g.send(to_send)
        except StopIteration:
            return
        except InteractionError as e:
            ShowModal("Error", [widgets.Latex(e.message)]).submit()
        else:
            op.submit(advance)

    advance()

def interaction(f):
    """
    Decorator used on interaction functions. Once decorated, they will
    be run using run_interaction when they are called (unless they
    don't contain yield statements, in which case they decorator does
    nothing).
    """
    @wraps(f)
    def wrapper(*args, **kwargs):
        if _analysis_session_widget.current_step != len(_analysis_session_widget.session.history) - 1:
            ShowModal("Error", [widgets.Latex(
                "Must be on the last step in the history to do this. Aborting."
            )]).submit()
            return
        run_interaction(f, args, kwargs)

    if isgeneratorfunction(f):
        return wrapper
    else:
        return f


class InteractionError(Exception):
    pass


class FrontEndOperation(object):
    """
    This class represents front end operations.

    Since communication with the front end is asynchronous, when
    performing a front end operation, you provide a callback function.
    """
    def submit(self, on_done=None):
        raise NotImplementedError()

class ExecuteNewCell(FrontEndOperation):
    def __init__(self, code, dedent_and_strip=True):
        if dedent_and_strip:
            code = dedent(code.strip())
        self.code = code
        self.ip = get_ipython()

    def submit(self, on_done=None):
        self.on_done = on_done
        self.ip.events.register('post_run_cell', self.post_run_cell)
        _analysis_session_widget.proof_graph.execute_new_cell(self.code)

    def post_run_cell(self):
        last_input = self.ip.history_manager.input_hist_raw[-1]
        last_output = self.ip.history_manager.output_hist.get(self.ip.execution_count)
        self.ip.events.unregister('post_run_cell', self.post_run_cell)
        assert last_input == self.code, "Seems like another cell was executed? {!r} != {!r}".format(
            last_input, self.code
        )
        if self.on_done is not None:
            self.on_done(last_output)


class ShowModal(FrontEndOperation):
    """
    A front end operation that displays a new modal dialog.

    The result is True if the user clicked OK and False
    otherwise. Other data entered by the user are available through
    widgets that populate the modal dialog.
    """
    def __init__(self, title, children):
        self.modal = ModalWidget(title=title, children=children)
        self.modal.on_close(self.on_close)

    def submit(self, on_done=None):
        self.on_done = on_done
        display(self.modal)

    def on_close(self, modal, button):
        if self.on_done is not None:
            self.on_done(button == 'OK')


class UserSelect(ShowModal):
    """
    A front end operation that asks the user to select one option or
    cancel.

    The result is the user selected value, or None if the user clicked
    cancel.

    options should be a dict (possibly OrderedDict) mapping labels to
    values
    """
    def __init__(self, options, title='', prompt='', default=None):
        self.prompt = widgets.Latex(prompt)
        kwargs = {'options': options}
        if default is not None:
            kwargs['value'] = default
        self.select = widgets.Select(**kwargs)
        super(UserSelect, self).__init__(title, [self.prompt, self.select])

    def on_close(self, modal, button):
        if self.on_done is not None:
            self.on_done(
                self.select.value if button == 'OK' else None
            )


class UserSelectMultiple(ShowModal):
    """
    A front end operation that asks the user to select multiple
    options or cancel.

    The result is a list of user selected values, or None if the user
    clicked cancel.

    options should be a dict (possibly OrderedDict) mapping labels to
    values

    If present, default must also be a list
    """
    def __init__(self, options, title='', prompt='', default=None):
        self.prompt = widgets.Latex(prompt)
        kwargs = {'options': options, 'width': '100%'}
        if default is not None:
            kwargs['value'] = default
        self.select = widgets.SelectMultiple(**kwargs)
        super(UserSelectMultiple, self).__init__(title, [self.prompt, self.select])

    def on_close(self, modal, button):
        if self.on_done is not None:
            self.on_done(
                self.select.value if button == 'OK' else None
            )


@interaction
def execute_arg_action(node, action):
    code = '''execute_action(arg_node({!r}), get_action({!r}), {})'''.format(
        node.id,
        action,
        _analysis_session_widget.select_abstractor.value,
    )
    yield ExecuteNewCell(code)


@interaction
def try_conjecture(node, conj):
    code = dedent('''
    f = negate_clauses(Clauses([{!r}]))
    push_new_goal(f, arg_node({!r}))
    ''').strip().format(
        conj.to_open_formula(),
        node.id,
    )
    yield ExecuteNewCell(code)


@arg_node_actions.action('new goal')
def arg_new_goal(node):
    code = '''push_new_goal(true_clauses(), arg_node({!r}))'''.format(
        node.id,
    )
    yield ExecuteNewCell(code)

@arg_node_actions.action('recalculate')
def arg_recalculate(node):
    code = dedent('''
    node = arg_node({!r})
    recalculate_facts(node, arg_get_conjuncts(arg_get_pred(node)))
    ''').strip().format(
        node.id,
    )
    yield ExecuteNewCell(code)

@arg_node_actions.action('check cover')
def arg_check_cover(node):
    """
    Check covering
    """
    if len(_analysis_session_widget.arg.selected) != 1:
        raise InteractionError("You must select one node to check covering by.")
    by = _analysis_session_widget.arg.selected[0]
    if len(by) != 1:
        raise InteractionError("You must select one node to check covering by. " +
                               "Seem's you've selected an edge.")
    by = by[0]
    code = dedent('''
    check_cover(arg_node({!r}), arg_node({!r}))
    ''').strip().format(
        node.id,
        by.id,
    )
    yield ExecuteNewCell(code)


@arg_node_actions.action('remove facts')
def arg_remove_facts(node):
    """
    Let the user choose facts to remove from an ARG node
    """
    user_selection = yield UserSelectMultiple(
        title='Remove Facts',
        prompt='Select facts to remove from ARG node {}:'.format(node.id),
        options=OrderedDict([
            (str(close_epr(x)), x) for x in node.clauses.fmlas
        ]),
    )
    if user_selection is None:
        return
    code = dedent('''
    remove_facts(arg_node({!r}), *{!r})
    ''').strip().format(
        node.id,
        list(user_selection),
    )
    yield ExecuteNewCell(code)


@interaction
def apply_goal_tactic(goal, tactic):
    """
    Create a new cell in the notebook that applies the tactic
    """
    code = '''{}(goal({!r}))'''.format(tactic, goal.id)
    yield ExecuteNewCell(code)

@arg_node_actions.action('join with selection')
def arg_join2(node):
    """
    Binary join
    """
    sels = _analysis_session_widget.arg.selected
    if len(sels) == 0:
        raise InteractionError("You must select at least one node to join with.")
    if any(len(x) != 1 for x in sels):
        raise InteractionError("You must select one node to with. " +
                               "Seem's you've selected an edge.")
    sels = [x[0] for x in sels if len(x) == 1]
    user_selection = yield UserSelect(options=dict((str(x.id),x) for x in sels),title='Binary join',prompt='Choose a node to join with')    
    code = dedent('''
    join2(arg_node({!r}), arg_node({!r}))
    ''').strip().format(
        node.id,
        user_selection.id,
    )
    yield ExecuteNewCell(code)

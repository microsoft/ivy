#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Script to create a new notebook for a given .ivy file, that is
used to BMC the conjectures to debug the model.

Usage:
python ivy_bmc.py ivy_filename
"""

import re
import sys
import os
from os.path import dirname, join, pardir, pathsep, abspath

import IPython


if __name__ == '__main__':
    #ivy_filename = abspath(sys.argv[1])
    ivy_filename = sys.argv[1]

    notebook_source = r"""{
 "cells": [
  {
   "cell_type": "code",
   "execution_count": null,
   "metadata": {
    "collapsed": false,
    "scrolled": true
   },
   "outputs": [],
   "source": [
    "from IPython.display import display\n",
    "import z3\n",
    "z3.set_param('smt.random_seed', 0)\n",
    "import random\n",
    "random.seed(0)\n",
    "from proof import AnalysisSession\n",
    "from widget_analysis_session import AnalysisSessionWidget\n",
    "from tactics_api import *\n",
    "import tactics_api as ta\n",
    "import ivy_actions\n",
    "from tactics import *\n",
    "from logic import *\n",
    "from ivy_logic_utils import true_clauses, false_clauses, Clauses\n",
    "import ivy_module\n",
    "from ivy_interp import EvalContext\n",
    "m = ivy_module.Module()\n",
    "m.__enter__()\n",
    "ctx = EvalContext(check=False)\n",
    "ctx.__enter__()\n",
    "ivy_widget = AnalysisSessionWidget()\n",
    "session = AnalysisSession(IVY_FILENAME, ivy_widget)\n",
    "set_context(session)\n",
    "ivy_widget.transition_view.conjectures = session.analysis_state.ivy_interp.conjs[:]\n",
    "ta._ivy_ag.actions.setdefault('initialize', ivy_actions.Sequence())\n",
    "ta._ivy_ag.actions.setdefault('step', ta.get_big_action())\n",
    "ivy_widget.transition_view.autodetect_transitive()\n",
    "display(ivy_widget)\n",
    "ivy_widget.transition_view.bmc_bound.value = 5\n",
    "if ivy_widget.transition_view.bmc_conjecture(None, ta.and_clauses(*ta._ivy_interp.conjs), True, False):\n",
    "    for conj in ta._ivy_interp.conjs[-1:]:\n",
    "        if ivy_widget.transition_view.bmc_conjecture(None, conj, True):\n",
    "            break"
   ]
  }
 ],
 "metadata": {
  "kernelspec": {
   "display_name": "Python 2",
   "language": "python",
   "name": "python2"
  },
  "language_info": {
   "codemirror_mode": {
    "name": "ipython",
    "version": 2
   },
   "file_extension": ".py",
   "mimetype": "text/x-python",
   "name": "python",
   "nbconvert_exporter": "python",
   "pygments_lexer": "ipython2",
   "version": "2.7.6"
  }
 },
 "nbformat": 4,
 "nbformat_minor": 0
}
""".replace('IVY_FILENAME', repr(ivy_filename))

    # if X.bmc.ipynb exists, open it, otherwise create a new X.ivy.bmc.ipynb
    notebook_filename = ivy_filename[:-4] + '.bmc.ipynb'
    if os.path.isfile(notebook_filename):
        print "Opening existing notebook: {}".format(notebook_filename)
    else:
        notebook_filename = ivy_filename + '.bmc.ipynb'
        print "Creating new notebook: {}".format(notebook_filename)
        open(notebook_filename, 'w').write(notebook_source)

    d = dirname(__file__)
    os.environ['PYTHONPATH'] = pathsep.join([
        os.environ['PYTHONPATH'],
        d,
        join(d, pardir, 'src', 'ivy'),
    ])
    sys.argv = ['ipython', 'notebook', notebook_filename]
    sys.argv[0] = re.sub(r'(-script\.pyw|\.exe)?$', '', sys.argv[0])
    sys.exit(IPython.start_ipython())

#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy
import ivy_interp as itp
import ivy_actions as act
import ivy_utils as utl
import ivy_logic_utils as lut
import tk_ui as ui
import ivy_logic as lg
import ivy_utils as iu
import ivy_module as im
import ivy_alpha
import ivy_art
import ivy_interp
import ivy_compiler
import ivy_isolate

import sys

diagnose = iu.BooleanParameter("diagnose",False)

def display_cex(msg,ag):
    print msg
    if diagnose.get():
        ui.ui_main_loop(ag)
    exit(1)
    
def check_conjectures(kind,msg,ag,state):
    failed = itp.undecided_conjectures(state)
    if failed:
        print "{} failed.".format(kind)
        if diagnose.get():
            gui = ui.new_ui()
            agui = gui.add(ag)
            gui.tk.update_idletasks() # so that dialog is on top of main window
            agui.try_conjecture(state,msg="{}\nChoose one to see counterexample.".format(msg))
            gui.tk.mainloop()
        exit(1)
    
def usage():
    print "usage: \n  {} file.ivy".format(sys.argv[0])
    sys.exit(1)

def check_module():
    # If user specifies an isolate, check it. Else, if any isolates
    # are specificied in the file, check all, else check globally.

    isolate = ivy_compiler.isolate.get()
    if isolate != None:
        isolates = [isolate]
    else:
        isolates = sorted(list(im.module.isolates))
        if len(isolates) == 0:
            isolates = [None]

    for isolate in isolates:
        if len(im.module.isolates[isolate].verified()) == 0:
            continue # skip if nothing to verify
        if isolate:
            print "Checking isolate {}...".format(isolate)
        with im.module.copy():
            ivy_isolate.create_isolate(isolate) # ,ext='ext'
            ag = ivy_art.AnalysisGraph(initializer=ivy_alpha.alpha)
            with ivy_interp.EvalContext(check=False):
                check_conjectures('Initiation','These conjectures are false initially.',ag,ag.states[0])
                for a in sorted(im.module.public_actions):
                    print "trying {}...".format(a)
                    ag.execute_action(a,prestate=ag.states[0])
                    cex = ag.check_bounded_safety(ag.states[-1])
                    if cex is not None:
                        display_cex("safety failed",cex)
                    check_conjectures('Consecution','These conjectures are not inductive.',ag,ag.states[-1])


def main():
    ivy.read_params()
    iu.set_parameters({'mode':'induction'})
    if len(sys.argv) != 2 or not sys.argv[1].endswith('ivy'):
        usage()
    with im.Module():
        with utl.ErrorPrinter():
            ivy.source_file(sys.argv[1],ivy.open_read(sys.argv[1]),create_isolate=False)
            check_module()
    print "OK"


if __name__ == "__main__":
    main()


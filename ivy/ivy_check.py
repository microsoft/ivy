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
coverage = iu.BooleanParameter("coverage",True)


def display_cex(msg,ag):
    if diagnose.get():
        ui.ui_main_loop(ag)
        exit(1)
    raise iu.IvyError(None,msg)
    
def check_properties():
    if itp.false_properties():
        if diagnose.get():
            print "Some properties failed."
            gui = ui.new_ui()
            gui.tk.update_idletasks() # so that dialog is on top of main window
            gui.try_property()
            gui.mainloop()
            exit(1)
        raise iu.IvyError(None,"Some properties failed.")
    im.module.labeled_axioms.extend(im.module.labeled_props)


def check_conjectures(kind,msg,ag,state):
    failed = itp.undecided_conjectures(state)
    if failed:
        if diagnose.get():
            print "{} failed.".format(kind)
            gui = ui.new_ui()
            agui = gui.add(ag)
            gui.tk.update_idletasks() # so that dialog is on top of main window
            agui.try_conjecture(state,msg="{}\nChoose one to see counterexample.".format(msg))
            gui.tk.mainloop()
            exit(1)
        raise iu.IvyError(None,"{} failed.".format(kind))
    
def usage():
    print "usage: \n  {} file.ivy".format(sys.argv[0])
    sys.exit(1)

def check_module():
    # If user specifies an isolate, check it. Else, if any isolates
    # are specificied in the file, check all, else check globally.

    missing = []

    isolate = ivy_compiler.isolate.get()
    if isolate != None:
        isolates = [isolate]
    else:
        isolates = sorted(list(im.module.isolates))
        if len(isolates) == 0:
            isolates = [None]
        else:
            if coverage.get():
                missing = ivy_isolate.check_isolate_completeness()
            
    if missing:
        raise iu.IvyError(None,"Some assertions are not checked")

    for isolate in isolates:
        if isolate != None and len(im.module.isolates[isolate].verified()) == 0:
            continue # skip if nothing to verify
        if isolate:
            print "Checking isolate {}...".format(isolate)
        with im.module.copy():
            ivy_isolate.create_isolate(isolate) # ,ext='ext'
            check_properties()
            ag = ivy_art.AnalysisGraph(initializer=ivy_alpha.alpha)
            if im.module.initializers:
                cex = ag.check_bounded_safety(ag.states[0])
                if cex is not None:
                    display_cex("safety failed in initializer",cex)
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


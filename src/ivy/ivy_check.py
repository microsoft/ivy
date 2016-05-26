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
    
def usage():
    print "usage: \n  {} file.ivy".format(sys.argv[0])
    sys.exit(1)

if __name__ == "__main__":
    ivy.read_params()
    if len(sys.argv) != 2 or not sys.argv[1].endswith('ivy'):
        usage()
    with im.Module():
        isolate = ivy_compiler.isolate.get()
        ivy.source_file(sys.argv[1],ivy.open_read(sys.argv[1]),create_isolate=False)

        # If user specifies an isolate, check it. Else, if any isolates
        # are specificied in the file, check all, else check globally.

        if isolate != None:
            isolates = [isolate]
        else:
            isolates = sorted(list(im.module.isolates))
            if len(isolates) == 0:
                isolates = [None]

        for isolate in isolates:
            if len(im.module.isolates[isolate].verified()) == 0:
                continue # skip if nothing to verify
            with im.module.copy():
                ivy_isolate.create_isolate(isolate,ext='ext')
                ag = ivy_art.AnalysisGraph(initializer=ivy_alpha.alpha)
                with utl.ErrorPrinter():
                    with ivy_interp.EvalContext(check=False):
                        ag.execute_action('ext')
                        cex = ag.check_bounded_safety(ag.states[-1])
                        if cex is not None:
                            display_cex("safety failed",cex)
    print "OK"


#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import sys

# pick up some paths if were are run as main
if __name__ == "__main__":
    mypath = sys.path[0]
    sys.path.insert(0,mypath+'/..')
    sys.path.insert(0,mypath+'/../tkui')
#    print "path: {}".format(sys.path)

import pickle
import string
from ivy_compiler import IvyError, ivy_new, ivy_load_file
from ivy_utils import Parameter, set_parameters
import ivy_logic
import proof as pf
import ivy_utils as iu
import ivy_module
#import tactics_api as ta

# mode = Parameter("mode",None)

def usage():
    print "usage: \n  {} <file>.[a2g,ivy,dfy]\n {} <file>.a2g <file.[ivy,dfy]> ".format(sys.argv[0],sys.argv[0])
    sys.exit(1)

def open_read(fn):
    try:
        f = open(fn,'rU')
        return f
    except:
        print "not found: %s" % fn
        sys.exit(1)

def read_params():
    ps = dict()
    args = sys.argv[1:]
    while args and '=' in args[0]:
        thing = string.split(args[0],'=')
        if len(thing) > 2:
            usage()
        ps[thing[0]] = thing[1]
        args = args[1:]
    try:
        set_parameters(ps)
    except IvyError as e:
        print e
        exit(1)
    sys.argv = sys.argv[0:1] + args

# def ivy_init2():
#     if len(sys.argv) < 2 or len(sys.argv) > 2:
#         usage()
#     fn = sys.argv[1]
#     try:
#         session = pf.AnalysisSession(fn)
#         ta.set_context(session)
# # tt.CheckCover.apply.im_func.func_code.co_argcount
#         return session.analysis_state.ivy_ag
#     except IvyError as e:
#         e.filename = fn
#         print repr(e)
#         sys.exit(1)
    
    
def source_file(fn,f,**kwargs):
    try:
        with iu.SourceFile(fn):
            ivy_load_file(f,**kwargs)
            ivy_module.module.name = fn[:fn.rindex('.')]
    except IvyError as e:
        if not hasattr(e,'filename'):
            e.filename = fn
        print str(e)
        sys.exit(1)

def ivy_init(**kwargs):
    read_params()

#    if mode.get() == "ivy2":
#        return ivy_init2()

    if len(sys.argv) < 2 or len(sys.argv) > 3:
        usage()

    files = [(fn,open_read(fn)) for fn in sys.argv[1:]]

    if files[0][0].endswith('.a2g'):
        fn,f = files.pop(0)
        ag = pickle.load(f)
        im.module = ag.domain
        il.sig = ag.domain.sig
        f.close()
    else:
        ag = None

    if files:
        fn,f = files.pop(0)
        if not fn.endswith('.ivy') and not fn.endswith('.dfy'):
            usage()
        skwargs = dict(kwargs)
        skwargs.update(iu.get_default_ui_compile_kwargs())
        source_file(fn,f,**skwargs)

        if ag:
            ag.update_module()
        else: 
            ag = ivy_new()

    return ag

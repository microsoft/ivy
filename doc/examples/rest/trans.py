#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# This script tracnslates requests and responses using a Swagger
# specification in JSON format to ivy.
#
# Usage:
#
#     python extract.py file.json
#

import sys
import os
import json
import collections
import ivy.ivy_utils
from bravado_core.spec import Spec

def read_file(name):
#    try:
        with open(name) as inp:
            return inp.readlines()
#   except:
#        sys.stderr.write('cannot open {} to read\n'.format(name))
#        exit(1)

def match_path(spath,rpath):
    print spath
    parms = dict()
    if len(spath) != len(rpath):
        return None
    for x,y in zip(spath,rpath):
        print x
        print y
        if x.startswith('{'):
            parms[x[1:-1]] = y
        elif x != y:
            return None
    return parms


def main():

    if len(sys.argv) != 2 or not sys.argv[1].endswith('.json'):
        sys.stderr.write('syntax: python extract.py <file>.json\n')
        exit(1)

    inpname = sys.argv[1]

    try:
        with open(inpname) as inp:
            try:
                spec = json.load(inp,object_pairs_hook=collections.OrderedDict)
            except:
                format_error(inpname,'JSON error')
    except:
        sys.stderr.write('cannot open {} to read\n'.format(inpname))
        exit(1)

    req = read_file('req.oapi')
    verb,url,prot = req[0].split()

    things = url.split('?')
    rpath = things[0][1:].split('/')
    parms = dict()
    if len(things) > 1:
        for s in things[1].split('&'):
            p,v = s.split('=')
            parms[p] = v
        
    matched = False
    for path,stuff in spec['paths'].iteritems():
        spath = path[1:].split('/')
        pparms = match_path(spath,rpath)
        if pparms is not None:
            parms.update(pparms)
            matched = True
            break
        
    if not matched:
        sys.stderr.write('cannot match path {}\n'.format(rpath))
        exit(1)

    print list(parms.iteritems())
    
        
    
if __name__ == "__main__":
    main()

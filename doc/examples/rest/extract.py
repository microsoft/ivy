#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# This script extracts some Ivy declarations from a Swagger
# specification in JSON format.
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

def format_error(inpname,err):
    sys.stderr.write('bad format in {}: {}\n'.format(inpname,err))
    exit(1)

name_counter = 0

# Ivy reserved words

ivy_words = {
    'relation',
   'individual',
   'function',
   'axiom',
   'conjecture',
   'schema',
   'instantiate',
   'instance',
   'derived',
   'concept',
   'init',
   'action',
   'method',
   'state',
   'assume',
   'assert',
   'set',
   'null',
   'old',
   'from',
   'update',
   'params',
   'in',
   'match',
   'ensures',
   'requires',
   'modifies',
   'true',
   'false',
   'fresh',
   'module',
   'object',
   'class',
   'type',
   'if',
   'else',
   'local',
   'let',
   'call',
   'entry',
   'macro',
   'interpret',
   'forall',
   'exists',
   'returns',
   'mixin',
   'execute',
   'before',
   'after',
   'isolate',
   'with',
   'export',
   'delegate',
   'import',
   'using',
   'include',
   'progress',
   'rely',
   'mixord',
   'extract',
   'destructor',
   'some',
   'maximizing',
   'minimizing',
   'private',
   'implement',
   'property',
   'while',
   'invariant',
   'struct',
   'definition',
   'ghost',
   'alias',
   'trusted',
   'this',
   'var',
   'attribute',
   'variant',
   'of',
   'scenario',
   'proof',
   'named',
   'fresh',
   'temporal',
   'globally',
   'eventually',
   'decreases',
   'specification',
   'implementation',
   'ensure',
   'require',
   'around',
   'parameter',
   'apply',
   'theorem',
   'showgoals',
   'defergoal',
   'spoil',
   'explicit',
   'thunk',
    'isa',
   'autoinstance',
   'constructor',
}


# Convert swagger name to ivy name
#
# - Initial capitals prefixed with underscore
# - Non-alphanum characters converted to underscore
#

def iname(name):
    name = ''.join(('_' if not x.isalnum() else x) for x in name)
    if name[0].isupper():
        name = '_' + name
    if name in ivy_words:
        name = '_' + name
    return name

def main():
    if len(sys.argv) != 2 or not sys.argv[1].endswith('.json'):
        sys.stderr.write('syntax: python extract.py <file>.json\n')
        exit(1)

    inpname = sys.argv[1]
    outname = inpname[:-4]+'ivy'

    try:
        with open(inpname) as inp:
            try:
                spec = json.load(inp,object_pairs_hook=collections.OrderedDict)
            except:
                format_error(inpname,'JSON error')
    except:
        sys.stderr.write('cannot open {} to read\n'.format(inpname))
        exit(1)

    try:
        out = open(outname,'w')
    except:
        sys.stderr.write('cannot open {} to write\n'.format(outname))
        exit(1)
        
    out.write('#lang ivy1.7\n')
    out.write('\n')
    out.write('# File generated from {}. Do not edit.\n'.format(inpname))
    out.write('\n')
    out.write('type unit\n')
    out.write('type string\n')
    out.write('type integer\n')
    out.write('include collections\n')
    
    
    
    if not isinstance(spec,dict):
        format_error(inpname,'top-level not a dictionary')

    defs = spec["definitions"]

    def follow(ref):
        rf = ref
        if rf.startswith("#/"):
            rf = rf[2:].split('/')
            thing = spec
            for word in rf:
                if word in thing:
                    thing = thing[word]
                else:
                    format_error(inpname,'undefined ref: {}'.format(rf))
            return thing
        format_error(inpname,'undefined ref: {}'.format(rf))
       
    def ref_basename(rf):
        if rf.startswith('#/definitions/'):
            return iname(rf[len('#/definitions/'):])
        else:
            format_error(inpname,'reference {} is not a definition'.format(path,opname,respname))
        
    def_refs = collections.defaultdict(list)

    for name,value in defs.iteritems():
        if "properties" in value:
            props = value["properties"]
            for df in props.values():
                if "$ref" in df:
                    def_refs[name].append(df["$ref"][len('#/definitions/'):])
    order = [(y,x) for x in def_refs.keys() for y in def_refs[x]]
    ordered_names = ivy.ivy_utils.topological_sort(defs.keys(),order)
    defs = collections.OrderedDict((x,defs[x]) for x in ordered_names)
                    
    def get_ref_or_type(prop,name,df):
        if not isinstance(df,dict):
            format_error(inpname,'property {} of entry {} not a dictionary'.format(prop,name))
        if "type" in df:
            ty = df["type"]
            if ty == "array":
                if "items" not in df:
                    format_error(inpname,'property {} of entry {} has no items field'.format(prop,name))
                items = df["items"]
                return "vector[{}]".format(get_ref_or_type(prop,name,items))
            elif ty == "object":
                if "additionalProperties" not in df:
                    format_error(inpname,'property {} of entry {} has no additionalProperties field'.format(prop,name))
                add_props = df["additionalProperties"]
#                global name_counter
#                name = prop+'_sub_'+str(name_counter)
#                name_counter += 1
#                emit_type(name,add_props)
#                ty = name
                return get_ref_or_type(prop,name,add_props)
            return iname(ty)
        elif "$ref" in df:
            rf = df["$ref"]
            return ref_basename(rf)
        else:
            format_error(inpname,'property {} of entry {} has no type field'.format(prop,name))
#        if isinstance(ty,dict):
#            name = prop+'_sub_'+str(idx)
#            emit_type(name,ty)
#            ty = name
    



    for name,value in defs.iteritems():
        if not isinstance(value,dict):
            format_error(inpname,'entry {} not a dictionary'.format(name))
        if "properties" in value:
            items = []
            items.append('object {} = {{\n'.format(iname(name)))
            items.append('    type this = struct {{\n'.format(iname(name)))
            props = value["properties"]
            num_props = len(props)
            if not isinstance(props,dict):
                format_error(inpname,'properties of entry {} not a dictionary'.format(name))
            for idx,(prop,df) in enumerate(props.iteritems()):
                ty = get_ref_or_type(prop,name,df)
                comment = ' # ' + df["description"] if "description" in df else ''
                items.append('        {}_ : {}{} {}\n'.format(iname(prop),ty,',' if idx < num_props-1 else '',comment))
            out.write('\n')
            if "description" in value:
                out.write('# ' + value["description"] + '\n')
            out.write(''.join(items))
            out.write('    }\n')
            out.write('}\n')

    paths = spec["paths"]
        
    path_count = 0
    for path,value in paths.iteritems():
        path_count = path_count + 1
        if not isinstance(value,dict):
            format_error(inpname,'path entry {} not a dictionary'.format(path))
        out.write("\n# path: {}\n".format(path))
        out.write("object path_{} = {{\n".format(path_count))
        for opname,op in value.iteritems():
            if not isinstance(op,dict):
                format_error(inpname,'op entry {} not a dictionary'.format(opname))
            out.write("\n    action {}".format(iname(opname)))
            param_count = 0
            params = op["parameters"]
            if not isinstance(params,list):
                format_error(inpname,'parameters of path {} op {} not a list'.format(path,opname))
            for param in params:
                if not isinstance(param,dict):
                    format_error(inpname,'param of path {} op {} not a dict'.format(path,opname))
                if "$ref" in param:
                    param = follow(param["$ref"])
                if "name" not in param:
                    format_error(inpname,'param of path {} op {} has no name'.format(path,opname))
                paramname = param["name"]
                if "schema" in param:
                    ty = ref_basename(param["schema"]["$ref"])
                elif "type" in param:
                    ty = iname(param["type"])
                else:
                    format_error(inpname,'param {} of path {} op {} has no type'.format(paramname,path,opname))
                if param_count == 0:
                    out.write("(\n")
                out.write('        {}_ : {}'.format(iname(paramname),ty))
                param_count += 1
                if param_count != len(params):
                    out.write(',')
                if "description" in param:
                    out.write(' # {}'.format(param["description"]))
                out.write('\n')
            if len(params) != 0:
                out.write('    )')
            out.write('\n')
            if "responses" not in op:
                format_error(inpname,'path {} op {} has no responses field'.format(path,opname))
            for respname,resp in op["responses"].iteritems():
                if "schema" not in resp:
                    type = "unit"
                else:
                    schema = resp["schema"]
                    if "$ref" in schema:
                        rf = schema["$ref"]
                        ty = ref_basename(rf)
                    else:
                        format_error(inpname,'path {} op {} response {} has no schema ref'.format(path,opname,respname))
                out.write('\n    action {}_response_{}(val:{})\n'.format(iname(opname),respname,ty))
        out.write("}\n")
    
                    
                        
                
                    

            
if __name__ == "__main__":
    main()

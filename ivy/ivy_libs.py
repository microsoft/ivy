#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

#
#  This script allows you to add and remove native libraries to be
#  used by the ivy compiler. The command line syntax is:
#
#  ivy_libs [add,remove] name [prefix] [libdir]
#
#  Here, name is the library name and prefix is the path prefix of
#  the library. If not present, the prefix defaults to lib/name within
#  the ivy main directory. The directory prefix is expected to have the
#  normal layout if a unix libray, that is:
#
#  prefix/lib/lib<name>.so        -- the library shared object file
#  prefix/include/*.h             -- the libaray header files
#
#  However, if the libraries are not found in prefix/lib, the optional
#  libdir argument can be given, specifying the path relative to
#  prefix of the directory containing the libraries.
#
#  Static libraries can also be used.
#
#  Information on added libraries is store in lib/specs in the ivy
#  main directory.
#

import sys
import os
import json

def main():
    if len(sys.argv) < 3 or len(sys.argv) > 5 or sys.argv[1] not in ['add','remove']:
        sys.stderr.write('syntax: python ivy_libs.y [add,remove] name [prefix] [libdir]\n')
        exit(1)

    verb = sys.argv[1]
    name = sys.argv[2]

    libpath = os.path.join(os.path.dirname(os.path.dirname(__file__)),'lib')
    default_prefix = os.path.abspath(os.path.join(libpath,name))
    prefix = sys.argv[3] if len(sys.argv) >= 4 else default_prefix
    libdir = [os.path.join(prefix,sys.argv[4])] if len(sys.argv) >= 5 else []

    print 'Adding library {} at prefix {}.'.format(name,prefix)

    specfilename = os.path.join(libpath,'specs')

    if os.path.isfile(specfilename):
        try:
            with open(specfilename) as inp:
                libs = json.load(inp)
        except:
            sys.stderr.write('bad format in {}\n'.format(specfilename))
            exit(1)
    else:
        libs = []

    libs = [x for x in libs if x[0] != name]
    if verb == 'add':
        libs.append([name,prefix] + libdir)

    with open(specfilename,"w") as out:
        json.dump(libs,out)



if __name__ == "__main__":
    main()

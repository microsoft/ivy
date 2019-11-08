import sys
import os
import platform

def do_cmd(cmd):
    print cmd
    status = os.system(cmd)
    if status:
        exit(1)
    
cwd = os.getcwd()

# if not os.path.exists('submodules/z3'):
#     print "submodules/z3 not found. try 'git submodule update; git submodule update'"
#     exit(1)

# os.chdir('submodules/z3')

# ivydir = os.path.join(cwd,'ivy')


# if platform.system() == 'Windows':
#     cmd = 'python scripts/mk_make.py --python --prefix {} --pypkgdir {}/'.format(cwd,ivydir)
# else:
#     cmd = 'python scripts/mk_make.py -x --python --pypkgdir {}/'.format(ivydir)

# do_cmd(cmd)

# os.chdir('build')

# if platform.system() == 'Windows':
#     do_cmd('nmake')
# else:
#     do_cmd('make -j 4')
#     do_cmd('make install')

# os.chdir(cwd)

if not os.path.exists('ivy/lib'):
    if platform.system() == 'Windows':
        do_cmd('mkdir ivy\\lib')
    else:
        do_cmd('mkdir ivy/lib')

if platform.system() == 'Windows':
    do_cmd('copy submodules\\z3\\src\\api\\*.h ivy\\include')
    do_cmd('copy "submodules\\z3\\src\\api\\c++\\*.h" ivy\\include')
    do_cmd('copy submodules\\z3\\build\\*.dll ivy\\lib')
    do_cmd('copy submodules\\z3\\build\\*.lib ivy\\lib')
    do_cmd('copy submodules\\z3\\build\\*.dll ivy\\z3')
else:
    do_cmd('cp include/*.h ivy/include')
    do_cmd('cp lib/*.so ivy/lib')
    do_cmd('cp lib/*.so ivy/z3')

# if not os.path.exists('submodules/picotls'):
#     print "submodules/picotls not found. try 'git submodule update; git submodule update'"
#     exit(1)

# os.chdir('submodules/picotls')

# do_cmd('git submodule init')
# do_cmd('git submodule update')
# do_cmd('cmake .')
# do_cmd('make')
# do_cmd('cp -a include/*.h include/picotls ../../ivy/include/')
# do_cmd('cp -a *.a ../../ivy/lib/')


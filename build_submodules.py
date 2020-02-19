import sys
import os
import platform

def do_cmd(cmd):
    print cmd
    status = os.system(cmd)
    if status:
        exit(1)
    
def make_dir_exist(dir):
    if not os.path.exists(dir):
        os.mkdir(dir)
    elif not os.path.isdir(dir):
        print "cannot create directory {}".format(dir)
        exit(1)
        

def find_vs():
    import os
    try:
        windir = os.getenv('WINDIR')
        drive = windir[0]
    except:
        drive = 'C'
    for v in ["2019","2017"]:
        for w in ['',' (x86)']:
            dir = '{}:\\Program Files{}\\Microsoft Visual Studio\{}'.format(drive,w,v)
            if os.path.exists(dir):
                for vers in ['Enterprise','Professional','Community']:
                    vers_dir = dir + '\\' + vers
                    if os.path.exists(vers_dir):
                        vcvars = vers_dir + '\\VC\\Auxiliary\\Build\\vcvars64.bat'
                        if os.path.exists(vcvars):
                            return vcvars
    for v in range(15,9,-1):
        for w in ['',' (x86)']:
            dir = '{}:\\Program Files{}\\Microsoft Visual Studio {}.0'.format(drive,w,v)
            vcvars = dir + '\\VC\\vcvars64.bat'
            if os.path.exists(vcvars):
                return vcvars
    print 'Cannot find a suitable version of Visual Studio (require 10.0-15.0 or 2017 or 2019)'

def build_z3():

    cwd = os.getcwd()

    if not os.path.exists('submodules/z3'):
        print "submodules/z3 not found. try 'git submodule update; git submodule update'"
        exit(1)

    os.chdir('submodules/z3')

    ivydir = os.path.join(cwd,'ivy')


    if platform.system() != 'Windows':
        cmd = 'python scripts/mk_make.py --python --prefix {} --pypkgdir {}/'.format(cwd,ivydir)
    else:
        cmd = 'python scripts/mk_make.py -x --python --pypkgdir {}/'.format(ivydir)

    do_cmd(cmd)

    os.chdir('build')

    if platform.system() == 'Windows':
        do_cmd('"{}" & nmake'.format(find_vs()))
    else:
        do_cmd('make -j 4')
        do_cmd('make install')

    os.chdir(cwd)

def install_z3():

    make_dir_exist('ivy/lib')
    make_dir_exist('ivy/z3')

    if platform.system() == 'Windows':
        do_cmd('copy submodules\\z3\\src\\api\\*.h ivy\\include')
        do_cmd('copy "submodules\\z3\\src\\api\\c++\\*.h" ivy\\include')
        do_cmd('copy submodules\\z3\\build\\*.dll ivy\\lib')
        do_cmd('copy submodules\\z3\\build\\*.lib ivy\\lib')
        do_cmd('copy submodules\\z3\\build\\*.dll ivy\\z3')
        do_cmd('copy submodules\\z3\\build\\python\\z3\\*.py ivy\\z3')
    else:
        do_cmd('cp include/*.h ivy/include')
        do_cmd('cp lib/*.so ivy/lib')
        do_cmd('cp lib/*.so ivy/z3')

def build_picotls():
        
    if not os.path.exists('submodules/picotls'):
        print "submodules/picotls not found. try 'git submodule update; git submodule update'"
        exit(1)

    cwd = os.getcwd()

    os.chdir('submodules/picotls')

    do_cmd('git submodule init')
    do_cmd('git submodule update')

    
    if platform.system() == 'Windows':
        do_cmd('"{}" & msbuild /p:OPENSSL64DIR=c:\\OpenSSL-Win64 picotlsvs\\picotls\\picotls.vcxproj'.format(find_vs()))
    else:
        do_cmd('cmake .')
        do_cmd('make')

    os.chdir(cwd)

def install_picotls():
    
    make_dir_exist('ivy/lib')

    cwd = os.getcwd()

    os.chdir('submodules/picotls')

    if platform.system() == 'Windows':
        do_cmd('copy include\\*.h ..\\..\\ivy\\include\\')
        if not os.path.exists('../../ivy/include/picotls'):
            do_cmd('mkdir ..\\..\\ivy\\include\\picotls')
        do_cmd('copy include\\picotls\\*.h ..\\..\\ivy\\include\\picotls\\')
        do_cmd('copy picotlsvs\\picotls\\*.h ..\\..\\ivy\\include\\picotls\\')
        do_cmd('copy picotlsvs\\picotls\\x64\\Debug\\picotls.lib ..\\..\\ivy\\lib\\')
    else:
        do_cmd('cp -a include/*.h include/picotls ../../ivy/include/')
        do_cmd('cp -a *.a ../../ivy/lib/')

    os.chdir(cwd)

def build_v2_compiler():

    cwd = os.getcwd()

    os.chdir('ivy/ivy2/s1')
    do_cmd('ivyc target=repl ivyc_s1.ivy')
    do_cmd('g++ -O2 -o ivyc_s1 ivyc_s1.cpp -pthread')

    os.chdir('../s2')
    do_cmd('IVY_INCLUDE_PATH=../s1/include ../s1/ivyc_s1 ivyc_s2.ivy')
    do_cmd('g++ -I../s1/include -O2 -o ivyc_s2 -std=c++17 ivyc_s2.cpp')

    os.chdir('../s3')
    do_cmd('IVY_INCLUDE_PATH=../s2/include ../s2/ivyc_s2 ivyc_s3.ivy')
    
    os.chdir(cwd)
    
if __name__ == "__main__":
    build_z3()
    install_z3()
    build_picotls()
    install_picotls()
    build_v2_compiler()
    

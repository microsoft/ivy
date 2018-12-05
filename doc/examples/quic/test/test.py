# This script runs a sequence of tests on the picoquicdemo server. 

import pexpect
import os
import sys
import imp
import subprocess
import stats
import re
import time

spawn = pexpect.spawn

servers = [
    ['picoquic',['/home/mcmillan/projects/picoquic','./picoquicdemo']],
    ['quant',['..','/home/mcmillan/projects/quant/Debug/bin/server -d . -c leaf_cert.pem -k leaf_cert.key -p 4443 -t 3600']],
    ['winquic',['..','true']],
]

tests = [
    ['..',
      [
          ['quic_server_test_stream','test_completed'],
          ['quic_server_test_reset_stream','test_completed'],
          ['quic_server_test_connection_close','test_completed'],
          ['quic_server_test_max','test_completed'],
      ]
    ],
]

import sys
def usage():
    print "usage: \n  {} <dir> <iters> <server> [pat]".format(sys.argv[0])
    sys.exit(1)
if len(sys.argv) < 4 or len(sys.argv) > 5 :
    usage()
    exit(1)
dirpath = sys.argv[1]
iters = int(sys.argv[2])
server_name = sys.argv[3]
pat = sys.argv[4] if len(sys.argv) >= 5 else '*'
try:
    patre = re.compile(pat)
except:
    sys.stderr.write('bad regular expression\n')
    exit(1)

try:  
    os.mkdir(dirpath)
except OSError:  
    sys.stderr.write('cannot create directory "{}"\n'.format(dirpath))
    exit(1)

svrd = dict(servers)
if server_name not in svrd:
    sys.stderr.write('unknown server: {}\n'.format(server_name))
    exit(1)
server_dir,server_cmd = svrd[server_name]

print 'server directory: {}'.format(server_dir)
print 'server command: {}'.format(server_cmd)


def open_out(name):
    return open(os.path.join(dirpath,name),"w")

def sleep():
    if server_name == 'winquic':
        st = 20
        print 'sleeping for {}'.format(st)
        time.sleep(st)

class Test(object):
    def __init__(self,dir,args):
        self.dir,self.name,self.res,self.opts = dir,args[0],args[-1],args[1:-1]
    def run(self,seq):
        print '{}/{} ({}) ...'.format(self.dir,self.name,seq)
        status = self.run_expect(seq)
        print 'PASS' if status else 'FAIL'
        return status
    def run_expect(self,seq):
        for pc in self.preprocess_commands():
            print 'executing: {}'.format(pc)
            child = spawn(pc)
            child.logfile = sys.stdout
            child.expect(pexpect.EOF)
            child.close()
            if child.exitstatus != 0:
#            if child.wait() != 0:
                print child.before
                return False
        with open_out(self.name+str(seq)+'.out') as out:
            with open_out(self.name+str(seq)+'.err') as err:
                with open_out(self.name+str(seq)+'.iev') as iev:
                    server = subprocess.Popen(server_cmd.split(),
                                              cwd=server_dir,
                                              stdout=out,
                                              stderr=err)
                    print 'server pid: {}'.format(server.pid)
                    try:
                        ok = self.expect(seq,iev)
                    except KeyboardInterrupt:
                        server.terminate()
                        raise KeyboardInterrupt
                    server.terminate()
                    retcode = server.wait()
                    if retcode != -15 and retcode != 0:  # if not exit on SIGTERM...
                        iev.write('server_return_code({})\n'.format(retcode))
                        print "server return code: {}".format(retcode)
                        return False
                    return ok
            
    def expect(self,seq,iev):
        command = self.command(seq)
        print command
        oldcwd = os.getcwd()
        os.chdir(self.dir)
        proc = subprocess.Popen(command,stdout=iev,shell=True)
        os.chdir(oldcwd)
        try:
            retcode = proc.wait()
        except KeyboardInterrupt:
            print 'terminating client process {}'.format(proc.pid)
            proc.terminate()
            raise KeyboardInterrupt
        if retcode == 124:
            print 'timeout'
            iev.write('timeout\n')
            sleep()
            return False
        if retcode != 0:
            iev.write('ivy_return_code({})\n'.format(retcode))
            print 'client return code: {}'.format(retcode)
        sleep()
        return retcode == 0
#             oldcwd = os.getcwd()
#             os.chdir(self.dir)
#             child = spawn(command)
#             os.chdir(oldcwd)
#             child.logfile = iev
#             try:
#                 child.expect(self.res,timeout=None)
#                 return True
#             except pexpect.EOF:
# #                print child.before
#                 return False
#             except pexpect.exceptions.TIMEOUT:
#                 print 'timeout'
#                 return False
    def preprocess_commands(self):
        return []
        
class IvyTest(Test):
    def command(self,seq):
        import platform
        return 'timeout 100 ./build/{} seed={}'.format(self.name,seq)

all_tests = []

def get_tests(cls,arr):
    for checkd in arr:
        dir,checkl = checkd
        for check in checkl:
            all_tests.append(cls(dir,check))

    
try:
    get_tests(IvyTest,tests)

    num_failures = 0
    for test in all_tests:
        if not patre.match(test.name):
            continue
        for seq in range(0,iters):
            status = test.run(seq)
            if not status:
                num_failures += 1
        with open_out(test.name+'.dat') as out:
            save = os.getcwd()
            os.chdir(dirpath)
            stats.doit(test.name,out)
            os.chdir(save)
    if num_failures:
        print 'error: {} tests(s) failed'.format(num_failures)
    else:
        print 'OK'
except KeyboardInterrupt:
    print 'terminated'

# for checkd in checks:
#     dir,checkl = checkd
#     for check in checkl:
#         name,res = check
#         print '{}/{} ...'.format(dir,name)
#         child = pexpect.spawn('timeout 100 ivy_check {}.ivy'.format(name))
#         try:
#             child.expect(res)
#             print 'PASS'
#         except pexpect.EOF:
#             print child.before
#             print 'FAIL'
        


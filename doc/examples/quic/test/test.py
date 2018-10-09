# This script runs a sequence of tests on the picoquicdemo server. 

import pexpect
import os
import sys
import imp
import subprocess

spawn = pexpect.spawn

tests = [
    ['..',
      [
          ['quic_server_test','test_completed'],
      ]
    ],
]



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
        with open(self.name+str(seq)+'.out', "w") as out:
            with open(self.name+str(seq)+'.err', "w") as err:
                with open(self.name+str(seq)+'.iev', "w") as iev:
                    server = subprocess.Popen(["./picoquicdemo"],
                                              cwd='/home/mcmillan/projects/picoquic',
                                              stdout=out,
                                              stderr=err)
                    try:
                        ok = self.expect(seq,iev)
                    except KeyboardInterrupt:
                        server.terminate()
                        raise KeyboardInterrupt
                    server.terminate()
                    retcode = server.wait()
                    if retcode != -15:  # if not exit on SIGTERM...
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
            proc.terminate()
            raise KeyboardInterrupt
        if retcode == 124:
            print 'timeout'
            iev.write('timeout\n')
            return False
        if retcode != 0:
            iev.write('ivy_return_code({})\n'.format(retcode))
            print 'client return code: {}'.format(retcode)
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
        return 'timeout 100 ./{} seed={}'.format(self.name,seq)

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
        for seq in range(0,10):
            status = test.run(seq)
            if not status:
                num_failures += 1
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
        


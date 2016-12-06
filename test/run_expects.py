import pexpect
import os
import sys

checks = [
    ['../doc/examples',
     [
      ['account2','OK'],
      ['account3','OK'],
      ['account','OK'],
      ['array1','error: Some assertions are not checked'],
      ['arrayset2','OK'],
      ['arrayset3','OK'],
      ['arrayset','OK'],
      ['client_server_example','error: safety failed'],
      ['counter_example','error: safety failed'],
      ['coveragefail','error: Some assertions are not checked'],
      ['helloworld','OK'],
      ['interference2','OK'],
      ['interference3','OK'],
      ['interference4','OK'],
      ['interference','interference.ivy: line 30: error: Call out to right_player.intf_ping'],
      ['leader_election_ring2','error: Some assertions are not checked'],
      ['leader_election_ring_btw','error: Some assertions are not checked'],
      ['leader_election_ring','error: Some assertions are not checked'],
      ['leader_election_ring_repl','OK'],
      ['leader_election_ring_udp2','OK'],
      ['leader_election_ring_udp','OK'],
      ['lesstrivnet','OK'],
      ['modparam_example','OK'],
      ['object_example','OK'],
      ['paraminit2','OK'],
      ['paraminit3','OK'],
      ['paraminit','OK'],
      ['pingpongclock','OK'],
      ['pingpong','OK'],
      ['po_example','OK'],
      ['timeout_test','OK'],
      ['trivnet','OK'],
      ['udp_test2','OK'],
      ['udp_test','OK'],
      ]
     ],
    ['../doc/examples/testing',
      [
          ['pingpong','trusted=true','OK'],
          ['interference','trusted=true','interference.ivy: line 30: error: Call out to right_player.intf_ping[implement] may have visible effect on left_player.ball'],
          ['coveragefail','trusted=true','coveragefail.ivy: line 20: error: assertion is not checked'],
      ]
    ],
]

tests = [
    ['../doc/examples/testing',
      [
          ['token_ring','isolate=iso_n','test_completed'],
#          ['trivnet','test_completed'],
#          ['pingpong','isolate=iso_l','test_completed'],
#          ['pingpong_bad','isolate=iso_l','pingpong_bad.ivy: line 15: : assertion failed'],
#          ['pingpong','isolate=iso_r','test_completed'],
#          ['leader_election_ring','isolate=iso_p','test_completed'],
#          ['leader_election_ring','isolate=iso_n','test_completed'],
#          ['leader_election_ring','isolate=iso_t test_iters=5','test_completed'],
#          ['token_ring','isolate=iso_p','test_completed'],
#          ['token_ring','isolate=iso_t','test_completed'],
#          ['token_ring_buggy','isolate=iso_t','trans_buggy.ivy: line 26: : assertion failed'],
      ]
     ]
]


class Test(object):
    def __init__(self,dir,args):
        self.dir,self.name,self.res,self.opts = dir,args[0],args[-1],args[1:-1]
    def run(self):
        oldcwd = os.getcwd()
        os.chdir(self.dir)
        print '{}/{} ...'.format(self.dir,self.name)
        status = self.run_expect()
        print 'PASS' if status else 'FAIL'
        os.chdir(oldcwd)
        return status
    def run_expect(self):
        for pc in self.preprocess_commands():
            print 'executing: {}'.format(pc)
            child = pexpect.spawn(pc)
            child.logfile = sys.stdout
            child.expect(pexpect.EOF)
            if child.wait() != 0:
                print child.before
                return False
        child = pexpect.spawn(self.command())
#        child.logfile = sys.stdout
        try:
            child.expect(self.res)
            return True
        except pexpect.EOF:
            print child.before
            return False
    def preprocess_commands(self):
        return []
        
class IvyCheck(Test):
    def command(self):
        return 'timeout 100 ivy_check {}.ivy'.format(self.name)

class IvyTest(Test):
    def command(self):
        return './'+self.name

    def preprocess_commands(self):
        return ['ivy_to_cpp target=test build=true '+' '.join(self.opts) + ' '+self.name+'.ivy']

all_tests = []

def get_tests(cls,arr):
    for checkd in arr:
        dir,checkl = checkd
        for check in checkl:
            all_tests.append(cls(dir,check))

#get_tests(IvyCheck,checks)
get_tests(IvyTest,tests)
        
num_failures = 0
for test in all_tests:
    status = test.run()
    if not status:
        num_failures += 1
if num_failures:
    print 'error: {} tests(s) failed'.format(num_failures)
else:
    print 'OK'

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
        


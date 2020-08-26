import pexpect
import os
import sys
import imp
import re

import platform

if platform.system() == 'Windows':
    import pexpect.popen_spawn
    spawn = pexpect.popen_spawn.PopenSpawn
else:
    spawn = pexpect.spawn

checks = [
    ['.',
      [
          ['fba','OK'],
          ['interpdef1','interpdef1.ivy: line 5: error: definition of interpreted symbol <'],
          ['whileexists1','OK'],
          ['whilesome1','OK'],
          ['whilesome2','OK'],
          ['fundef1','error: Variable Y:t occurs free on right-hand side of definition'],
          ['fundef2','error: Variable X:t occurs twice on left-hand side of definition'],
          ['strat1','error: The verification condition is not in'],
          ['skolem1','error: failed checks: 1'],
          ['ifstar1','OK'],
          ['frag1','OK'],
          ['frag2','An interpreted symbol is applied to a universally quantified variable'],
          ['frag3','OK'],
          ['frag4','An interpreted symbol is applied to a universally quantified variable'],
          ['frag5','OK'],
          ['frag6','OK'],
          ['frag7','An interpreted symbol is applied to a universally quantified variable'],
          ['frag8','An interpreted symbol is applied to a universally quantified variable'],
          ['frag9','An interpreted symbol is applied to a universally quantified variable'],
          ['frag10','An interpreted symbol is applied to a universally quantified variable'],
          ['frag11','OK'],
          ['frag12','OK'],
          ['frag13','OK'],
          ['frag14','An interpreted symbol is applied to a universally quantified variable'],
          ['frag15','An interpreted symbol is applied to a universally quantified variable'],
          ['frag16','OK'],
          ['frag17','OK'],
          ['frag18','OK'],
          ['frag19','OK'],
          ['oddeven','complete=fo','OK'],
          ['oddeven2','complete=fo','OK'],
          ['oddeven3','OK'],
          ['oddeven4','OK'],
          ['learning_switch1','trace=true','learning_switch1.ivy: line 37:'],
          ['ded1','OK'],
      ]
    ],
    ['../doc/examples/testing',
      [
          ['pingpong','trusted=true','OK'],
          ['interference','trusted=true','error: Call out to right_player.intf_ping'],
          ['coveragefail','trusted=true','error: assertion is not checked'],
      ]
    ],
    ['../doc/examples',
     [
      ['account2','OK'],
      ['account3','OK'],
      ['account','OK'],
      ['array1','error: Some assertions are not checked'],
      ['arrayset2','OK'],
      ['arrayset3','OK'],
      ['arrayset','OK'],
      ['client_server_example','OK'],
      ['counter_example','counter_example.ivy: line 54: guarantee ... FAIL'],
      ['coveragefail','error: Some assertions are not checked'],
      ['helloworld','OK'],
      ['interference2','OK'],
      ['interference3','OK'],
      ['interference4','OK'],
      ['interference','error: Call out to right_player.intf_ping'],
      ['leader_election_ring2','error: Some assertions are not checked'],
      ['leader_election_ring_btw','leader_election_ring_btw.ivy: line 118: guarantee ... FAIL'],
      ['leader_election_ring','leader_election_ring.ivy: line 114: guarantee ... FAIL'],
      ['leader_election_ring_repl','OK'],
      ['leader_election_ring_udp2','OK'],
      ['leader_election_ring_udp','OK'],
      ['lesstrivnet','OK'],
      ['modparam_example','OK'],
      ['object_example','OK'],
      ['paraminit2','OK'],
      ['paraminit3','OK'],
      ['paraminit','isolate=iso_foo','OK'],
      ['pingpongclock','OK'],
      ['pingpong','OK'],
      ['po_example','OK'],
      ['timeout_test','OK'],
      ['trivnet','OK'],
      ['udp_test2','OK'],
      ['udp_test','OK'],
      ['list_reverse','OK'],
      ['indexset','OK'],
      ['number_theory','OK'],
      ]
     ],
    ['../examples/ivy',
     [
      ['flash3','OK'],
     ]
    ],
]

tests = [
    ['../doc/examples/testing',
      [
         ['trivnet','test_completed'],
         ['pingpong','isolate=iso_l','test_completed'],
         ['pingpong_bad','isolate=iso_l','assertion failed'],
         ['pingpong','isolate=iso_r','test_completed'],
         ['leader_election_ring','isolate=iso_p','test_completed'],
         ['leader_election_ring','isolate=iso_n','test_completed'],
         ['leader_election_ring','isolate=iso_t test_iters=5','test_completed'],
         ['token_ring','isolate=iso_p','test_completed'],
         ['token_ring','isolate=iso_t','test_completed'],
         ['token_ring_buggy','isolate=iso_t test_runs=10','assertion failed'],
         ['token_ring','isolate=iso_n','test_completed'],
         ['token_ring','isolate=iso_pt','test_completed'],
      ]
     ]
]

repls = [
    ['../doc/examples',
      [
         ['leader_election_ring_repl','isolate=iso_impl','leader_election_ring_repl_iso_impl_expect'],
         ['helloworld',None],
         ['account',None],
         ['account2',None],
         ['account3',None],
         ['leader_election_ring_repl',None],
         ['udp_test','isolate=iso_impl',None],
         ['udp_test2','isolate=iso_impl',None],
         ['leader_election_ring_udp','isolate=iso_impl',None],
         ['timeout_test',None],
         ['leader_election_ring_udp2','isolate=iso_impl',None],
         ['paraminit','isolate=iso_foo',None],
         ['paraminit3','isolate=iso_foo',None],
      ]
     ]
]

to_cpps = [
    ['../doc/examples',
      [
         ['leader_election_ring_repl_err','target=repl','isolate=iso_impl','error: relevant axiom asgn.injectivity not enforced'],
         ['leader_election_ring_repl_err2','target=repl','isolate=iso_impl','error: No implementation for action node.get_next'],
         ['leader_election_ring_udp2_warn','target=repl','isolate=iso_impl','warning: action sec.timeout is implicitly exported'],
         ['paraminit','target=repl','error: cannot compile initial constraint on "foo.bit" because type t is large. suggest using "after init"'],
         ['paraminit2','target=repl','isolate=iso_foo','initial condition depends on stripped parameter'],
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
            child = spawn(pc)
            child.logfile = sys.stdout
            child.expect(pexpect.EOF)
            child.close()
            if child.exitstatus != 0:
#            if child.wait() != 0:
                print child.before
                return False
        return self.expect()
    def expect(self):
        command = self.command()
        print command
        child = spawn(command)
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
        import platform
        if platform.system() == 'Windows':
            return 'ivy_check {} {}.ivy'.format(' '.join(self.opts),self.name)
        return 'timeout 100 ivy_check {} {}.ivy'.format(' '.join(self.opts),self.name)

class IvyTest(Test):
    def command(self):
        import platform
        return './build/'+self.name

    def preprocess_commands(self):
        make_directory_exist('build')
        return ['ivy_to_cpp target=test build=true '+' '.join(self.opts) + ' '+self.name+'.ivy']

class IvyRepl(Test):
    def command(self):
        return './build/'+self.name
    def preprocess_commands(self):
        make_directory_exist('build')
        return ['ivy_to_cpp target=repl build=true '+' '.join(self.opts) + ' '+self.name+'.ivy']
    def expect(self):
        print 'wd:{}'.format(os.getcwd())
        modname = self.res if self.res != None else (self.name+'_expect')
        mod = imp.load_source(modname,modname+'.py')
        return mod.run('build/'+self.name,self.opts,self.res)
    
class IvyToCpp(Test):
    def command(self):
        res = 'ivy_to_cpp ' + ' '.join(self.opts) + ' '+self.name+'.ivy'
        print 'compiling: {}'.format(res)
        return res

def make_directory_exist(dir):
    if not os.path.exists(dir):
        os.mkdir(dir)

all_tests = []

allpat = re.compile('.*')
test_type = allpat
test_dir = allpat
test_name = allpat

for arg in sys.argv[1:]:
    vals = arg.split('=')
    if len(vals) != 2:
        usage()
    name,val = vals
    if name == 'type':
        test_type = re.compile(val)
    elif name == 'dir':
        test_dir = re.compile(val)
    elif name == 'name':
        test_name = re.compile(val)
    else:
        usage()

def usage():
    print """usage:
    {} [option...]
options:
    type=<test type pattern>
    dir=<test directory pattern>
    name=<test name pattern>
""".format(sys.argv[0])
    sys.exit(1)

def get_tests(cls,arr):
    for checkd in arr:
        dir,checkl = checkd
        if test_dir.match(dir):
            for check in checkl:
                if test_name.match(check[0]):
                    all_tests.append(cls(dir,check))

if test_type.match('check'):
    get_tests(IvyCheck,checks)
if test_type.match('test'):
    get_tests(IvyTest,tests)
if test_type.match('repl'):
    get_tests(IvyRepl,repls)
if test_type.match('to_cpp'):
    get_tests(IvyToCpp,to_cpps)

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
        


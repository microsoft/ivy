import pexpect
import os

checks = [
    ['../doc/examples',
     [
      ['account2','error: safety failed'],
      ['account3','error: safety failed'],
      ['account','OK'],
      ['array1','error: Some assertions are not checked'],
      ['arrayset2','OK'],
      ['arrayset3','OK'],
      ['arrayset','OK'],
      ['client_server_example','OK'],
      ['counter_example','OK'],
      ['coveragefail','OK'],
      ['helloworld','OK'],
      ['interference2','OK'],
      ['interference3','OK'],
      ['interference4','OK'],
      ['interference','OK'],
      ['leader_election_ring2','OK'],
      ['leader_election_ring_btw','OK'],
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
     ]
    ]

for checkd in checks:
    dir,checkl = checkd
    oldcwd = os.getcwd()
    os.chdir(dir)
    for check in checkl:
        name,res = check
        print '{}/{} ...'.format(dir,name)
        child = pexpect.spawn('timeout 100 ivy_check {}.ivy'.format(name))
        try:
            child.expect(res)
            print 'PASS'
        except pexpect.EOF:
            print child.before
            print 'FAIL'
        
    os.chdir(oldcwd)


import pexpect
import sys

def run(name,opts,res):
    child = pexpect.spawn('./{}'.format(name))
    child.logfile = sys.stdout
    try:
        child.expect('>')
        child.sendline('foo.send(0,1,2)')
        child.expect(r'< foo.recv\(1,2\)')
        child.sendline('foo.send(1,0,3)')
        child.expect(r'foo.recv\(0,3\)')
        return True
    except pexpect.EOF:
        print child.before
        return False

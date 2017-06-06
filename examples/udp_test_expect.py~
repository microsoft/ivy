import pexpect
import sys

def run(name,opts,res):
    child = pexpect.spawn('./{}'.format(name))
    child.logfile = sys.stdout
    try:
        child.expect('>')
        child.sendline('app.async(0)')
        child.expect(r'< trans.send\(1,1\)')
        child.expect('>')
        child.sendline('trans.recv(1,1)')
        child.expect(r'trans.send\(0,1\)')
        child.expect('>')
        child.sendline('trans.recv(0,1)')
        child.expect(r'serv.elect\(0\)')
        child.expect('>')
        child.sendline('trans.recv(1,0)')
        child.expect(r'serv.elect\(1\)')
        return True
    except pexpect.EOF:
        print child.before
        return False

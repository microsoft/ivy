import pexpect
import sys

def run(name,opts,res):
    child = pexpect.spawn('./{} 0'.format(name))
    child.logfile = sys.stdout
    try:
        child.expect('>')
        child.sendline('foo.get_bit')
        child.expect(r'= 1')
    except pexpect.EOF:
        print child.before
        return False
    finally:
        child.close()
    child = pexpect.spawn('./{} 1'.format(name))
    child.logfile = sys.stdout
    try:
        child.expect('>')
        child.sendline('foo.get_bit')
        child.expect(r'= 0')
        return True
    except pexpect.EOF:
        print child.before
        return False
    finally:
        child.close()
        

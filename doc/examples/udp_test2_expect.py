import pexpect
import sys

def run(name,opts,res):
    child = [pexpect.spawn('./{} {}'.format(name,idx)) for idx in range(2)]
    for idx in range(2):
        child[idx].logfile = sys.stdout
    try:
        child[0].expect('>')
        child[0].sendline('foo.send(1,2)')
        child[1].expect(r'< foo.recv\(2\)')
        child[1].sendline('foo.send(0,3)')
        child[0].expect(r'foo.recv\(3\)')
        child[0].sendline('foo.send(0,4)')
        child[0].expect(r'< foo.recv\(4\)')
        return True
    except pexpect.EOF:
        print child.before
        return False
    finally:
        for idx in range(2):
            child[idx].close()

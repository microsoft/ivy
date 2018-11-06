import pexpect
import sys

def run(name,opts,res):
    child = [pexpect.spawn('./{} {}'.format(name,idx)) for idx in range(2)]
    for idx in range(2):
        child[idx].logfile = sys.stdout
    try:
        # child[0].expect('>')
        child[0].expect(r'< serv.elect')
        return True
    except pexpect.EOF:
        print child.before
        return False
    finally:
        for idx in range(2):
            child[idx].close()

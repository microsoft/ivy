import pexpect
import sys

def run(name,opts,res):
    child = pexpect.spawn('./{}'.format(name))
    child.logfile = sys.stdout
    try:
        child.expect('>')
        child.sendline('account.deposit(5)')
        child.expect('>')
        child.sendline('ask_and_check_balance')
        child.expect('ask')
        child.expect(r'\?')
        child.sendline('4')
        child.expect('1')
        child.expect('>')
        child.sendline('ask_and_check_balance')
        child.expect('ask')
        child.expect(r'\?')
        child.sendline('6')
        child.expect('0')
        return True
    except pexpect.EOF:
        print child.before
        return False

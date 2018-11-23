import ivy_lexer
import sys

f = open(sys.argv[1],'r')
ivy_lexer.lexer.input(f.read())

count = 0

while True:
    tok = ivy_lexer.lexer.token()
    if not tok: 
        break      # No more input
    count += 1

print count


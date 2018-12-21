import ivy.ivy_ev_parser as ev
import ivy.ivy_utils as iu
import os

counts = [
    ['frame.ack','frame.ack.handle'],
    ['frame.stream','frame.stream.handle'],
    ['frame.crypto','frame.crypto.handle'],
    ['frame.rst_stream','frame.rst_stream.handle'],
    ['frame.connection_close','frame.connection_close.handle'],
    ['packet_event','packet_event'],
    ['app_send_event','app_send_event'],
    ['tls_recv_event','tls_recv_event'],
    ['max stream offset','frame.stream.handle({offset:$1})','maxz','%($1)s'],
    ['max stream data','frame.stream.handle({offset:$1,length:$2})','maxz','%($1)s + %($2)s'],
    ['ivy error','ivy_return_code'],
    ['server error','server_return_code'],
    ['server_ack','show_frame(*,*,*,*,{frame.ack:*})'],
    ['server_stream','show_frame(*,*,*,*,{frame.stream:*})'],
]

def count(x):
    return len(x)

def maxz(x):
    return 0 if len(x) == 0 else max(x)

def doit(fbase,out):

    import chardet # $ pip install chardet

    out.write('file,' + ','.join(l[0] for l in counts) + '\n')

    files = sorted([n for n in os.listdir('.') if n.startswith(fbase) and n.endswith('.iev')])
    
    for fn in files:
    
        try:
            f = open(fn,'r')
        except:
            print "not found: %s" % fn
            sys.exit(1)

        with iu.ErrorPrinter():
            with iu.SourceFile(fn):
                s = f.read()
                evs = ev.parse(s)


        vals = []
        for line in counts:
            name,patstring = line[:2]
            op = line[2] if len(line) >= 3 else 'count'
            expr = line[3] if len(line) >= 4 else 'None'
            pats = ev.parse(patstring)
            res = ev.bind(ev.EventGen()(evs),pats)
            col = [eval(expr % b) for e,b in res]
            s =  op + '(' + str(col) + ')'
            sum = eval(s)
            vals.append(sum)
        out.write(fn + ',' + ','.join(str(v) for v in vals) + '\n')

def main():
    import sys
    def usage():
        print "usage: \n  {} <file>.iev ".format(sys.argv[0])
        sys.exit(1)
    if len(sys.argv) != 2:
        usage()
        exit(1)
    fbase = sys.argv[1]
    doit(fbase,sys.stdout)
    
    
if __name__ == '__main__':
    main()


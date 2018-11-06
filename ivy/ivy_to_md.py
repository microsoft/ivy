import sys
import xml
import xml.etree.ElementTree as ET
import StringIO

def main():

    if len(sys.argv) != 2 or not sys.argv[1].endswith('.ivy'):
        print 'usage: {} <file>.ivy'.format(sys.argv[0])

    inpname = sys.argv[1]
    outname = inpname[:-3]+'md'

    try: 
        with open(inpname) as f:
            content = f.readlines()
    except IOError:
        print 'file {} not found'.format(inpname)
        exit(1)

    try:
        outf = open(outname,'w')
    except:
        print 'could not open {} for output'.format(outname)


    last_was_comment = True
    with outf:
        for line in content[1:]:
            if not line.strip():
                outf.write('\n')
            elif line.strip().startswith('#') and not line.strip().startswith('#-'):
                if not last_was_comment:
                    outf.write('```\n')
                comment = '#'.join(line.split('#')[1:])
                if comment.startswith(' '):
                    comment = comment[1:]
                outf.write(comment)
                last_was_comment = True
            else:
                if last_was_comment:
                    outf.write('```\n')
#                outf.write('    '+line)
                outf.write(line)
                last_was_comment = False
        if not last_was_comment:
            outf.write('```\n')

import os
import csv
import numpy
from tabulate import tabulate

def main():
    import sys
    def usage():
        print "usage: \n  {} <file>.dat [field...]".format(sys.argv[0])
        sys.exit(1)
    if len(sys.argv) < 2:
        usage()
        exit(1)
    fn = sys.argv[1]
    fields = sys.argv[2:]
    import chardet # $ pip install chardet

    with open(fn) as csv_file:
        csv_reader = csv.DictReader(csv_file, delimiter=',')
        line_count = 0
        rows = []
        for row in csv_reader:
            for f in fields:
                if f not in row:
                    sys.stderr.write('unknown field "{}"\n'.format(f))
                    exit(1)
            rows.append([row[f] for f in fields])
        print tabulate(rows,tablefmt="fancy_grid",headers=fields)


if __name__ == '__main__':
    main()


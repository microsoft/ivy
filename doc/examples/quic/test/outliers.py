import os
import csv
import numpy
from tabulate import tabulate

def main():
    import sys
    def usage():
        print "usage: \n  {} <file>.dat".format(sys.argv[0])
        sys.exit(1)
    if len(sys.argv) != 2:
        usage()
        exit(1)
    fn = sys.argv[1]
    import chardet # $ pip install chardet

    with open(fn) as csv_file:
        csv_reader = csv.reader(csv_file, delimiter=',')
        line_count = 0
        rows = []
        for row in csv_reader:
            if line_count == 0:
                labels = row
            else:
                rows.append(row)
            line_count += 1

        cands = []
        files = [row[0] for row in rows]
        for colidx in range(1,len(labels)):
            label = labels[colidx]
            col = [float(row[colidx]) for row in rows]
            sigma = numpy.std(col)
            mu = numpy.average(col)
            if sigma != 0.0:
                for f,v in zip(files,col):
                    cands.append((abs(float(v)-mu)/sigma,f,label,v,mu,sigma))
        fun = lambda x: x[0]
        scands = sorted(cands,key=fun)
        data = [cand[1:] for cand in scands[-3:]]
        print tabulate(data,tablefmt="fancy_grid")


if __name__ == '__main__':
    main()


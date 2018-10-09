import os
import csv

def plot(fn,column,col):
    import numpy as np
    import matplotlib.pyplot as plt

    # the histogram of the data
    n, bins, patches = plt.hist(col, 'auto', density=1, facecolor='g', alpha=0.75)


    plt.xlabel(column)
    plt.ylabel('Probability')
    plt.title('Histogram of {}'.format(column))
#    plt.axis([40, 160, 0, 0.03])
    plt.grid(True)
    plt.show()

def main():
    import sys
    def usage():
        print "usage: \n  {} <file>.dat column ".format(sys.argv[0])
        sys.exit(1)
    if len(sys.argv) != 3:
        usage()
        exit(1)
    fn = sys.argv[1]
    column = sys.argv[2]
    import chardet # $ pip install chardet

    with open(fn) as csv_file:
        csv_reader = csv.DictReader(csv_file, delimiter=',')
        line_count = 0
        col = []
        for row in csv_reader:
            if line_count != 0:
                col.append(row[column])
            line_count += 1

        plot(fn,column,col)



if __name__ == '__main__':
    main()

        

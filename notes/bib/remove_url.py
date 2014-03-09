#!/usr/bin/python
import sys
import re
import fileinput

def inplace_change(filename, old_string):
    ifile = open(filename,'r')
    text = ifile.read()
    ifile.close()
    newtext = re.sub(old_string,"",text)
    ofile = open(filename,'w')
    ofile.write(newtext)
    # for line in fileinput.input(filename, inplace=True):
    #     print re.sub(old_string,"",line),

if __name__ == "__main__":
    #import doctest
    #doctest.testmod()
    inplace_change(str(sys.argv[1]),r"(?s)annote = \{.*?\},\n")
    inplace_change(str(sys.argv[1]),r"url = \{.*?\}\n")
    inplace_change(str(sys.argv[1]),r"(?s)url = \{.*?\},\n")


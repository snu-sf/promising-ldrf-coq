import sys, re

if len(sys.argv) != 2:
    print ("Usage: " + sys.argv[0] + " infile")
    sys.exit(1)

arg_infile = sys.argv[1]

with open(arg_infile, 'r') as infile:
    for line in infile:
        match = re.search('^\[.*\]\s+(\S+)\s+\((\S+)\s+ms\)$', line)
        if match:
            test = match.group(1)
            time = match.group(2)
            print (test + "\t" + time)

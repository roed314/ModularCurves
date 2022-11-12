#! /usr/local/bin/sage -python

import os
import sys
# This need sto be run outside the shell, before the script
# os.system("ulimit -n 4096")
from lmfdb import db
label = sys.argv[1]
gens = db.gps_gl2zhat_test.lucky({'label' : label}, 'generators')
os.system("mkdir -p input_data")
genstr = ', '.join([str(g)[1:-1] for g in gens])
f = open("input_data/" + label, 'w')
f.write(genstr)


#!/usr/bin/env python3

import os
import argparse
import subprocess

parser = argparse.ArgumentParser("Parallelize computation of pictures for modular curves")
parser.add_argument("num_jobs", type=int, help="number of processes to use")
args = parser.parse_args()

os.makedirs("picture_stdout", exist_ok=True)
n = args.num_jobs
# Unfortunately we don't get bash expansion so can't use {0..n-1}
# n should be small enough that we can just do it inline
assert n < 500
subprocess.run('parallel -j%s "sage make_modular_curve_picture.sage {1} %s >> picture_stdout/{1}" ::: %s' % (n, n, " ".join(str(c) for c in range(n))), shell=True)

#!/usr/bin/env python3

import os
import argparse
import subprocess

parser = argparse.ArgumentParser("Parallelize computation of pictures for modular curves")
parser.add_argument("num_jobs", type=int, help="number of processes to use")
args = parser.parse_args()

os.makedirs("picture_stdout", exist_ok=True)
n = args.num_jobs
subprocess.run('parallel -j%s "sage make_modular_curve_picture.sage {1} %s >> picture_stdout/{1}" ::: {0..%s}' % (n, n, n-1), shell=True)

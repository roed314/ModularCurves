#!/usr/bin/env python3

import os
opj = os.path.join
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
subprocess.run('parallel -j%s "sage make_modular_curve_picture.sage {1} %s >> picture_stdout/{1} 2>&1" ::: %s' % (n, n, " ".join(str(c) for c in range(n))), shell=True)
t = 0
for fname in os.listdir("picture_stdout"):
    fullname = opj("picture_stdout", fname)
    with open(fullname) as F:
        for line in F:
            if line.startswith("Total time "):
                t += float(line.strip()[11:])
            else:
                print(f"Error found in {fullname}")
print(f"Total time {t}")
with open("modcurve_pictures.txt", "w") as Fout:
    _ = Fout.write("psl2label|image\ntext|text\n\n")
    for fname in os.listdir("pictures"):
        with open(opj("pictures", fname)) as F:
            _ = Fout.write(F.read())

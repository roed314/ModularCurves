#!/usr/bin/env python3

import os
import argparse
import subprocess

opj = os.path.join
ope = os.path.exists
parser = argparse.ArgumentParser("Dispatch to appropriate magma script")
parser.add_argument("job", type=int, help="job number")
parser.add_argument("--verbose", action="store_true")

# These folders are needed by the scripts to be called below
os.makedirs("ishyp", exist_ok=True)
os.makedirs("timings", exist_ok=True)
os.makedirs("stdout", exist_ok=True)

args = parser.parse_args()
job = args.job - 1 # shift from 1-based to 0-based indexing
with open("todo.txt") as F:
    L = F.read().strip().split("\n")
    label = L[job]

def get_hyperellipticity(label, verbose):
    verb = "verbose:= " if verbose else ""
    subprocess.run('parallel --timeout 600 "magma -b label:={1} %sGetPrecHyp.m >> stdout/{1} 2>&1" ::: %s' % (verb, label), shell=True)

def collate_data(label):
    with open("output", "a") as Fout:
        for code, folder in [
                ("Y", "ishyp"),
                ("T", "timings"),
                ("E", "stdout")]:
            fname = opj(folder, label)
            if ope(fname):
                with open(fname) as F:
                    for line in F:
                        if line[-1] != "\n":
                            line += "\n"
                        _ = Fout.write(f"{code}{label}|{line}")

get_hyperellipticity(label, args.verbose)
collate_data(label)

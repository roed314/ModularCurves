#!/usr/bin/env python3

import os
import shutil
import argparse

parser = argparse.ArgumentParser("Clean up from a test run of cloud_start.py")
parser.add_argument("saven", help="number where output should be moved")
parser.add_argument("--savecan", action="store_true", help="whether to keep the canonical_models folder")

args = parser.parse_args()

prefix = "mid" + args.saven + "_"
tomove = ["ghyp_models", "graphviz_out", "output", "plane_models", "rats", "cusps", "stdout", "timings"]
if not args.savecan:
    tomove.extend(["canonical_models", "gonality"])
# Don't move graphviz_in/, jinvs/ or cod/ since they generally are input-only
# Don't move hypstdout/ or ishyp/ since they're from a precomputation step
for x in tomove:
    if os.path.exists(x):
        shutil.move(x, prefix + x)

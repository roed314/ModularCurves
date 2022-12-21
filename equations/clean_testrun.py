#!/usr/bin/env python3

import shutil
import argparse

parser = argparse.ArgumentParser("Clean up from a test run of cloud_start.py")
parser.add_argument("saven", help="number where output should be moved")
parser.add_argument("savecan", action="store_true", help="whether to keep the canonical_models folder")

args = parser.parser_args()

prefix = "mid" + args.saven + "_"
tomove = ["ghyp_models", "graphviz_out", "output", "plane_models", "rats", "stdout", "timings"]
if not args.savecan:
    tomove.extend(["canonical_models", "jinvs"])
for x in tomove:
    shutil.move(x, prefix + x)

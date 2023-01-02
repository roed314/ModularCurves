#!/usr/bin/env python3


import os
import argparse
import subprocess

opj = os.path.join
ope = os.path.exists

parser.add_argument("label", help="label of modular curve")
os.makedirs("graphviz_out", exist_ok=True)
args = parser.parse_args()

# We use graphviz to lay out the displayed lattice
infile = opj("graphviz_in", label)
if ope(infile):
    outfile = opj("graphviz_out", label)
    subprocess.run(["dot", "-Tplain", "-o", outfile, infile], check=True)
    xcoord = {}
    with open(outfile) as F:
        maxx = 0
        minx = 10000
        for line in F:
            if line.startswith("graph"):
                scale = float(line.split()[2])
            elif line.startswith("node"):
                pieces = line.split()
                short_label = pieces[1].replace('"', '')
                diagram_x = int(round(10000 * float(pieces[2]) / scale))
                xcoord[short_label] = diagram_x
    with open(outfile, "w") as F:
        lattice_labels, lattice_x = zip(*xcoord.items())
        _ = F.write("{%s}|{%s}\n" % (",".join(lattice_labels), ",".join(str(c) for c in lattice_x)))

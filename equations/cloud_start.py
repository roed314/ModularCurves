#!/usr/bin/env python3

#### Data Generation Process ####
# Generate gps_gl2zhat_coarse and gps_gl2zhat_fine (Drew)
# Add adelic_reductions to ec_galrep (Drew)
# Use upload/cloud_prep.py to create equations/input_data/ (generators), equations/graphviz_in/ (lattice), equations/jinvs/ (rational points) and upload/picture_labels.txt and the tarball
# In the cloud (or wherever you want to unpack the tarball), run cloud_start.py, producing data for inclusion in gp2_gl2zhat_fine (gonality bounds, lattice_x, lattice_labels), modcurve_models (all columns), modcurve_maps (all columns), modcurve_points (coordinates, isolated)
# On a server (since you're going to be creating pictures in parallel), run make_modular_curve_pictures.py
# On a server, run cloud_collect.py, which will propogate gonalities, create the copy_from files for modcurve_points, modcurve_models, modcurve_maps and an update_from_file file gps_gl2zhat_coarse

# TODO
# - Update verbosity (two levels: one for debugging and another for reporting timing info)
# - Do group identification
# - Update descriptions of labels (RSZB and LMFDB)
# - Base change for CM points (duplicated points in rats/).  Need to throw away points of lower degree?

# Copied into the home directory for running
# Consistent segfault on 22.180.6.b.1

import os
import argparse
import subprocess
from time import time

opj = os.path.join
ope = os.path.exists
parser = argparse.ArgumentParser("Dispatch to appropriate magma script")
parser.add_argument("job", type=int, help="job number")

# These folders are needed by the scripts to be called below
os.makedirs("canonical_models", exist_ok=True)
os.makedirs("plane_models", exist_ok=True)
os.makedirs("ghyp_models", exist_ok=True)
os.makedirs("rats", exist_ok=True)
os.makedirs("gonality", exist_ok=True)
os.makedirs("graphviz_out", exist_ok=True)
os.makedirs("timings", exist_ok=True)
os.makedirs("stdout", exist_ok=True)


# These functions use subprocess to actually compute the various needed quantities

args = parser.parse_args()
job = args.job - 1 # shift from 1-based to 0-based indexing
with open("todo.txt") as F:
    L = F.read().strip().split("\n")
    label = L[job]

def get_lattice_coords(label):
    # We use graphviz to lay out the displayed lattice
    infile = opj("graphviz_in", label)
    if not ope(infile):
        return
    outfile = opj("graphviz_out", label)
    with open(opj("timings", label), "a") as F:
        _ = F.write("Starting lattice layout\n")
        t0 = time()
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
    with open(opj("timings", label), "a") as F:
        _ = F.write(f"Finished lattice layout in {time() - t0}\n")

def get_canonical_model(label):
    # Also produces a first stab at a plane model
    g = int(label.split(".")[2])
    if g <= 24:
        subprocess.run('parallel --timeout 3600 "magma -b label:={1} GetModelLMFDB.m >> stdout/{1} 2>&1" ::: %s' % label, shell=True)
    return ope(opj("canonical_models", label))

def get_plane_and_gonality(label):
    # Runs the script to compute gonality bounds and a better plane model
    # Returns true whether the curve is geometrically hyperelliptic
    subprocess.run('parallel --timeout 1200 "magma -b label:={1} GetPlaneAndGonality.m >> stdout/{1} 2>&1" ::: %s' % label, shell=True)
    gon = opj("gonality", label)
    with open(opj("canonical_models", label)) as F:
        model_type = F.read().strip().split("|")[-1]
        return model_type == "-1"

def get_ghyperelliptic_model(label):
    for prec in [100, 200, 300, 400, 600, 1200]:
        if ope(opj("ghyp_models", label)):
            break
        subprocess.run('parallel --timeout 600 "magma -b label:={1} prec:=%s GetGHyperellipticModel.m >> stdout/{1} 2>&1" ::: %s' % (prec, label), shell=True)

def get_rational_coordinates(label):
    subprocess.run('parallel --timeout 1200 "magma -b label:={1} GetRationalCoordinates.m >> stdout/{1} 2>&1" ::: %s' % label, shell=True)

def collate_data(label):
    with open("output", "a") as Fout:
        for code, folder in [
                ("C", "canonical_models"),
                ("P", "plane_models"),
                ("H", "ghyp_models"),
                ("R", "rats"),
                ("G", "gonality"),
                ("L", "graphviz_out"),
                ("T", "timings"),
                ("E", "stdout")]:
            fname = opj(folder, label)
            if ope(fname):
                with open(fname) as F:
                    for line in F:
                        if line[-1] != "\n":
                            line += "\n"
                        _ = Fout.write(f"{code}{label}|{line}")

#if get_canonical_model(label):
if ope("canonical_models/" + label):
    if get_plane_and_gonality(label):
        get_ghyperelliptic_model(label)
    get_rational_coordinates(label)
get_lattice_coords(label)
collate_data(label)

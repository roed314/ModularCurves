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

# Copied into the home directory for running

import os
import argparse
import subprocess

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
    return xcoord

def get_canonical_model(label):
    # Also produces a first stab at a plane model
    subprocess.run('parallel --timeout 3600 "magma -b label:={1} GetModelLMFDB.m >> stdout/{1} 2>&1" ::: %s' % label, shell=True)
    return ope(opj("canonical_models", label))

def get_plane_and_gonality(label):
    # Runs the script to compute gonality bounds and a better plane model
    # Returns true whether the curve is geometrically hyperelliptic and not hyperelliptic
    subprocess.run('parallel --timeout 1200 "magma -b label:={1} GetPlaneAndGonality.m >> stdout/{1} 2>&1" ::: %s' % label, shell=True)
    gon = opj("gonality", label)
    if ope(gon):
        with open(gon) as F:
            bounds = F.read().strip().split(",")
            return bounds[0] == bounds[1] == "4" and bounds[2] == bounds[3] == "2"

def get_ghyperelliptic_model(label):
    for prec in [100, 200, 300, 400, 600, 1200]:
        subprocess.run('parallel --timeout 600 magma -b label:={1} prec:=%s GetGHyperellipticModel.m ::: %s' % (prec, label), shell=True)
        if ope(opj("ghyp_models", label)):
            break

def get_rational_coordinates(label):
    subprocess.run('parallel --timeout 1200 "magma -b label:={1} GetRationalCoordinates.m >> stdout/{1} 2>&1" ::: %s' % label, shell=True)

def collate_data(label):
    xcoord = get_lattice_coords(label)
    with open(opj("canonical_models", label)) as F:
        return tuple(F.read().strip().replace("{","").replace("}","").split("|"))

if get_canonical_model(label):
    if get_plane_and_gonality(label):
        get_ghyperelliptic_model(label)
    get_rational_coordinates(label)
#collate_data(label)

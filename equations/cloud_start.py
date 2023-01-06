#!/usr/bin/env python3

#### Data Generation Process ####
# Generate gps_gl2zhat_coarse and gps_gl2zhat_fine (Drew)
# Add adelic_reductions to ec_galrep (Drew)
# Use upload/cloud_prep.py to create equations/input_data/ (generators), equations/graphviz_in/ (lattice), equations/jinvs/ (rational points) and upload/picture_labels.txt and the tarball
# In the cloud (or wherever you want to unpack the tarball), run cloud_start.py, producing data for inclusion in gp2_gl2zhat_fine (gonality bounds, lattice_x, lattice_labels), modcurve_models (all columns), modcurve_maps (all columns), modcurve_points (coordinates, isolated)
# On a server (since you're going to be creating pictures in parallel), run make_modular_curve_pictures.py AND MAKE_LATTICES.PY
# On a server, run cloud_collect.py, which will propogate gonalities, create the copy_from files for modcurve_points, modcurve_models, modcurve_maps and an update_from_file file gps_gl2zhat_coarse

# TODO
# - Do group identification
# - Update descriptions of labels (RSZB and LMFDB)
# - Base change for CM points (duplicated points in rats/).  Need to throw away points of lower degree?

# ** Computation changes **
# Code for making tarball
# Create a mechanism for redoing failed labels
# Need to move rational point and cusp data from output file to folders after cod and before second deployment
# Finish splitting off lattice computation, remove test for g<=24 below, update todo list generation
# Store number of points per j-inv in modcurve_points
# Optimized models

# ** Checks **
# check on other todos in compute_lattice_x
# Check lifting of rational points (and cusps?) on relative j-maps
# Indexes for modcurve_models, modcurve_modelmaps
# Make sure Elabel is the minimal one
# Work around magma bug in pulling back j-invariants (18.81.3.a.1, 20.90.3.e.1) by checking that the image under the j-map is correct
# Figure out why we're computing plane models when the canonical model is already a plane model (18.81.3.a.1)
# Add leading_coefficients to model isomorphisms and relative j-maps
# Lattice: https://red.lmfdb.xyz/ModularCurve/Q/4.12.0.a.1/ doesn't go to X(1) since it contains X(2), but maybe it should
# Bug: On https://red.lmfdb.xyz/ModularCurve/Q/16.384.21.k.2/ it claims that there are two cusps of degree 4, but magma code didn't find them (looks like a problem with the magma code since 1+1+1+1+2+2+8+8+8 isn't 24)
# Correct the precision needed for relative j-map
# Create picture database
# Cusps that didn't get coordinates aren't included in modcurve_points
# Parallelize polredabs

# ** Front-end changes **
# Fun diagram: https://red.lmfdb.xyz/ModularCurve/Q/16.192.5.bu.1/
# Update display of relative j-maps to account for leading coefficients differently
# Highlight this curve initially in lattice
# Use - instead of -1 in factoring negative integers (utils)
# Have j-invariant infinity in modcurve_points for cusps
# Display a-invariant list when fine model not in db
# Add index to modcurve_points and make sortable (low)
# Use select to set sort order when doing one-per-jinv (low)
# Knowl for model type that's a double cover of conic
# Display fields using pretty names (and i rather than a for coordinates and j-invariant in Q(i))

import os
import argparse
import subprocess

opj = os.path.join
ope = os.path.exists
parser = argparse.ArgumentParser("Dispatch to appropriate magma script")
parser.add_argument("job", type=int, help="job number")
parser.add_argument("--verbose", action="store_true")
parser.add_argument("--cod", action="store_true")

# These folders are needed by the scripts to be called below
os.makedirs("canonical_models", exist_ok=True)
os.makedirs("plane_models", exist_ok=True)
os.makedirs("ghyp_models", exist_ok=True)
os.makedirs("rats", exist_ok=True)
os.makedirs("jcusps", exist_ok=True)
os.makedirs("jfacs", exist_ok=True)
os.makedirs("cusps", exist_ok=True)
os.makedirs("gonality", exist_ok=True)
os.makedirs("graphviz_out", exist_ok=True)
os.makedirs("timings", exist_ok=True)
os.makedirs("stdout", exist_ok=True)


# These functions use subprocess to actually compute the various needed quantities

args = parser.parse_args()
job = args.job - 1 # shift from 1-based to 0-based indexing
if args.cod:
    todo = "codtodo.txt"
else:
    todo = "todo.txt"
with open(todo) as F:
    L = F.read().strip().split("\n")
    label = L[job]
    genus = int(label.split(".")[2])

def get_lattice_coords(label):
    # We use graphviz to lay out the displayed lattice
    infile = opj("graphviz_in", label)
    if not ope(infile):
        return
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

def get_canonical_model(label, verbose):
    # Also produces a first stab at a plane model
    if genus <= 24:
        verb = "verbose:= " if verbose else ""
        subprocess.run('parallel --timeout 900 "magma -b label:={1} %sGetModelLMFDB.m >> stdout/{1} 2>&1" ::: %s' % (verb, label), shell=True)

def get_plane_and_gonality(label, verbose):
    # Runs the script to compute gonality bounds and a better plane model
    # Returns true whether the curve is geometrically hyperelliptic
    g = int(label.split(".")[2])
    verb = "verbose:= " if verbose else ""
    subprocess.run('parallel --timeout 600 "magma -b label:={1} %sGetPlaneAndGonality.m >> stdout/{1} 2>&1" ::: %s' % (verb, label), shell=True)

def get_ghyperelliptic_model(label, verbose):
    with open(opj("canonical_models", label)) as F:
        model_type = F.read().strip().split("|")[-1]
    if genus >= 3 and model_type == "8":
        verb = "verbose:= " if verbose else ""
        for prec in [100, 300, 600]:
            if ope(opj("ghyp_models", label)):
                break
            subprocess.run('parallel --timeout 600 "magma -b label:={1} %sprec:=%s GetGHyperellipticModel.m >> stdout/{1} 2>&1" ::: %s' % (verb, prec, label), shell=True)

def get_plane_model(label, verbose):
    # Attempts to contruct a plane model via projection from rational points
    verb = "verbose:= " if verbose else ""
    subprocess.run('parallel --timeout 300 "magma -b label:={1} %sGetPlaneModel.m >> stdout/{1} 2>&1" ::: %s' % (verb, label), shell=True)

def get_rational_coordinates(label, verbose):
    verb = "verbose:= " if verbose else ""
    subprocess.run('parallel --timeout 300 "magma -b label:={1} %sGetRationalCoordinates.m >> stdout/{1} 2>&1" ::: %s' % (verb, label), shell=True)

def get_cusp_coordinates(label, verbose):
    verb = "verbose:= " if verbose else ""
    subprocess.run('parallel --timeout 60 "magma -b label:={1} %sGetCuspCoordinates.m >> stdout/{1} 2>&1" ::: %s' % (verb, label), shell=True)

def get_jfactorization(label, verbose):
    verb = "verbose:= " if verbose else ""
    subprocess.run('parallel --timeout 60 "magma -b label:={1} %sGetJFactorization.m >> stdout/{1} 2>&1" ::: %s' % (verb, label), shell=True)

def collate_data(label):
    with open("output", "a") as Fout:
        for code, folder in [
                ("C", "canonical_models"),
                ("P", "plane_models"),
                ("H", "ghyp_models"),
                ("R", "rats"),
                ("J", "jcusps"),
                ("F", "jfacs"),
                ("U", "cusps"),
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

get_canonical_model(label, args.verbose)
if ope(opj("canonical_models", label)):
    if genus != 0:
        get_plane_and_gonality(label, args.verbose)
        get_ghyperelliptic_model(label, args.verbose)
        if ope(opj("jcusps", label)): # These need a j-map or cusps
            get_plane_model(label, args.verbose)
            get_rational_coordinates(label, args.verbose)
            get_cusp_coordinates(label, args.verbose)
if ope(opj("jcusps", label)): # For P1 we don't write down a canonical model, so this is outside the above if statement
    get_jfactorization(label, args.verbose)
get_lattice_coords(label)
collate_data(label)

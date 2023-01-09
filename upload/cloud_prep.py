#!/usr/bin/env -S sage -python

import os
import sys
import shutil
import re
import time
import subprocess
import argparse
from collections import defaultdict
from sage.all import ZZ, QQ, PolynomialRing, MatrixSpace, EllipticCurve, NumberField, cached_function, flatten, walltime, cputime, DiGraph
from sage.combinat.posets.posets import FinitePoset
from sage.databases.cremona import class_to_int
from sage.misc.prandom import random, randint
from cloud_common import rational_poset_query, lattice_query, model_query, rat_query, psl2_query, get_lattice_poset, get_rational_poset, index_iterator, to_coarse_label, inbox, pslbox, load_gl2zhat_rational_data, dbtable, load_ecq_data, load_ecnf_data, load_points_files


opj = os.path.join
ope = os.path.exists
sys.path.append(os.path.expanduser(opj("~", "lmfdb")))
from lmfdb import db

parser = argparse.ArgumentParser("Create a tarball for cloud computation")
parser.add_argument("stage", type=int, help="stage of compututation (1=initial setup, 2=after getting cod data back")
parser.add_argument("--hypprob", type=float, help="probablity that each potentially hyperelliptic curve is tested")
parser.add_argument("--hyplevel", type=int, help="for stage 0.  if negative, only include curves with level less than or equal to absolute value.  If positive, only include curves with larger level")
parser.add_argument("--codprob", type=float, help="probability that each valid codomain is included")
parser.add_argument("--domprob", type=float, help="probablity that domains of relative j-maps are included, conditional on their codomain being included")
parser.add_argument("--absprob", type=float, help="probability that non-canonical curves are included")

parser.add_argument("--norelj", action="store_true", help="disable computation of relj_codomains")
parser.add_argument("--nopsl2", action="store_true", help="disable creation of psl2_input_data and picture_labels.txt")
parser.add_argument("--nographviz", action="store_true", help="disable creation of graphviz input folder")
parser.add_argument("--norats", action="store_true", help="disable creation of rational points data")

parser.add_argument("--redomissing", help="determine which canonical models didn't finish and create a new tarball with just them as a todo.  Pass in the codes to be checked for (C is a common choice, for canonical model)")
parser.add_argument("--combinemissing", help="An output file to merge into output{stage}")

args = parser.parse_args()

def prep(stage):
    if args.combinemissing:
        cur_ofile = f"output{stage}"
        gap_ofile = args.combinemissing
        codes = args.redomissing
        if codes is None: codes = "C"
        done = set()
        with open(cur_ofile) as F:
            for line in F:
                if line and line[0] in codes:
                    label = line[1:].split("|")[0]
                    done.add(label)
        fixed = set()
        with open(gap_ofile) as F:
            for line in F:
                if line and line[0] in codes:
                    label = line[1:].split("|")[0]
                    fixed.add(label)
        tmpfile = "tmp" + "%04x"%(randint(0,65535))
        with open(tmpfile, "w") as Fout:
            with open(cur_ofile) as F:
                for line in F:
                    label = line[1:].split("|")[0]
                    if label not in fixed:
                        _ = Fout.write(line)
            with open(gap_ofile) as F:
                for line in F:
                    label = line[1:].split("|")[0]
                    if label in fixed:
                        _ = Fout.write(line)
        os.rename(cur_ofile, "combinemissing" + "%04x"%(randint(0,65535)) + cur_ofile)
        os.rename(tmpfile, cur_ofile)
        return
    elif args.redomissing:
        codes = args.redomissing
        if stage == 1:
            todofile = "codtodo.txt"
        elif stage == 2:
            todofile = "nexttodo.txt"
        else:
            raise ValueError(stage)
        shutil.copy(todofile, "redomissing" + "%04x"%(randint(0,65535)) + todofile)
        with open(f"output{stage}") as F:
            done = set()
            for line in F:
                if line and line[0] in codes:
                    label = line[1:].split("|")[0]
                    done.add(label)
            todo = set()
            with open(todofile) as F:
                for line in F:
                    label = line.strip()
                    todo.add(label)
            undone = todo.difference(done)
        with open(todofile, "w") as F:
            for label in undone:
                _ = F.write(label + "\n")
    elif stage == -1:
        make_input_data()
        return
    elif stage == 0:
        make_input_data()
        prep_hyperelliptic()
        #run_hyperelliptic()
    elif stage == 1:
        extract_stage0()
        if not args.norelj:
            get_relj_codomains()
        if not args.nopsl2:
            make_psl2_input_data()
        make_g2_lookup_data() # if folder exists, does nothing
        if not args.nographviz:
            make_graphviz_files()
        if not args.nopsl2:
            make_picture_input()
        make_gonality_files()
        if not args.norats:
            prepare_rational_points()
    elif stage == 2:
        extract_stage1()
        update_relj_codomains()
    elif stage == 3:
        extract_stage1_2()
        return
    make_tarball(stage=stage)

def make_input_data():
    """
    Create the input folder that stores generators
    """
    print("Creating input data...", end="")
    t0 = time.time()
    sys.stdout.flush()
    folder = opj("..", "equations", "input_data")
    os.makedirs(folder, exist_ok=True)
    for rec in db.gps_gl2zhat_coarse.search(model_query(), ["label", "generators"]):
        with open(opj(folder, rec["label"]), "w") as F:
            _ = F.write(",".join(str(c) for c in flatten(rec["generators"])))
    print(f" done in {time.time() - t0:.2f}s")

def extract_stage0():
    print("Extracting output from stage 0...", end="")
    t0 = time.time()
    sys.stdout.flush()
    ifold = opj("..", "equations", "ishyp")
    os.makedirs(ifold, exist_ok=True)
    with open("output0") as F:
        for line in F:
            if not line: continue
            label, rest = line[1:].split("|", 1)
            if line[0] == "Y":
                with open(opj(ifold, label), "w") as Fout:
                    _ = Fout.write(rest.strip())
    print(f" done in {time.time() - t0:.2f}s")

def extract_stage1():
    """
    Extract contents of stage 1 output file (stored in ROOT/upload/output1) for running stage 2
    """
    rfold = opj("..", "equations", "rats")
    cfold = opj("..", "equations", "canonical_models")
    os.makedirs(rfold, exist_ok=True)
    os.makedirs(cfold, exist_ok=True)
    # We need to delete any current contents of these directories (which may have been created by running locally), since the append mode below will screw things up for stage 2.
    rdata = os.listdir(rfold)
    if rdata:
        delete = input("There are files in equations/rats; delete [Y/n]? ")
        if delete and delete.lower()[0] != "y":
            print("Exiting")
            sys.exit(1)
        for label in rdata:
            os.unlink(opj(rfold, label))
    cdata = os.listdir(cfold)
    if cdata:
        delete = input("There are files in equations/canonical_models; delete [Y/n]? ")
        if delete and delete.lower()[0] != "y":
            print("Exiting")
            sys.exit(1)
        for label in cdata:
            os.unlink(opj(cfold, label))
    with open("output1") as F:
        for line in F:
            if not line: continue
            label, rest = line[1:].split("|", 1)
            if line[0] == "R":
                folder = rfold
            elif line[0] == "C":
                folder = cfold
            else:
                continue
            with open(opj(folder, label), "a") as Fout:
                _ = Fout.write(rest)

def make_tarball(stage=1):
    """
    Create a tarball with all the files needed to run on another server
    """
    if stage == 0:
        shutil.copy("hyptodo.txt", opj("..", "equations", "todo.txt"))
    elif stage == 1:
        shutil.copy("codtodo.txt", opj("..", "equations", "todo.txt"))
    else:
        shutil.copy("nexttodo.txt", opj("..", "equations", "todo.txt"))
    os.chdir(opj("..", "equations"))
    with open("todo.txt") as F:
        for n, line in enumerate(F, 1):
            pass
    print("Creating tarball...", end="")
    t0 = time.time()
    sys.stdout.flush()
    include = [
        "equations.spec",
        "CanonicalRing.m",
        "CuspOrbits.m",
        "findjmap.m",
        "io.m",
        "plane_model.m",
        "precision.m",
        "ProcessModel.m",
        "Genus0Common.m",
        "Genus0CongSubs.m",
        "Genus0Models.m",
        "hyperelliptic/load.m",
        "hyperelliptic/code.m",
        "GetCuspCoordinates.m",
        "GetGHyperellipticModel.m",
        "GetJFactorization.m",
        "GetModelLMFDB.m",
        "GetPlaneAndGonality.m",
        "GetPlaneModel.m",
        "GetPrecHyp.m",
        "GetRationalCoordinates.m",

        "cloud_start.py",
        "todo.txt",

        "CHIMP",
        "Gm-Reduce",
        "OpenImage",

        "cod",
        "gonality",
        "graphviz_in",
        "input_data",
        #"jinvs",
        "g2invs",
    ]
    if stage == 0:
        include.extend(["cloud_hypstart.py"])
    elif stage == 1:
        include.extend(["ishyp"])
    if stage == 2:
        include.extend(["ishyp", "rats", "canonical_models"])
    subprocess.run(f"tar -cf ../upload/stage{stage}_{n}.tar " + " ".join(include), shell=True)
    print(f" done in {time.time() - t0:.2f}s")
    if stage == 0:
        print("Next steps:")
        print(f"  Copy stage0_{n}.tar to a server or cloud disk image, extract and run cloud_hypstart.py in parallel")
    elif stage == 1:
        print("Next steps:")
        print(f"  Copy stage1_{n}.tar to a server or cloud disk image, extract and run cloud_start.py in parallel")
        print("  ./make_pictures.py NUM_PROC")
        print("    (then db.modcurve_pictures.reload('modcurve_pictures.txt'))")
        print("  cd ../equations && parallel -jNUM_PROC -a lattodo.txt ./get_lattice_coords.py {1}")
    else:
        print("Next steps:")
        print(f"  Copy stage2_{n}.tar to a server or cloud disk image, extract and run cloud_start.py in parallel")
    os.chdir(opj("..", "upload"))

#########################################################
# Functions for preparing for computing relative j-maps #
#########################################################

def prep_hyperelliptic():
    # Need to figure out which modular curves are on the "border" between canonical models and not (g=0,1 or hyperelliptic)
    print("Preparing for hyperelliptic computation...", end="")
    t0 = time.time()
    sys.stdout.flush()
    with open(opj("hyptodo.txt"), "w") as F:
        query = model_query()
        query["genus"] = {"$gte":3, "$lte":17}
        for rec in db.gps_gl2zhat_coarse.search(query, ["label", "level", "qbar_gonality_bounds"]):
            if args.hyplevel is not None:
                if args.hyplevel < 0 and rec["level"] > abs(args.hyplevel):
                    continue
                if args.hyplevel > 0 and rec["level"] <= args.hyplevel:
                    continue
            if inbox(rec["label"]) and rec["qbar_gonality_bounds"][0] == 2 and rec["qbar_gonality_bounds"][1] > 2 and not ope(opj("..", "ishyp", rec["label"])):
                if args.hypprob is not None:
                    r = random()
                    if r > args.hypprob:
                        continue
                # possibly hyperelliptic
                _ = F.write(rec["label"] + "\n")
    print(f" done in {time.time() - t0:.2f}s")

def run_hyperelliptic():
    """
    Determines which modular curves that might be hyperelliptic actually are, since this is required for determining codomains for relative j-maps
    """
    with open("hyptodo.txt") as F:
        n = 0
        for n, line in enumerate(F, 1):
            pass
    os.chdir(opj("..", "equations"))
    if n > 0:
        curn = len(os.listdir("ishyp"))
        folder = os.path.abspath("ishyp")
        print(f"Determining hyperellipticity (done when {curn + n} files exist in {folder})")
        t0 = time.time()
        subprocess.run('parallel -j80 -a ../upload/hyptodo.txt "magma -b label:={1} GetPrecHyp.m"', shell=True)
        print(f"Done determining hyperellipticity in {time.time() - t0:.2f}s")
    os.chdir(opj("..", "upload"))

def get_relj_codomains():
    # We extracted the results of stage0 into the ishyp folder
    output_folder, hyp_lookup, parents_conj, P, H, M, X1, index_sort_key = get_relj_codomain_input()
    print("Determining codomains...", end="")
    sys.stdout.flush()
    t0 = time.time()
    cod = {}
    for x in index_iterator(P, X1):
        label = P._vertex_to_element(x)
        N, i, g, a, n = label.split(".")
        if int(g) >= 3 and inbox(label) and hyp_lookup.get(label) is False:
            tmp = [(label, M((1,0,0,1)))]
            for y in H.neighbors_in(x):
                ylabel = P._vertex_to_element(y)
                if ylabel in cod:
                    ybest, yconj = cod[ylabel]
                    conj = parents_conj[label, ylabel] * yconj
                    tmp.append((ybest, conj))
            cod[label] = min(tmp, key=index_sort_key)
    print(f"Codomains selected in {time.time() - t0:.2f}s")
    t0 = time.time()
    cods = defaultdict(int)
    for label, (codomain, conj) in cod.items():
        if label != codomain:
            # We track the maximum index used for a given codomain, since that affects the precision needed for computing the relative j-map.
            cods[codomain] = max(cods[codomain], int(label.split(".")[1]) // int(codomain.split(".")[1]))
            with open(opj(output_folder, label), "w") as F:
                _ = F.write(f"{codomain}|{','.join(str(c) for c in conj.list())}")
    # Now cods contains the maximum relative index of anything mapping to the given codomain
    skipped = set()
    with open("codtodo.txt", "w") as Ftodo:
        for c, maxind in cods.items():
            if args.codprob is not None:
                r = random()
                if r > args.codprob:
                    skipped.add(c)
                    continue
            _ = Ftodo.write(c + "\n")
            with open(opj(output_folder, c), "w") as F:
                _ = F.write(f"{c}|{maxind}")
    with open("nexttodo.txt", "w") as Fnext:
        with open("lattodo.txt", "w") as Flat:
            for label in db.gps_gl2zhat_coarse.search(lattice_query(), "label"):
                if label not in cods:
                    if inbox(label):
                        codomain, conj = cod.get(label, (None, None))
                        if codomain is None:
                            # Uses absolute j-map
                            if args.absprob is not None:
                                r = random()
                                if r > args.absprob:
                                    continue
                        elif codomain in skipped:
                            continue
                        elif args.domprob is not None:
                            r = random()
                            if r > args.domprob:
                                continue
                        _ = Fnext.write(label + "\n")
                    else:
                        if args.absprob is not None:
                            r = random()
                            if r > args.absprob:
                                continue
                        _ = Flat.write(label + "\n")
    print(f"Todo files printed in {time.time() - t0:.2f}s")

def get_relj_codomain_input():
    print("Loading hyperelliptic data...", end="")
    t0 = time.time()
    sys.stdout.flush()
    output_folder = opj("..", "equations", "cod")
    os.makedirs(output_folder, exist_ok=True)
    hyp_lookup = {}
    for label in os.listdir(opj("..", "equations", "ishyp")):
        with open(opj("..", "equations", "ishyp", label)) as F:
            hyp, prec, reldeg = F.read().strip().split("|")
            hyp_lookup[label] = (hyp == "t")
    print(f" done in {time.time() - t0:.2f}s")
    print("Loading conjugators...", end="")
    sys.stdout.flush()
    t0 = time.time()
    parents_conj = {}
    M = MatrixSpace(ZZ, 2)
    query = model_query()
    query["genus"] = {"$gte": 3}
    for rec in db.gps_gl2zhat_coarse.search(query, ["label", "parents", "parents_conj", "qbar_gonality_bounds"]):
        if not inbox(rec["label"]):
            continue
        gon = rec["qbar_gonality_bounds"]
        if gon == [2, 2]:
            hyp_lookup[rec["label"]] = True
        elif gon[0] > 2:
            hyp_lookup[rec["label"]] = False
        for plabel, pconj in zip(rec["parents"], rec["parents_conj"]):
            parents_conj[rec["label"], plabel] = M(pconj)
    print(f" done in {time.time() - t0:.2f}s")
    P = get_lattice_poset()
    H = P._hasse_diagram
    X1 = P._element_to_vertex("1.1.0.a.1")
    def index_sort_key(pair):
        N, i, g, a, n = pair[0].split(".")
        return (int(i), int(N), int(g), class_to_int(a), int(n))
    return output_folder, hyp_lookup, parents_conj, P, H, M, X1, index_sort_key

def update_relj_codomains():
    # Stage 0 extract into ishyp, and stage1 (hopefully) computed canonical models for a bunch of codomains.
    # Some may have failed, but there was flexibility in choosing them (We aimed to optimize the index, but having the model is obviously a lot more important)
    output_folder, hyp_lookup, parents_conj, P, H, M, X1, index_sort_key = get_relj_codomain_input()
    print("Determining codomains...", end="")
    sys.stdout.flush()
    t0 = time.time()
    models_available = {}
    for label in os.listdir(opj("..", "equations", "canonical_models")):
        codfile = opj("..", "cod", label)
        if ope(codfile): # should always exist....
            with open(codfile) as F:
                codomain, data = F.read().strip().split("|")
            if codomain == label and data.isdigit(): # if we've only finished stage1, this should be true
                N, i, g, a, n = label.split(".")
                # maximum index this codomain supports
                models_available[label] = int(data) * int(i)
    prior_cod = {}
    for label in os.listdir(opj("..", "cod")):
        if label in models_available:
            continue
        codfile = opj("..", "cod", label)
        with open(codfile) as F:
            codomain, data = F.read().strip().split("|")
        if codomain != label:
            prior_cod[label] = codomain
    current_cod = {}
    cod = defaultdict(dict)
    # Unlike in get_relj_codomains, we may be restricted in the index allowed by a codomain
    # So here the values of cod are a list of options
    def collapse(tmp, ind):
        # For each maximum index supported, keep only the minimum index_sort_key
        D = defaultdict(list)
        for pair in tmp:
            D[models_available[pair[0]]].append(pair)
        for maxind, pairs in D.items():
            # We can omit options that don't support this index, since everything downstream will have even larger index
            if ind <= maxind:
                yield min(pairs, key=index_sort_key)
    for x in index_iterator(P, X1):
        label = P._vertex_to_element(x)
        N, i, g, a, n = label.split(".")
        i, g = int(i), int(g)
        if g >= 3 and inbox(label) and hyp_lookup.get(label) is False:
            if label in models_available:
                tmp = [(label, M((1,0,0,1)))]
            else:
                tmp = []
            for y in H.neighbors_in(x):
                ylabel = P._vertex_to_element(y)
                for ybest, yconj in cod.get(ylabel, []):
                    conj = parents_conj[label, ylabel] * yconj
                    tmp.append((ybest, conj))
            tmp = list(collapse(tmp, i))
            if tmp:
                cod[label] = tmp # includes multiple options at different indexes
                current_cod[label] = min(tmp, key=index_sort_key) # best option at this index
            else:
                print(f"Warning: no valid codomain for {label}")
                # We need to delete the file in cod/ since it won't get overwritten below
                os.unlink(opj(output_folder, label))
    print(f"Codomains selected in {time.time() - t0:.2f}s")
    ndiff = len([label for label, prior in prior_cod.items() if prior != current_cod.get(label, (None,None))[0]])
    print(f"{ndiff} codomains selected differently from stage 1")
    t0 = time.time()
    # We don't support codprob, absprob or domprob here
    if ope("nexttodo.txt"):
        n = 0
        while ope(f"stage1_nexttodo{n}.txt"):
            n += 1
        os.rename("codtodo.txt", "stage1_nexttodo{n}.txt")
    with open("nexttodo.txt", "w") as Fnext:
        for label in db.gps_gl2zhat_coarse.search(model_query(), "label"):
            if inbox(label):
                if label not in models_available:
                    codomain, conj = current_cod.get(label, (None, None))
                    if codomain is not None:
                        # Use relative j-map
                        with open(opj(output_folder, label), "w") as F:
                            _ = F.write(f"{codomain}|{','.join(str(c) for c in conj.list())}")
                
                _ = Fnext.write(label + "\n")
    print(f"Todo files printed in {time.time() - t0:.2f}s")

#######################################################
# Functions for preparing for the lattice computation #
#######################################################

@cached_function
def distinguished_vertices():
    """
    The vertices in the lattice with special names that serve as the bottoms of intervals in the lattice
    """
    query = lattice_query()
    query["name"] = {"$ne":""}
    return {rec["label"]: rec["name"] for rec in db.gps_gl2zhat_coarse.search(query, ["label", "name"])}

Xfams = ['X', 'X0', 'Xpm1', 'Xns+', 'Xsp+', 'Xns', 'Xsp', 'Xpm1,', 'XS4']

@cached_function
def intervals_to_save(max_size=60):
    """
    Returns a dictionary with keys the distinguished vertices (as integers in the hasse diagram) and values a list of labels to include in the lattice for that vertex
    """
    P = get_lattice_poset()
    H = P._hasse_diagram
    t0 = cputime()
    DV = distinguished_vertices()
    D = [P._element_to_vertex(d) for d in DV]
    trimmed = {}
    intervals = {}
    for d in D:
        trimmed[d] = T = {}
        intervals[d] = I = {}
        for x in index_iterator(P, d):
            N = [y for y in H.neighbors_in(x) if y in T]
            if any(T[y] for y in N):
                T[x] = True
            else:
                dx = set([x])
                dx.update(*[I[y] for y in N])
                if len(dx) <= max_size:
                    T[x] = False
                    I[x] = dx
                else:
                    T[x] = True
    print(f"initial transversal in {cputime() - t0:.2f}s")
    t0 = cputime()
    # Flip so that it's first indexed on vertex rather than distinguished vertex
    flipped = defaultdict(dict)
    for d in D:
        dd = P._vertex_to_element(d)
        for x, S in intervals[d].items():
            if x == d: continue # Don't include single-point intervals
            flipped[P._vertex_to_element(x)][dd] = set([P._vertex_to_element(y) for y in S])
    # Choose some collection of distinguished vertices to store in each case
    print(f"Flipped in {cputime() - t0:.2f}s")
    t0 = cputime()
    stored_intervals = {}
    num_tops = {}
    def sort_key(label):
        return [-get_rank(label)] + [(ZZ(c) if c.isdigit() else class_to_int(c)) for c in label.split(".")]
    for x, ints in flipped.items():
        if len(ints) > 1:
            # Throw out Xx(n) if n divides m and Xx(m) is also in ints
            # Unless it's X(2) and X(1), when we go up to X(1)
            by_fam = defaultdict(dict)
            for d in ints:
                fam = DV[d].split("(")[0]
                n = DV[d].split("(")[1].split(")")[0]
                if "," in n: # X1(2, m)
                    fam += ","
                    n = n.split(",")[1]
                n = ZZ(n)
                by_fam[fam][n] = d
            S = []
            for fam, ns in by_fam.items():
                for n, d in ns.items():
                    if fam == "X" or len([m for m in ns if n.divides(m)]) == 1:
                        i = int(d.split(".")[1])
                        # Sort by index (reversed), then family
                        S.append((-i, Xfams.index(fam), d))
            S.sort()
            I = J = set([x]).union(ints[S[0][2]])
            num_tops[x] = 1
            for i, f, d in S[1:]:
                I = J.union(ints[d])
                if len(I) > max_size:
                    continue
                num_tops[x] += 1
                J = I
        else:
            J = list(ints.values())[0]
            num_tops[x] = 1
        if len(J) <= max_size:
            J = sorted(J, key=sort_key)
            stored_intervals[x] = J
    print(f"Stored in {cputime() - t0:.2f}s")
    return stored_intervals, num_tops

def display(label):
    """
    The string used to space tags when rendering the lattice using graphviz
    """
    # We try to model how wide the latexed tag will be just using characters,
    # leaning toward increasing the width of named vertices
    DV = distinguished_vertices()
    if label in DV:
        return DV[label] + "XX"
    return "%sX" % label.split(".")[0]

def get_rank(label):
    """
    The layer of the lattice in which to situate the modular curve
    """
    return sum(e for (p,e) in ZZ(label.split(".")[1]).factor())

def subposet_cover_relations(P, nodes):
    """
    Analogue of P.subposet, but assuming that the nodes are saturated (if x < y in nodes then there is no z in P with x < z < y).  This can give a big speedup.
    """
    H = P._hasse_diagram
    verts = set([P._element_to_vertex(v) for v in nodes])
    edges = {}
    for a in verts:
        outedges  = [
            P._vertex_to_element(b)
            for b in H.neighbor_out_iterator(a)
            if b in verts]
        if outedges:
            edges[P._vertex_to_element(a)] = outedges
    return edges

def make_graphviz_file(label):
    """
    Creates an input file for graphviz that lays out the lattice.
    """
    P = get_lattice_poset()
    D, num_tops = intervals_to_save()
    t0 = cputime()
    if label not in D:
        return
    nodes = D[label]
    edges = subposet_cover_relations(P, nodes)
    edges = [(a, '","'.join(b)) for (a,b) in edges.items()]
    ranks = defaultdict(list)
    for lab in nodes:
        ranks[get_rank(lab)].append(lab)
    nodes = [f'"{lab}" [label="{display(lab)}",shape=plaintext]' for lab in nodes]
    edges = [f'"{a}" -> {{"{b}"}} [dir=none]' for (a,b) in edges]

    nodes = ";\n".join(nodes)
    edges = ";\n".join(edges)
    ranks = ";\n".join('{rank=same; "%s"}' % ('" "'.join(labs)) for labs in ranks.values())
    graph = f"""strict digraph "{label}" {{
rankdir=TB;
splines=line;
{edges};
{nodes};
{ranks};
}}
"""
    infile = opj("..", "equations", "graphviz_in", label)
    with open(infile, "w") as F:
        _ = F.write(graph)

def make_graphviz_files():
    """
    Creates input files for graphviz, storing them in a graphviz_in directory
    """
    print("Writing graphviz files...")
    t0 = time.time()
    P = get_lattice_poset()
    os.makedirs(opj("..", "equations", "graphviz_in"), exist_ok=True)
    for label in P:
        make_graphviz_file(label)
    print(f"Graphviz files completed in {time.time() - t0:.2f}s")

###############################################################
# Functions for preparing for the rational points computation #
###############################################################

def is_isolated(degree, g, rank, gonlow, simp, dims):
    # We encode the isolatedness in a small integer, p + a, where
    # p = 3,0,-3 for P1 isolated/unknown/parameterized and
    # a = 1,0,-1 for AV isolated/unknown/parameterized
    # 4 = isolated (both P1 isolated and AV isolated)
    # 0 = unknown for both
    # -4 = both P1 and AV parameterized
    if g == 0:
        # Always P1 parameterized and AV isolated
        return "-2"
    elif degree == 1:
        if g == 1:
            if rank is None:
                return "3"
            elif rank > 0:
                # Always P1 isolated and AV parameterized
                return "2"
            else:
                return "4"
        else:
            return "4"
    elif degree < QQ(gonlow) / 2 or degree < gonlow and (rank == 0 or simp and degree < g):
        return "4"
    elif degree > g:
        # Always P1 parameterized; AV parameterized if and only if rank positive
        if rank is None:
            return "-3"
        if rank > 0:
            return "-4"
        else:
            return "-2"
    elif rank is not None and degree == g and rank > 0:
        return "-1" # AV parameterized; can compute if P1 parameterized by Riemann Roch with a model
    else:
        if rank == 0 or (dims is not None and degree <= min(dims)): # for second part, using degree < g
            # Actually only need to check the minimum of the dimensions where the rank is positive
            # Always AV isolated; can try to computed whether P1 parameterized by Riemann roch
            return "1"
        else:
            return "0"

def prepare_rational_points(output_folder="../equations/jinvs/", manual_data_folder="../rational-points/data", ecnf_data_file="ecnf_data.txt", cm_data_file="cm_data.txt"):
    print("Creating rational point data...")
    t0 = time.time()
    # Writes files with rational points for pullback along j-maps
    os.makedirs(output_folder, exist_ok=True)

    lit_data = load_points_files(manual_data_folder)
    lit_fields = sorted(set([datum[2] for datum in lit_data]))
    print(f"Loaded tables from files in {time.time() - t0:.2f}s")

    gpdata = load_gl2zhat_rational_data()

    P = get_rational_poset()
    H = P._hasse_diagram
    ecq_db_data = load_ecq_data(cm_data_file)

    ecnf_db_data = list(load_ecnf_data(ecnf_data_file))

    fields = list(set(tup[2] for tup in ecq_db_data + ecnf_db_data + lit_data))
    nf_lookup = {rec["label"]: rec["coeffs"] for rec in db.nf_fields.search({"label": {"$in": fields}})}
    assert all(K in nf_lookup for K in fields)

    # Check for overlap as we add points
    jinvs_seen = defaultdict(set)
    #point_counts = defaultdict(Counter)
    jinvs = defaultdict(list)
    print("Writing rational points files...")
    t0 = time.time()
    with open("allpoints.txt", "w") as F:
        for ctr, (label, degree, field_of_definition, jorig, jinv, jfield, j_height, cm, Elabel, known_isolated, conductor_norm, ainvs) in enumerate(ecq_db_data + ecnf_db_data + lit_data):
            if ctr and ctr % 100000 == 0:
                print(f"{ctr}/{len(ecq_db_data) + len(ecnf_db_data) + len(lit_data)}")
            #assert label != "1.1.0.a.1"
            if label == "1.1.0.a.1": continue
            if "-" in label:
                # For now, if the label is a fine label we coarsify it (so that we can get started on models)
                label = to_coarse_label(label)
            for v in H.breadth_first_search(P._element_to_vertex(label)):
                plabel = P._vertex_to_element(v)
                if (field_of_definition, jfield, jinv) not in jinvs_seen[plabel]:
                    jinvs_seen[plabel].add((field_of_definition, jfield, jinv))
                    #point_counts[plabel][degree] += 1
                    gdat = gpdata[plabel]
                    if label == plabel and known_isolated:
                        isolated = "4"
                    else:
                        isolated = is_isolated(degree, gdat["genus"], gdat["rank"], gdat["q_gonality_bounds"][0], gdat["simple"], gdat["dims"])
                    # We only store ainvs for fine models, since otherwise it's recoverable from the j-invariant
                    if "-" in plabel:
                        ainvshow = ainvs
                    else:
                        ainvshow = r"\N"
                    _ = F.write(f"{plabel}|{degree}|{field_of_definition}|{jorig}|{jinv}|{jfield}|{j_height}|{cm}|{Elabel}|{isolated}|{conductor_norm}|{ainvshow}\n")

                    # We only need to compute isolatedness and model-coordinates when genus > 0
                    if gdat["genus"] == 0: continue
                    if jorig == r"\N":
                        jorig = jinv
                    jinvs[plabel].append((jorig, nf_lookup[field_of_definition], isolated))
    for plabel, pts in jinvs.items():
        with open(opj(output_folder, plabel), "w") as F:
            for jinv, nf, isolated in pts:
                _ = F.write(f"{jinv}|{str(nf).replace(' ','')[1:-1]}|{isolated}\n")
    print(f"Done writing rational point files in {time.time() - t0:.2f}s")

#######################################################
# Functions for preparing for the picture computation #
#######################################################

def make_picture_input():
    print("Creating picture input...", end="")
    t0 = time.time()
    sys.stdout.flush()
    with open("picture_labels.txt", "w") as F:
        for label in db.gps_sl2zhat_fine.search(psl2_query(), "label"):
            if pslbox(label): # checks that contains -1
                _ = F.write(label + "\n")
    print(f" done in {time.time() - t0:.2f}s")

def make_psl2_input_data():
    print("Writing psl2 input data...", end="")
    t0 = time.time()
    sys.stdout.flush()
    folder = opj("..", "equations", "psl2_input_data")
    os.makedirs(folder, exist_ok=True)
    for rec in db.gps_sl2zhat_fine.search(psl2_query(), ["label", "subgroup"]):
        if pslbox(rec["label"]): # checks that contains -1
            with open(opj(folder, rec["label"]), "w") as F:
                _ = F.write(",".join(str(c) for c in flatten(rec["subgroup"])))
    print(f" done in {time.time() - t0:.2f}s")

########################################################
# Functions for preparing for the gonality computation #
########################################################

def make_gonality_files():
    print("Writing gonality files...", end="")
    t0 = time.time()
    sys.stdout.flush()
    folder = opj("..", "equations", "gonality")
    os.makedirs(folder, exist_ok=True)
    for rec in db.gps_gl2zhat_coarse.search(model_query(), ["label", "q_gonality_bounds", "qbar_gonality_bounds"]):
        with open(opj(folder, rec["label"]), "w") as F:
            _ = F.write(",".join(str(c) for c in rec["q_gonality_bounds"] + rec["qbar_gonality_bounds"]))
    print(f" done in {time.time() - t0:.2f}s")

#########################################################
# Functions for setting up genus 2 curve identification #
#########################################################

def make_g2_lookup_data():
    print("Writing g2 invariant files...", end="")
    t0 = time.time()
    sys.stdout.flush()
    folder = opj("..", "equations", "g2invs")
    if not ope(folder):
        os.makedirs(folder)
        for rec in db.g2c_curves.search({}, ["label", "eqn", "g2_inv"]):
            fname = "h" + rec["g2_inv"][1:-1].replace(",", ".").replace("/", "_")
            with open(opj(folder, fname), "a") as F:
                _ = F.write(f"{rec['label']}|{rec['eqn']}")
    print(f" done in {time.time() - t0:.2f}s")

#############################
# Execute the main function #
#############################

prep(stage=args.stage)

#!/usr/bin/env -S sage -python

import os
import sys
import shutil
import re
import subprocess
import argparse
from collections import defaultdict
from sage.all import ZZ, QQ, PolynomialRing, MatrixSpace, EllipticCurve, NumberField, cached_function, flatten, walltime, cputime, DiGraph
from sage.combinat.posets.posets import FinitePoset
from sage.databases.cremona import class_to_int

opj = os.path.join
ope = os.path.exists
sys.path.append(os.path.expanduser(opj("~", "lmfdb")))
from lmfdb import db
from cloud_common import rational_poset_query, get_lattice_poset, index_iterator, to_coarse_label, inbox, load_gl2zhat_rational_data


parser = argparse.ArgumentParser("Create a tarball for cloud computation")
parser.add_argument("stage", type=int, help="stage of compututation (1=initial setup, 2=after getting cod data back")
parser.add_argument("--codprob", type=float, help="probability that each valid codomain is included")
parser.add_argument("--domprob", type=float, help="probablity that domains of relative j-maps are included, conditional on their codomain being included")
parser.add_argument("--absprob", type=float, help="probability that non-canonical curves are included")

args = parser.parse_args()

def prep(stage):
    if stage == 1:
        make_input_data()
        prep_hyperelliptic()
        run_hyperelliptic()
        get_relj_codomains()
        make_psl2_input_data()
        make_g2_lookup_data()
        make_graphviz_files()
        make_picture_input()
        make_gonality_files()
        prepare_rational_points()
    else:
        extract_stage1()
    make_tarball(stage=stage)

def make_input_data():
    """
    Create the input folder that stores generators
    """
    print("Creating input data...", end="")
    folder = opj("..", "equations", "input_data")
    os.makedirs(folder, exist_ok=True)
    for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True}, ["label", "generators"]):
        with open(opj(folder, rec["label"]), "w") as F:
            _ = F.write(",".join(str(c) for c in flatten(rec["generators"])))
    print(" done")

def extract_stage1():
    """
    Extract contents of stage 1 output file (stored in ROOT/upload/output1) for running stage 2
    """
    os.makedirs(opj("..", "equations", "rats"), exist_ok=True)
    os.makedirs(opj("..", "equations", "canonical_models"), exist_ok=True)
    with open("output1") as F:
        for line in F:
            if not line: continue
            label, rest = line[1:].split("|", 1)
            if line[0] == "R":
                folder = "rats"
            elif line[0] == "C":
                folder = "canonical_models"
            else:
                continue
            with open(opj("..", "equations", folder, label), "a") as Fout:
                _ = Fout.write(rest)

def make_tarball(stage=1):
    """
    Create a tarball with all the files needed to run on another server
    """
    if stage == 1:
        shutil.copy("codtodo.txt", opj("..", "equations", "todo.txt"))
    else:
        shutil.copy("nexttodo.txt", opj("..", "equations", "todo.txt"))
    os.chdir(opj("..", "equations"))
    with open("todo.txt") as F:
        for n, line in enumerate(F, 1):
            pass
    print("Creating tarball...", end="")
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
        "jinvs",
        "g2invs",
    ]
    if stage == 2:
        include.extend(["rats", "canonical_models"])
    subprocess.run(f"tar -cf ../upload/stage{stage}_{n}.tar " + " ".join(include), shell=True)
    print(" done")
    if stage == 1:
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
    with open(opj("..", "equations", "hyptodo.txt"), "w") as F:
        for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True, "genus":{"$gte":3, "$lte":17}}, ["label", "qbar_gonality_bounds"]):
            if inbox(rec["label"]) and rec["qbar_gonality_bounds"][0] == 2 and rec["qbar_gonality_bounds"][1] > 2 and not ope(opj("..", "ishyp", rec["label"])):
                # possibly hyperelliptic
                _ = F.write(rec["label"] + "\n")
    print(" done")

def run_hyperelliptic():
    """
    Determines which modular curves that might be hyperelliptic actually are, since this is required for determining codomains for relative j-maps
    """
    os.chdir(opj("..", "equations"))
    with open("hyptodo.txt") as F:
        n = 0
        for n, line in enumerate(F, 1):
            pass
    if n > 0:
        curn = len(os.listdir("ishyp"))
        folder = os.path.abspath("ishyp")
        print(f"Determining hyperellipticity (done when {curn + n} files exist in {folder})")
        subprocess.run('parallel -j80 -a hyptodo.txt "magma -b label:={1} GetPrecHyp.m"', shell=True)
        print("Done determining hyperellipticity")
    os.chdir(opj("..", "upload"))

def get_relj_codomains():
    # Currently, the plan is to just run GetPrecHyp.m on lovelace, so we just use the output in the folder ishyp
    print("Loading hyperelliptic data...", end="")
    output_folder = opj("..", "equations", "cod")
    os.makedirs(output_folder, exist_ok=True)
    hyp_lookup = {}
    for label in os.listdir(opj("..", "equations", "ishyp")):
        with open(opj("..", "equations", "ishyp", label)) as F:
            hyp, prec = F.read().strip().split("|")
            hyp_lookup[label] = (hyp == "t")
    print(" done")
    print("Determining codomains...", end="")
    parents_conj = {}
    M = MatrixSpace(ZZ, 2)
    for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True, "$or": [{"level":{"$lt":24}, "genus": {"$gte": 3, "$lte": 24}}, {"level":{"$lt":120}, "genus":{"$gte":3, "$lte":14}}, {"genus":{"$gte":3, "$lte":6}}]}, ["label", "parents", "parents_conj", "qbar_gonality"]):
        if not inbox(rec["label"]):
            continue
        if rec["qbar_gonality"] == 2:
            hyp_lookup[rec["label"]] = True
        for plabel, pconj in zip(rec["parents"], rec["parents_conj"]):
            parents_conj[rec["label"], plabel] = M(pconj)
    P = get_lattice_poset()
    H = P._hasse_diagram
    X1 = P._element_to_vertex("1.1.0.a.1")
    cod = {}
    def index_sort_key(pair):
        N, i, g, a, n = pair[0].split(".")
        return (int(i), int(N), int(g), class_to_int(a), int(n))
    for x in index_iterator(P, X1):
        label = P._vertex_to_element(x)
        N, i, g, a, n = label.split(".")
        if int(g) >= 3 and inbox(label) and not hyp_lookup.get(label):
            tmp = [(label, M((1,0,0,1)))]
            for y in H.neighbors_in(x):
                ylabel = P._vertex_to_element(y)
                if ylabel in cod:
                    ybest, yconj = cod[ylabel]
                    conj = parents_conj[label, ylabel] * yconj
                    tmp.append((ybest, conj))
            cod[label] = min(tmp, key=index_sort_key)
    cods = defaultdict(int)
    for label, (codomain, conj) in cod.items():
        if label != codomain:
            # We track the maximum index used for a given codomain, since that affects the precision needed for computing the relative j-map.
            cods[codomain] = max(cods[codomain], int(label.split(".")[1]))
            with open(opj(output_folder, label), "w") as F:
                _ = F.write(f"{codomain}|{','.join(str(c) for c in conj.list())}")
    # Now cods contains the maximum relative index of anything mapping to the given codomain
    with open("codtodo.txt", "w") as Ftodo:
        for c, maxind in cods.items():
            _ = Ftodo.write(c + "\n")
            with open(opj(output_folder, c), "w") as F:
                _ = F.write(f"{c}|{maxind}")
    with open("nexttodo.txt", "w") as Fnext:
        with open("lattodo.txt", "w") as Flat:
            for label in db.gps_gl2zhat_fine.search({"contains_negative_one":True}, "label"):
                if label not in cods:
                    if inbox(label):
                        _ = Fnext.write(label + "\n")
                    else:
                        _ = Flat.write(label + "\n")

#######################################################
# Functions for preparing for the lattice computation #
#######################################################

@cached_function
def distinguished_vertices():
    """
    The vertices in the lattice with special names that serve as the bottoms of intervals in the lattice
    """
    return {rec["label"]: rec["name"] for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True, "name":{"$ne":""}}, ["label", "name"])}

Xfams = ['X', 'X0', 'X1', 'Xsp', 'Xns', 'Xsp+', 'Xns+', 'XS4']

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
    print("initial transversal in", cputime() - t0)
    t0 = cputime()
    # Flip so that it's first indexed on vertex rather than distinguished vertex
    flipped = defaultdict(dict)
    for d in D:
        dd = P._vertex_to_element(d)
        for x, S in intervals[d].items():
            if x == d: continue # Don't include single-point intervals
            flipped[P._vertex_to_element(x)][dd] = set([P._vertex_to_element(y) for y in S])
    # Choose some collection of distinguished vertices to store in each case
    print("Flipped in", cputime() - t0)
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
                n = ZZ(DV[d].split("(")[1].split(")")[0])
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
                I = I.union(ints[d])
                if len(I) > max_size:
                    break;
                num_tops[x] += 1
                J = I
        else:
            J = list(ints.values())[0]
            num_tops[x] = 1
        if len(J) <= max_size:
            J = sorted(J, key=sort_key)
            stored_intervals[x] = J
    print("Stored in", cputime() - t0)
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
    P = get_lattice_poset()
    os.makedirs(opj("..", "equations", "graphviz_in"), exist_ok=True)
    for label in P:
        make_graphviz_file(label)

###############################################################
# Functions for preparing for the rational points computation #
###############################################################

def trim_modm_images(images):
    """
    Takes partially defined labels from the modm_images column of ec_curvedata and
    only keeps fully-defined images that are maximal (for level-divisibility)
    """
    images = [label for label in images if "?" not in label and int(label.split(".")[0]) < 24]
    Ns = [int(label.split(".")[0]) for label in images]
    locs = [i for i in range(len(Ns)) if not any(Ns[j] % Ns[i] == 0 for j in range(len(Ns)) if i != j)]
    return [images[i] for i in locs]


S_LABEL_RE = re.compile(r"^(\d+)(G|B|Cs|Cn|Ns|Nn|A4|S4|A5)(\.\d+){0,3}$")
LABEL_RE = re.compile(r"^\d+\.\d+\.\d+\.[a-z]+\.\d+$")
NFLABEL_RE = re.compile(r"^\d+\.\d+\.\d+\.\d+$")
QQ_RE = re.compile(r"^-?\d+(/\d+)?$")
ZZ_RE = re.compile(r"^(-?\d+)|\\N$")
QQ_LIST_RE = re.compile(r"^-?\d+(/\d+)?(,-?\d+(/\d+)?)*$") # can't be empty
NN_LIST_RE = re.compile(r"^(\d+(,\s*\d+)*)?$") # can be empty

def load_points_files(data_folder):
    all_pieces = []
    field_labels = set()
    for fname in os.listdir(data_folder):
        if fname.endswith("-pts.txt"):
            with open(os.path.join(data_folder, fname)) as F:
                for line in F:
                    if line.startswith("//") or not line.strip():
                        continue
                    line = line.replace("'", "").replace('"', '')
                    pieces = line.strip().split("|")
                    if len(pieces) != 8:
                        raise ValueError(f"line has {len(pieces)} when it should have 8: {line}")
                    all_pieces.append(pieces)
                    field_labels.add(pieces[4].strip())

    nfs, sub_lookup, embeddings = load_nf_data(list(field_labels))

    ans = []
    X0s = {rec["name"]: rec["label"] for rec in db.gps_gl2zhat_fine.search({"name": {"$like": "X0%"}}, ["name", "label"], silent=True)}
    RSZB_lookup = {rec["RSZBlabel"]: rec["label"] for rec in db.gps_gl2zhat_fine.search({"name": {"$exists": True}}, ["label", "RSZBlabel"])}
    skipped = set()
    for pieces in all_pieces:
        name = label = pieces[0].strip()
        if label.startswith("X0"):
            label = X0s.get(label)
            if label is None:
                # We haven't added X0(56) yet....
                if name not in skipped:
                    print(f"Skipping name {name}")
                    skipped.add(name)
                continue
        level = int(label.split(".")[0])
        if level >= 24: continue
        if not LABEL_RE.fullmatch(label):
            label = RSZB_lookup[label]
        field_of_definition = pieces[2].strip()
        degree = field_of_definition.split(".")[0]
        jinv = pieces[3].replace(" ", "").replace("[", "").replace("]", "")
        jfield = pieces[4].strip()
        if jfield in ["1.1.1.1", field_of_definition]:
            jorig = r"\N"
        else:
            # Recover the j-invariant in the residue field from our chosen embedding.
            K = nfs[jfield]
            j = [QQ(c) for c in jinv.split(",")]
            j += [0] * (K.degree() - len(j))
            j = K(j)
            L = nfs[field_of_definition]
            root = embeddings[jfield, field_of_definition]
            emb = K.hom([root])
            jorig = ",".join(str(c) for c in list(emb(j)))
        j_height = get_j_height(jinv, jfield, nfs)
        cm = pieces[6].strip()
        quo_info = pieces[7].strip().replace("[", "{").replace("]", "}")
        assert LABEL_RE.fullmatch(label), f"Invalid curve label {label}"
        assert ZZ_RE.match(degree), f"Invalid degree {degree} for {label}"
        assert NFLABEL_RE.match(field_of_definition), f"Invalid field of definition {field_of_definition} for {label}"
        assert QQ_LIST_RE.match(jinv), f"Invalid j-invariant {jinv} for {label}"
        assert NFLABEL_RE.match(jfield), f"Invalid field of j {jfield} for {label}"
        assert ZZ_RE.match(cm), f"Invalid CM discriminant {cm} for {label}"
        assert quo_info == r"\N" or NN_LIST_RE.match(quo_info[1:-1]), f"Invalid quotient information {quo_info} for {label}"
        ans.append((label, int(degree), field_of_definition, jorig, jinv, jfield, j_height, cm, r"\N", True, r"\N", r"\N"))
    return ans

def get_j_height(jinv, j_field, nfs):
    K = nfs[j_field]
    j = [QQ(c) for c in jinv.split(",")]
    j += [0] * (K.degree() - len(j))
    j = K(j)
    return j.global_height()

def load_nf_data(field_labels=None):
    if field_labels is None:
        field_labels = db.ec_nfcurves.distinct("field_label")
    R = PolynomialRing(QQ, 'x')
    field_data = list(db.nf_fields.search({"label": {"$in": field_labels}},
                                          ["label", "coeffs", "subfields", "degree", "disc_abs"], silent=True))
    subs = [[int(c) for c in sub.split(".")] for sub in set(sum((rec["subfields"] for rec in field_data), []))]
    sub_data = list(db.nf_fields.search({"$or": [{"coeffs": sub} for sub in subs]}, ["degree", "disc_abs", "label", "coeffs"], silent=True))
    if len(subs) != len(sub_data):
        raise RuntimeError("Sub not labeled or discriminant clash")
    sub_lookup = {(rec["degree"], rec["disc_abs"]) : (rec["label"], R(rec["coeffs"])) for rec in sub_data}
    by_coeffs = {tuple(rec["coeffs"]): rec["label"] for rec in sub_data}
    sub_lookup[1, 1] = ("1.1.1.1", R.gen() - 1)
    nfs = {"1.1.1.1": QQ}
    embeddings = {}
    for rec in field_data:
        f = R(rec["coeffs"])
        nfs[rec["label"]] = L = NumberField(f, 'a')
        sub_lookup[rec["degree"], rec["disc_abs"]] = (rec["label"], f)
        for sub in rec["subfields"]:
            sub = [ZZ(c) for c in sub.split(".")]
            g = R(sub)
            embeddings[by_coeffs[tuple(sub)], rec["label"]] = g.roots(L, multiplicities=False)[0]

    print("Constructed number field lookup tables")
    return nfs, sub_lookup, embeddings

def save_ecnf_data(fname="ecnf_data.txt"):
    # We have to modify ecnf data in a way that's somewhat slow (computing the actual field in which j lies)
    # We do that once, save it, and then load the result from disc as needed
    nfs, sub_lookup, _ = load_nf_data()

    total = db.ec_nfcurves.count()
    with open(fname, "w") as F:
        for progress, rec in enumerate(db.ec_nfcurves.search({}, ["galois_images", "degree", "field_label", "jinv", "cm", "label", "conductor_norm", "base_change", "ainvs"], silent=True)):
            if progress and progress % 10000 == 0:
                print(f"ECNF: {progress}/{total}")
            if rec["base_change"] or not rec["galois_images"]:
                continue
            if rec["jinv"].endswith(",0" * (rec["degree"] - 1)):
                jfield = "1.1.1.1"
                jinv = rec["jinv"].split(",")[0]
                # Searching ecnf using a rational j-invariant works even when the residue field is not Q
                jorig = r"\N"
            else:
                K = nfs[rec["field_label"]]
                j = K([QQ(c) for c in rec["jinv"].split(",")])
                Qj, jinc = K.subfield(j)
                if Qj.degree() == rec["degree"]:
                    jfield = rec["field_label"]
                    jinv = rec["jinv"]
                    jorig = r"\N"
                else:
                    jfield, f = sub_lookup[Qj.degree(), Qj.discriminant().abs()]
                    jinv = ",".join(str(c) for c in f.roots(Qj, multiplicities=False)[0].coordinates_in_terms_of_powers()(Qj.gen()))
                    #root = embeddings[jfield, rec["field_label"]]
                    #jinv = ",".join(str(c) for c in root.coordinates_in_terms_of_powers()(jinc(Qj.gen())))
                    jorig = rec["jinv"]
            Slabels = ",".join(rec["galois_images"])
            j_height = get_j_height(jinv, jfield, nfs)
            _ = F.write(f"{Slabels}|{rec['degree']}|{rec['field_label']}|{jorig}|{jinv}|{jfield}|{j_height}|{rec['cm']}|{rec['label']}|{rec['conductor_norm']}|{rec['ainvs']}\n")

def load_ecnf_data(fname="ecnf_data.txt"):
    # Galois images are stored for NF curves using Sutherland labels
    from_Slabel = {
        rec["Slabel"] : rec["label"]
        for rec in db.gps_gl2zhat_fine.search(
                {"Slabel": {"$exists":True}},
                ["Slabel", "label"],
                silent=True,
        )
    }
    print("Constructed Sutherland label lookup table")

    # db.ec_nfcurves doesn't currently contain information about which curves are base changes
    # We want to avoid base changes, since they would have incorrect field_of_definition
    # We computed the set of base change curves separately
    with open("ecnf_is_bc.txt") as F:
        isbc = set(line.strip() for line in F)

    with open(fname) as F:
        for line in F:
            Slabels, degree, field_of_definition, jorig, jinv, jfield, j_height, cm, Elabel, conductor_norm, ainvs = line.strip().split("|")
            if Elabel in isbc:
                continue
            for Slabel in Slabels.split(","):
                if not ("[" in Slabel or S_LABEL_RE.fullmatch(Slabel)):
                    print("Warning: invalid Slabel", Slabel)
                if Slabel in from_Slabel:
                    label = from_Slabel[Slabel]
                    yield label, int(degree), field_of_definition, jorig, jinv, jfield, j_height, int(cm), Elabel, False, conductor_norm, ainvs
    print("Loaded ECNF data from file")

def convert_cm_datafile(cmin, cmout):
    # Convert from Drew's format (which has some extra stuff and is missing others)
    lookup = {tuple(rec["ainvs"]): rec["lmfdb_label"] for rec in db.ec_curvedata.search({}, ["ainvs", "lmfdb_label"])}
    with open(cmout, "w") as Fout:
        with open(cmin) as F:
            for line in F:
                level, gens, label, ainvs = line.strip().split(":")
                ainvs = [ZZ(a) for a in ainvs[1:-1].split(",")]
                E = EllipticCurve(ainvs)
                cm = E.cm_discriminant()
                j = E.j_invariant()
                ainvs = tuple(E.minimal_model().a_invariants())
                conductor = E.conductor()
                lmfdb_label = lookup.get(ainvs, r"?")
                ainvs = ";".join(str(a) for a in ainvs) # format compatible with ec_nfcurves
                _ = Fout.write(f"{lmfdb_label}|{label}|{j}|{cm}|{ainvs}|{conductor}\n")

def load_ecq_data(cm_data_file):
    t0 = walltime()
    ecq_db_data = []
    # CM data computed by Shiva
    cm_lookup = defaultdict(list)
    with open(cm_data_file) as F:
        for line in F:
            lmfdb_label, modcurve_label, j, cm, ainvs, conductor = line.strip().split("|")
            if lmfdb_label == "?":
                ecq_db_data.append((modcurve_label, 1, "1.1.1.1", r"\N", j, "1.1.1.1", str(QQ(j).global_height()), int(cm), lmfdb_label, False, conductor, ainvs))
            else:
                cm_lookup[lmfdb_label].append(modcurve_label)

    for rec in db.ec_curvedata.search({}, ["lmfdb_label", "jinv", "cm", "conductor", "modm_images", "ainvs"]):
        Elabel = rec["lmfdb_label"]
        jinv = QQ(tuple(rec["jinv"]))
        if rec["cm"]:
            images = cm_lookup.get(rec["lmfdb_label"], [])
        else:
            images = rec["modm_images"]
        images = trim_modm_images(images)
        ainvs = ";".join(str(a) for a in rec["ainvs"])
        for label in images:
            ecq_db_data.append((label, 1, "1.1.1.1", r"\N", str(jinv), "1.1.1.1", str(jinv.global_height()), rec["cm"], Elabel, False, str(rec["conductor"]), ainvs))
    print("Loaded elliptic curves over Q", walltime() - t0)
    return ecq_db_data

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
            if rank > 0:
                # Always P1 isolated and AV parameterized
                return "2"
            elif rank == 0:
                return "4"
            else: # rank is None
                return "3"
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
    elif degree == g and rank > 0:
        return "-1" # AV parameterized; can compute if P1 parameterized by Riemann Roch with a model
    else:
        if rank == 0 or (dims is not None and degree <= min(dims)): # for second part, using degree < g
            # Actually only need to check the minimum of the dimensions where the rank is positive
            # Always AV isolated; can try to computed whether P1 parameterized by Riemann roch
            return "1"
        else:
            return "0"

@cached_function
def get_rational_poset():
    # The poset of modular curves that might have rational points, omitting X(1)
    t0 = walltime()
    R = []
    for rec in db.gps_gl2zhat_fine.search(rational_poset_query(), ["label", "parents", "coarse_label"]):
        if rec["label"] == "1.1.0.a.1": continue
        parents = [label for label in rec["parents"] if label != "1.1.0.a.1"]
        if rec["label"] != to_coarse_label(rec["label"]) and to_coarse_label(rec["label"]) != "1.1.0.a.1":
            parents += [to_coarse_label(rec["label"])]
        for olabel in parents:
            R.append([rec["label"], olabel]) # note that this is the opposite direction of edges from lattice_poset
    print("DB data loaded in", walltime() - t0)
    t0 = cputime()
    D = DiGraph()
    D.add_edges(R, loops=False)
    print("Edges added to graph in", cputime() - t0)
    t0 = cputime()
    P = FinitePoset(D)
    print("Poset created in", cputime() - t0)
    return P

def prepare_rational_points(output_folder="../equations/jinvs/", manual_data_folder="../rational-points/data", ecnf_data_file="ecnf_data.txt", cm_data_file="cm_data.txt"):
    # Writes files with rational points for pullback along j-maps
    os.makedirs(output_folder, exist_ok=True)

    lit_data = load_points_files(manual_data_folder)
    lit_fields = sorted(set([datum[2] for datum in lit_data]))
    print("Loaded tables from files")

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
    with open("allpoints.txt", "w") as F:
        for ctr, (label, degree, field_of_definition, jorig, jinv, jfield, j_height, cm, Elabel, known_isolated, conductor_norm, ainvs) in enumerate(ecq_db_data + ecnf_db_data + lit_data):
            if ctr and ctr % 10000 == 0:
                print(f"{ctr}/{len(ecq_db_data) + len(ecnf_db_data) + len(lit_data)}")
            #assert label != "1.1.0.a.1"
            if label == "1.1.0.a.1": continue
            # Don't want to save the interval, since that takes quadratic space
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

#######################################################
# Functions for preparing for the picture computation #
#######################################################

def make_picture_input():
    with open("picture_labels.txt", "w") as F:
        for label in db.gps_gl2zhat_fine.distinct("psl2label"):
            _ = F.write(label + "\n")

def make_psl2_input_data():
    folder = opj("..", "equations", "psl2_input_data")
    os.makedirs(folder, exist_ok=True)
    for rec in db.gps_sl2zhat_fine.search({}, ["label", "generators"]):
        with open(opj(folder, rec["label"]), "w") as F:
            _ = F.write(",".join(str(c) for c in flatten(rec["generators"])))

########################################################
# Functions for preparing for the gonality computation #
########################################################

def make_gonality_files():
    folder = opj("..", "equations", "gonality")
    os.makedirs(folder, exist_ok=True)
    for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True}, ["label", "q_gonality_bounds", "qbar_gonality_bounds"]):
        with open(opj(folder, rec["label"]), "w") as F:
            _ = F.write(",".join(str(c) for c in rec["q_gonality_bounds"] + rec["qbar_gonality_bounds"]))

#########################################################
# Functions for setting up genus 2 curve identification #
#########################################################

def make_g2_lookup_data():
    folder = opj("..", "equations", "g2invs")
    if not ope(folder):
        os.makedirs(folder)
        for rec in db.g2c_curves.search({}, ["label", "eqn", "g2_inv"]):
            fname = "h" + rec["g2_inv"][1:-1].replace(",", ".").replace("/", "_")
            with open(opj(folder, fname), "a") as F:
                _ = F.write(f"{rec['label']}|{eqn}")

#############################
# Execute the main function #
#############################

prep(stage=args.stage)

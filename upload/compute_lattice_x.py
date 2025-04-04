#!/usr/bin/env -S sage -python
import subprocess
import argparse
import os
import re
import sys
from collections import defaultdict, Counter
from sage.misc.cachefunc import cached_function
from sage.all import ZZ, QQ, Poset, DiGraph, flatten, gcd, PolynomialRing, MatrixSpace, EllipticCurve, NumberField
from sage.combinat.posets.posets import FinitePoset
from sage.misc.misc import cputime, walltime
from sage.databases.cremona import class_to_int
from numpy import mean, median, std
opj = os.path.join
ope = os.path.exists

#parser = argparse.ArgumentParser("Compute diagramx for modular curve lattices")
#parser.add_argument("job", type=int, help="job number: 0 to n-1, where n is the number of parallel threads used")
#parser.add_argument("num_jobs", type=int, help="total number of jobs n")
#parser.add_argument("outfolder", help="folder to store results")
#args = parser.parse_args()

sys.path.append(os.path.expanduser(opj("~", "lmfdb")))
from lmfdb import db

@cached_function
def get_lattice_poset():
    t0 = walltime()
    R = []
    for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True}, ["label", "parents"]):
        for olabel in rec["parents"]:
            R.append([olabel, rec["label"]]) # Use backward direction so that breadth first search is faster
    print("DB data loaded in", walltime() - t0)
    t0 = cputime()
    D = DiGraph()
    D.add_edges(R, loops=False)
    print("Edges added to graph in", cputime() - t0)
    t0 = cputime()
    P = FinitePoset(D)
    print("Poset created in", cputime() - t0)
    return P

@cached_function
def rational_poset_query():
    # We need to also include prime levels since ec_nfcurve has prime level galois_images, and many of the hand-curated low-degree points are on curves of prime level
    ecnf_primes = sorted(set(sum(db.ec_nfcurves.distinct('nonmax_primes'), [])))
    return {"$or": [{"pointless": False}, {"pointless": None}, {"level": {"$in": ecnf_primes}}]}

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

def index_iterator(P, v, reverse=False):
    """
    INPUT:

    - P, the output of either get_lattice_poset() or get_rational_poset()
    - v, a vertex in P._hasse_diagram

    OUTPUT:
    - an iterator over the descedents of v, in index order (and thus iterating over parents before children)
    """
    # Since breadth_first_search doesn't guarantee that parents are visited before children, we return an ordering of the vertices that will do so
    H = P._hasse_diagram
    by_index = defaultdict(list)
    for w in H.breadth_first_search(v):
        label = P._vertex_to_element(w)
        ind = int(label.split(".")[1])
        by_index[ind].append(w)
    for ind in sorted(by_index, reverse=reverse):
        yield from by_index[ind]

@cached_function
def distinguished_vertices():
    return {rec["label"]: rec["name"] for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True, "name":{"$ne":""}}, ["label", "name"])}

Xfams = ['X', 'X0', 'X1', 'Xsp', 'Xns', 'Xsp+', 'Xns+', 'XS4']

@cached_function
def intervals_to_save(max_size=60):
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
    # We try to model how wide the latexed tag will be just using characters,
    # leaning toward increasing the width of named vertices
    DV = distinguished_vertices()
    if label in DV:
        return DV[label] + "XX"
    return "%sX" % label.split(".")[0]

def get_rank(label):
    return sum(e for (p,e) in ZZ(label.split(".")[1]).factor())

def sort_key(label):
    return [-get_rank(label)] + [(ZZ(c) if c.isdigit() else class_to_int(c)) for c in label.split(".")]

def subposet_cover_relations(P, nodes):
    # Unlike P.subposet(nodes), we assume that nodes are saturated: if x < y in nodes then there is no z in P with x < z < y
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

def trim_modm_images(images):
    # Only keep fully-defined images that are maximal (for level-divisibility)
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

def load_gl2zhat_rational_data():
    return {rec["label"]: rec for rec in db.gps_gl2zhat_fine.search(rational_poset_query(), ["label", "genus", "simple", "rank", "dims", "name", "level", "index", "q_gonality_bounds", "coarse_label"], silent=True)}

def load_gl2zhat_cusp_data():
    return {rec["label"]: rec for rec in db.gps_gl2zhat_fine.search({"contains_negative_one": True}, ["label", "genus", "simple", "rank", "dims", "name", "level", "index", "q_gonality_bounds", "rational_cusps"], silent=True)}

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

#os.makedirs(args.outfolder, exist_ok=True)
#todo = list(db.gps_gl2zhat_test.search({}, "label"))[args.job::args.num_jobs]
#for label in todo:
#    xcoord = save_graphviz(label)
#    lat = sorted(xcoord, key=sort_key)
#    xs = [xcoord[lab] for lab in lat]
#    lat = ",".join(lat)
#    xs = ",".join([str(x) for x in xs])
#    with open(opj(args.outfolder, label), "w") as F:
#        _ = F.write(f"{label}|{{{lat}}}|{{{xs}}}\n")


def make_graphviz_files():
    P = get_lattice_poset()
    os.makedirs(opj("..", "equations", "graphviz_in"), exist_ok=True)
    for label in P:
        make_graphviz_file(label)

def make_picture_input():
    with open("picture_labels.txt", "w") as F:
        for label in db.gps_gl2zhat_fine.distinct("psl2label"):
            _ = F.write(label + "\n")

def make_gonality_files():
    folder = opj("..", "equations", "gonality")
    os.makedirs(folder, exist_ok=True)
    for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True}, ["label", "q_gonality_bounds", "qbar_gonality_bounds"]):
        with open(opj(folder, rec["label"]), "w") as F:
            _ = F.write(",".join(str(c) for c in rec["q_gonality_bounds"] + rec["qbar_gonality_bounds"]))

def make_input_data():
    folder = opj("..", "equations", "input_data")
    os.makedirs(folder, exist_ok=True)
    for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True}, ["label", "generators"]):
        with open(opj(folder, rec["label"]), "w") as F:
            _ = F.write(",".join(str(c) for c in flatten(rec["generators"])))

def make_psl2_input_data():
    folder = opj("..", "equations", "psl2_input_data")
    os.makedirs(folder, exist_ok=True)
    for rec in db.gps_sl2zhat_fine.search({}, ["label", "generators"]):
        with open(opj(folder, rec["label"]), "w") as F:
            _ = F.write(",".join(str(c) for c in flatten(rec["generators"])))

def make_todo():
    with open(opj("..", "equations", "todo.txt"), "w") as F:
        for label in db.gps_gl2zhat_fine.search({"contains_negative_one":True}, "label"):
            _ = F.write(label+"\n")

def prep_hyperelliptic():
    # Need to figure out which modular curves are on the "border" between canonical models and not (g=0,1 or hyperelliptic)
    with open(opj("..", "equations", "hyptodo.txt"), "w") as F:
        for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True, "genus":{"$gte":3, "$lte":17}}, ["label", "qbar_gonality_bounds"]):
            if rec["qbar_gonality_bounds"][0] == 2 and rec["qbar_gonality_bounds"][1] > 2:
                # possibly hyperelliptic
                _ = F.write(rec["label"] + "\n")

def get_relj_codomains():
    # Currently, the plan is to just run GetPrecHyp.m on lovelace, so we just use the output in the folder ishyp
    output_folder = opj("..", "equations", "cod")
    os.makedirs(output_folder, exist_ok=True)
    hyp_lookup = {}
    for label in os.listdir(opj("..", "equations", "ishyp")):
        with open(opj("..", "equations", "ishyp", label)) as F:
            hyp, prec = F.read().strip().split("|")
            hyp_lookup[label] = (hyp == "t")
    parents_conj = {}
    M = MatrixSpace(ZZ, 2)
    for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True, "genus": {"$gte": 3, "$lte": 24}}, ["label", "parents", "parents_conj", "qbar_gonality"]):
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
        if 3 <= int(g) <= 24 and not hyp_lookup.get(label):
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
    with open(opj("..", "equations", "codtodo.txt"), "w") as Ftodo:
        for cod, maxind in cods.items():
            _ = Ftodo.write(cod + "\n")
            with open(opj(output_folder, cod), "w") as F:
                _ = F.write(f"{cod}|{maxind}")
    with open(opj("..", "equations", "todo.txt"), "w") as Ftodo:
        for label in db.gps_gl2zhat_fine.search({"contains_negative_one":True}, "label"):
            if label not in cods:
                _ = Ftodo.write(label + "\n")

def prep_all():
    make_input_data()
    make_graphviz_files()
    make_picture_input()
    make_gonality_files()
    make_todo()
    prepare_rational_points()
    # Make tarball

def timing_statistics():
    with open("output") as F:
        timing_data = [line[1:] for line in F.read().strip().split("\n") if line.startswith("T")]
        by_label = defaultdict(list)
        for line in timing_data:
            label, line = line.split("|")
            by_label[label].append(line)
        start_re = re.compile("Starting (.*)")
        end_re = re.compile("Finished (.*) in (.*)")
        unfinished = {}
        unstarted = {}
        by_task = defaultdict(list)
        uby_task = defaultdict(list)
        for label, lines in by_label.items():
            started = [start_re.fullmatch(x) for x in lines]
            started = [m.group(1) for m in started if m is not None]
            finished = [end_re.fullmatch(x) for x in lines]
            timings = [float(m.group(2)) for m in finished if m is not None]
            finished = [m.group(1) for m in finished if m is not None]
            for task, t in zip(finished, timings):
                # 33 is to truncate the specific j-invariant in "computing rational points above j="
                by_task[task[:33]].append((t, label))
            UF = set(started).difference(set(finished))
            US = set(finished).difference(set(started))
            if UF:
                unfinished[label] = UF
                for task in UF:
                    uby_task[task[:33]].append(label)
            if US:
                unstarted[label] = US
    for task, data in by_task.items():
        times = [pair[0] for pair in data]
        level = [int(pair[1].split(".")[0]) for pair in data]
        genus = [int(pair[1].split(".")[2]) for pair in data]
        printtask = task + " "*(33-len(task))
        by_level = defaultdict(list)
        for N, t in zip(level, times):
            by_level[N].append(t)
        by_genus = defaultdict(list)
        for g, t in zip(genus, times):
            by_genus[g].append(t)

        ulevel = [int(label.split(".")[0]) for label in uby_task.get(task, [])]
        uby_level = Counter(ulevel)
        ugenus = [int(label.split(".")[2]) for label in uby_task.get(task, [])]
        uby_genus = Counter(ugenus)
        a = mean(times)
        b = median(times)
        c = std(times)
        d = max(times)
        e = len(times)
        f = len(uby_task.get(task, []))
        print(f"{printtask}       Mean ({a:5.2f}) Median ({b:5.2f}) Std ({c:5.2f}) Max ({d:6.2f}) OK ({e:<3}) Bad ({f})\n")
        for N in sorted(set(list(by_level) + list(uby_level))):
            if N in by_level:
                ts = by_level[N]
                a = mean(ts)
                b = median(ts)
                c = std(ts)
                d = max(ts)
                e = len(ts)
                f = uby_level.get(N, 0)
                print(f"{printtask} N={N:<3} Mean ({a:5.2f}) Median ({b:5.2f}) Std ({c:5.2f}) Max ({d:6.2f}) OK ({e:<3}) Bad ({f})")
            else:
                f = uby_level[N]
                print(f"{printtask} N={N:<3} {' '*61} Bad ({f})")
        print("")
        for g in sorted(set(list(by_genus) + list(uby_genus))):
            if g in by_genus:
                ts = by_genus[g]
                a = mean(ts)
                b = median(ts)
                c = std(ts)
                d = max(ts)
                e = len(ts)
                f = uby_genus.get(g, 0)
                print(f"{printtask} g={g:<3} Mean ({a:5.2f}) Median ({b:5.2f}) Std ({c:5.2f}) Max ({d:6.2f}) OK ({e:<3}) Bad ({f})")
            else:
                f = uby_genus[g]
                print(f"{printtask} g={g:<3} {' '*61} Bad ({f})")
        print("")
    return unfinished, by_task, uby_task

def get_gonalities(model_gonalities):
    P = get_lattice_poset()
    H = P._hasse_diagram
    gonalities = {P._element_to_vertex(rec["label"]): rec["q_gonality_bounds"] + rec["qbar_gonality_bounds"] for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":True}, ["label", "q_gonality_bounds", "qbar_gonality_bounds"])}
    for x, bounds in gonalities.items():
        for i in [0,2]:
            assert bounds[i+1] >= bounds[i]
    X1 = P._element_to_vertex("1.1.0.a.1")
    def index_genus(label):
        pieces = label.split(".")
        return int(pieces[1]), int(pieces[2])
    ig = {v: index_genus(P._vertex_to_element(v)) for v in H}
    recursive_ig = {}
    def castelnuovo_severi(x, gonalities, ig, rig, P, F, bars=[0,2]):
        """
        Attempts to rule out gonalities between low and high for a modular curve X
        using the Castelnuovo-Severi inequality

        Input:
        - gonalities -- current gonality bounds
        - ig -- the index and genus dictionary
        - rig -- the set of index-genus pairs dictionary for modular curves Y with X -> Y (indexed by x)
        - P -- the Poset
        - F -- the improvement output file
        - bars -- either [0,2], [0], or [2], governing whether both q and qbar done, or just one
        Output:
        - None, but updates gonalities[x] and prints to F if improvements possible
        """
        index, genus = ig[x]
        dg = defaultdict(list)
        for i, g in rig[x]:
            if i != index:
                dg[index // i].append(g)
        for bar in bars:
            low, high = gonalities[x][bar:bar+2]
            # See if we can increase the lower bound using maps to other modular curves
            for gon in range(low, high):
                # Try to rule out gon as a possible gonality using Castelnuovo–Severi
                if all(all((genus - d*g) / (d - 1) + 1 <= gon
                           for g in dg[d])
                       for d in dg if gcd(d, gon) == 1):
                    if gon > low:
                        _ = F.write(f"C|{bar}|{P._vertex_to_element(x)}|{gon}|C|{gon - low}\n")
                        gonalities[x][bar] = gon
                    break
            else:
                if high > low:
                    _ = F.write(f"C|{bar}|{P._vertex_to_element(x)}|{high}|C|{high - low}\n")
                    gonalities[x][bar] = high

    def get_bars(bounds):
        return ([] if bounds[0] == bounds[1] else [0]) + ([] if bounds[2] == bounds[3] else [2])
    # We record the changes so that we can write about them
    with open("gon_improvements.txt", "w") as F:
        # Import the gonalities from models
        for label, bounds in model_gonalities.items():
            x = P._element_to_vertex(label)
            for i in range(4):
                if bounds[i] * (-1)**i > gonalities[x][i] * (-1)**i:
                    _ = F.write(f"M|{i}|{label}|{bounds[i]}|M|{(bounds[i] - gonalities[x][i]) * (-1)**i}\n")
                    gonalities[x][i] = bounds[i]
            for i in [0,2]:
                assert gonalities[x][i+1] >= gonalities[x][i]

        for x in index_iterator(P, X1):
            index, genus = ig[x]
            recursive_ig[x] = set([ig[x]])
            for y in H.neighbors_in(x):
                recursive_ig[x].update(recursive_ig[y])
            bars = get_bars(gonalities[x])
            if bars:
                castelnuovo_severi(x, gonalities, ig, recursive_ig, P, F, bars)
        while True:
            # We alternate until no improvements are made, since gonality improvements can go either direction along maps
            improvements = 0
            for x in index_iterator(P, X1):
                for y in H.neighbors_in(x):
                    for bar in [1,3]:
                        # Update gonality upper bound: we can compose a map to y with a gonality map from y to P1 to get a gonality map from x to P1
                        # if X -> Y, gon(X) <= deg(pi)*gon(Y)
                        bound = gonalities[y][bar] * index // ig[y][0]
                        if bound < gonalities[x][bar]:
                            assert bound >= gonalities[x][bar-1]
                            _ = F.write(f"0|{bar}|{P._vertex_to_element(x)}|{bound}|{P._vertex_to_element(y)}|{gonalities[x][bar] - bound}\n")
                            improvements += 1
                            gonalities[x][bar] = bound
                        # if X -> Y, gon(X) >= gon(Y)
                        bound = gonalities[y][bar-1]
                        if bound > gonalities[x][bar-1]:
                            assert bound <= gonalities[x][bar]
                            _ = F.write(f"1|{bar-1}|{P._vertex_to_element(x)}|{bound}|{P._vertex_to_element(y)}|{bound - gonalities[x][bar-1]}\n")
                            improvements += 1
                            gonalities[x][bar-1] = bound
                            if bound < gonalities[x][bar]:
                                castelnuovo_severi(x, gonalities, ig, recursive_ig, P, F, [bar-1])
            print(f"{improvements} improvements made for gon(X) in X->Y")
            if improvements == 0:
                break
            improvements = 0
            # We iterate over x in a reverse order, and try to improve the gonality of y
            for x in index_iterator(P, X1, reverse=True):
                for y in H.neighbors_in(x):
                    for bar in [1,3]:
                        # if X -> Y, gon(Y) >= gon(X)/deg(pi)
                        bound = ceil(gonalities[x][bar-1] * ig[y][0] / index)
                        if bound > gonalities[y][bar-1]:
                            assert bound <= gonalities[y][bar]
                            _ = F.write(f"0|{bar-1}|{P._vertex_to_element(y)}|{bound}|{P._vertex_to_element(x)}|{bound - gonalities[y][bar-1]}\n")
                            improvements += 1
                            gonalities[y][bar-1] = bound
                            if bound < gonalities[y][bar]:
                                castelnuovo_severi(y, gonalities, ig, recursive_ig, P, F, [bar-1])
                        # if X -> Y, gon(Y) <= gon(X)
                        bound = gonalities[x][bar]
                        if bound < gonalities[y][bar]:
                            assert bound >= gonalities[y][bar-1]
                            _ = F.write(f"1|{bar}|{P._vertex_to_element(y)}|{bound}|{P._vertex_to_element(x)}|{gonalities[y][bar] - bound}\n")
                            improvements += 1
                            gonalities[y][bar] = bound
            print(f"{improvements} improvements made for gon(Y) in X->Y")
            if improvements == 0:
                break

    def package(gon):
        q_low, q_high, qbar_low, qbar_high = gon
        q = q_low if q_low == q_high else None
        qbar = qbar_low if qbar_low == qbar_high else None
        return q, qbar, (q_low, q_high), (qbar_low, qbar_high)
        #return f"{q}|{qbar}|{{{q_low},{q_high}}}|{{{qbar_low},{qbar_high}}}"
    return {P._vertex_to_element(v): package(gon) for (v, gon) in gonalities.items()}

def get_nf_lookup(pols):
    # All polynomials should be stored without spaces
    lookup = {}
    R = PolynomialRing(QQ, name="x")
    if ope("polreds.txt"):
        with open("polreds.txt") as F:
            for line in F:
                poly, nflabel, g, phi = line.strip().split("|")
                lookup[poly] = (nflabel, g, phi)
    save = False
    nf_lookup = {}
    for i, poly in enumerate(pols):
        if i and i % 1000 == 0:
            print(f"Creating nf lookup table: {i}/{len(pols)}")
        if poly not in lookup:
            save = True
            f = R(poly)
            K = NumberField(f, name='a')
            g = R(f.__pari__().polredabs())
            L = NumberField(g, name='b')
            phi = K.embeddings(L)[0]
            if g not in nf_lookup:
                nf_lookup[g] = db.nf_fields.lucky({"coeffs":[int(c) for c in g]}, "label")
                assert nf_lookup[g] is not None
            nflabel = nf_lookup[g]
            g = ",".join(str(c) for c in g)
            phi = ",".join(str(c) for c in phi(K.gen()))
            lookup[poly] = (nflabel, g, phi)
    if save:
        with open("polreds_tmp.txt", "w") as F:
            for poly, tup in lookup.items():
                _ = F.write("|".join((poly,) + tup) + "\n")
        os.rename("polreds_tmp.txt", "polreds.txt")
    return lookup

def get_model_points(rats, usps, jusps):
    # We need to do polredabs computations for cusps, which might take a while
    print("Creating nf lookup table")
    pols = set()
    for lines in rats.values():
        for line in lines:
            if line:
                pols.add(line.split("|")[0])
    for lines in jusps.values():
        for line in lines:
            toadd = line.split("|")[-1][1:-1].split(",")
            for f in toadd:
                pols.add(f)
    for lines in usps.values():
        for line in lines:
            pols.add(line.split("|")[0])
    nf_lookup = get_nf_lookup(pols)
    points = defaultdict(lambda: defaultdict(list))
    R = PolynomialRing(QQ, name="x")
    to_polredabs = {}
    print("Loading polynomials")
    for label, lines in rats.items():
        for out in lines:
            if not out: continue
            poly, j, model_type, coord = out.split("|")
            model_type = int(model_type)
            if poly == "x-1":
                points[label, "1.1.1.1", j][model_type].append(coord)
            else:
                nflabel, g, phi = nf_lookup[poly]
                points[label, nflabel, j][model_type].append(coord)

    cusps = defaultdict(lambda: defaultdict(list))
    phiD = {}
    def add_to_phiD(poly, i=None):
        nflabel, g, phi = nf_lookup[poly]
        if poly in phiD:
            phi = phiD[poly]
        else:
            K = NumberField(R(poly), name="a")
            L = NumberField(R([ZZ(c) for c in g.split(",")]), name="b")
            phi = K.hom([L([QQ(c) for c in phi.split(",")])])
            phiD[nflabel,g,phi] = phi
        if i is not None:
            phi = phi * K.change_names(f"a_{i}").structure()[0]
        return nflabel, phi.domain(), phi
    for i, (label, lines) in enumerate(usps.items()):
        if i and i%1000 == 0:
            print(f"usps {i}/{len(usps)}")
        for line in lines:
            if not line: continue
            poly, model_type, coord = line.split("|")
            # Skip model_type 0,5,8 since that will be handled in the jusps section
            if model_type not in "058":
                nflabel, K, phi = add_to_phiD(poly)
                coord = [K([QQ(c) for c in x.split(",")]) for x in coord.split(":")]
                coord = [phi(x) for x in coord]
                coord = ":".join(",".join(str(c) for c in list(x)) for x in coord)
                cusps[label, nflabel][model_type].append(coord)
    amatcher = re.compile(r"a_(\d+)")
    for i, (label, lines) in enumerate(jusps.items()):
        if i and i%1000 == 0:
            print(f"jusps {i}/{len(jusps)}")
        assert len(lines) == 1
        line = lines[0]
        data = line.split("|")
        model_type = data[0]
        coords, fields = data[-2:]
        if coords == "{}":
            # no cusps
            continue
        coords = coords[1:-1].split(",")
        fields = fields[1:-1].split(",")
        for coord in coords:
            m = amatcher.search(coord)
            if m:
                i = int(m.group(1))
                nflabel, K, phi = add_to_phiD(fields[i-1], i=i)
                coord = [K(c) for c in coord[1:-1].split(":")]
                coord = [phi(x) for x in coord]
                coord = ":".join(",".join(str(c) for c in list(x)) for x in coord)
            else:
                nflabel = "1.1.1.1"
                coord = coord[1:-1]
            cusps[label, nflabel][model_type].append(coord)
    return points, cusps

def write_models_maps(cans, planes, ghyps, jcusps, jfacs):
    def dontdisplay_str(s):
        return "t" if (len(s) > 100000) else "f"
    models = defaultdict(list)
    maps = defaultdict(list)
    can_type = {}
    # Check that P1s aren't included in models
    assert "1.1.0.a.1" not in cans and "8.2.0.a.1" not in cans
    for label, lines in cans.items():
        assert len(lines) == 1
        line = lines[0]
        nvar, can, model_type = line.split("|")
        assert model_type != "1"
        # encoding for model types (in the modcurve_models and modcurve_modelmaps schemas)
        # For a given modular curve, there should be at most one of each type of model in modcurve_models (since they're used as keys in modcurve_modelmaps)
        # 0: canonical (including plane models for nonhyperelliptic genus 3)
        # 1: only used in modelmaps for P^1; for the modular curve X(1), this indicates that the j-invariant is used as the coordinate (as opposed to type 3 where j-1728 is)
        # 2: plane model, including pointless conics but excluding nonhyperelliptic genus 3 (0) and elliptic curves (5)
        # 3: P^1, only used in modelmaps for j-1728
        # 4: P(4,6), only used in modelmaps for (E4,E6)
        # 5: elliptic or hyperelliptic over Q
        # 6: bielliptic (not yet implemented)
        # 7: double cover of a pointless conic
        # 8: the high dimensional smooth embeddings of geometrically hyperelliptic curves produced by FindModelOfXG
        # -1: other (currently unused)
        # -2: external plane model (e.g. Drew's optimized ones for X0(N))
        can_type[label] = model_type
        smooth = "t"
        dontdisplay = dontdisplay_str(can)
        models[label].append(f"{label}|{can}|{nvar}|{model_type}|{smooth}|{dontdisplay}\n")
    for label, lines in jcusps.items():
        assert len(lines) == 1
        line = lines[0]
        index = int(label.split(".")[1]) # coarse model, so psl2_index same as index
        if line.count("|") == 4:
            model_type, codomain, jmap, cuspcoords, cuspfields = line.split("|")
            assert codomain in models
            codomain_index = int(codomain.split(".")[1]) # coarse model, so psl2_index same as index
            degree = index // codomain_index
            toadd = [(str(degree), codomain, "0", jmap, r"\N", "t")]
        else:
            codomain = "1.1.0.a.1"
            model_type, jmap, cuspcoords, cuspfields = line.split("|")
            if label in jfacs:
                faclines = jfacs[label]
                toadd = []
                for facline in faclines:
                    codtype, jmap, leading, nfacs, jdegs = facline.split("|")
                    toadd.append((str(index), codomain, codtype, jmap, leading, "t"))
            else:
                toadd = [(str(index), codomain, "1", jmap, r"\N", "f")]
        assert model_type == "1" or label in models
        for degree, codomain, codtype, jmap, leading, factored in toadd:
            dontdisplay = dontdisplay_str(jmap)
            maps[label].append(f"{degree}|{label}|{model_type}|{codomain}|{codtype}|{jmap}|{leading}|{factored}|{dontdisplay}\n")

    triangular_nbs = [str(i*(i-1)//2) for i in range(1, 18)]
    for label, lines in planes.items():
        assert len(lines) == 1
        line = lines[0]
        plane, proj, nvar, smooth, alg = line.split("|") # Note that nvar is the number of variables in the domain of the projection
        dontdisplay = dontdisplay_str(plane)
        models[label].append(f"{label}|{{{plane}}}|3|2|{smooth}|{dontdisplay}\n")
        leading_coefficients = r"\N"
        factored = "f"
        dontdisplay = dontdisplay_str(proj)
        maps[label].append(f"1|{label}|{can_type[label]}|{label}|2|{{{proj}}}|{leading_coefficients}|{factored}|{dontdisplay}\n")

    for label, lines in ghyps.items():
        assert len(lines) == 1
        line = lines[0]
        if "|" in line:
            # Hyperelliptic model where we have the projection
            model, proj, nvar = line.split("|")
            leading_coefficients = r"\N"
            factored = "f"
            dontdisplay = dontdisplay_str(proj)
            maps[label].append(f"1|{label}|{can_type[label]}|{label}|5|{{{proj}}}|{leading_coefficients}|{factored}|{dontdisplay}\n")
        else:
            model = line
        if "W" in model:
            model_type = 7 # geometrically hyperelliptic
            nvars = 4
        else:
            model_type = 5 # actually hyperelliptic
            nvars = 3
        smooth = "t"
        dontdisplay = dontdisplay_str(model)
        models[label].append(f"{label}|{model}|{nvars}|{model_type}|{smooth}|{dontdisplay}\n")

    def sort_key(label):
        # only works on coarse labels, but that's okay here
        return [(int(c) if c.isdigit() else class_to_int(c)) for c in label.split(".")]
    with open("modcurve_models.txt", "w") as Fmodels:
        _ = Fmodels.write("modcurve|equation|number_variables|model_type|smooth|dont_display\ntext|text[]|smallint|smallint|boolean|boolean\n\n")
        for label in sorted(models, key=sort_key):
            _ = Fmodels.write("".join(models[label]))
    with open("modcurve_modelmaps.txt", "w") as Fmaps:
        Fmaps.write("degree|domain_label|domain_model_type|codomain_label|codomain_model_type|coordinates|leading_coefficients|factored|dont_display\ninteger|text|smallint|text|smallint|text[]|text[]|boolean|boolean\n\n")
        for label in sorted(maps, key=sort_key):
            _ = Fmaps.write("".join(maps[label]))

def transform_label(old_label):
    if old_label.count(".") == 4:
        return old_label
    #Old: M.j.g.a.m-N.n
    coarse, fine = old_label.split("-")
    M, j, g, a, m = coarse.split(".")
    i = 2*int(j)
    N, n = fine.split(".")
    # New: N.i.g-M.a.m.n
    return f"{N}.{i}.{g}-{M}.{a}.{m}.{n}"

def untransform_label(new_label):
    if new_label.count(".") == 4:
        return new_label
    # New: N.i.g-M.a.m.n
    fine, coarse = new_label.split("-")
    N, i, g = fine.split(".")
    j = int(j)//2
    M, a, m, n = coarse.split(".")
    #Old: M.j.g.a.m-N.n
    return f"{M}.{j}.{g}.{a}.{m}-{N}-{n}"

def to_coarse_label(label):
    # Work around broken coarse_label column
    if label.count(".") == 4:
        return label
    # N.i.g-M.a.m.n
    fine, coarse = label.split("-")
    N, i, g = fine.split(".")
    j = int(i)//2
    M, a, m, n = coarse.split(".")
    return f"{M}.{j}.{g}.{a}.{m}"

def create_db_uploads(input_file="output"):
    data = defaultdict(lambda: defaultdict(list))
    with open(input_file) as F:
        for line in F:
            label, out = line.strip().split("|", 1)
            if not out: continue
            code, label = label[0], label[1:]
            data[code][label].append(out)

    # Propogate gonalities
    assert all(len(gon) == 1 for gon in data["G"].values())
    data["G"] = {label: [int(g) for g in gon[0].split(",")] for label,gon in data["G"].items()}
    gonalities = get_gonalities(data["G"])

    # Construct modcurve_points
    model_points, cusps = get_model_points(data["R"], data["U"], data["J"])
    print("Model points loaded")
    gpdata = load_gl2zhat_rational_data()
    gpcuspdata = load_gl2zhat_cusp_data()
    print("Group data loaded")

    def write_dict(D):
        if isinstance(D, str): return D # \N
        D = dict(D) # might be a defaultdict
        parts = []
        for modtype, coords in D.items():
            coords = str(coords).replace(" ", "").replace("'", '"')
            parts.append(f'"{modtype}":{coords}')
        return "{" + ",".join(parts) + "}"
    def get_card(coords):
        if coords == r"\N":
            return r"\N"
        # canonical, embedded, Weierstrass
        for model_type in "085":
            if model_type in coords:
                return len(coords[model_type])
        return r"\N"
    num_pts = defaultdict(int)
    # cm_Elabel = {rec["cm"]: rec["lmfdb_label"] for rec in db.ec_curvedata.search({"cm":{"$ne": 0}}, ["cm", "lmfdb_label"], one_per=["cm"])}
    cm_Elabel = {
        '-3': '27.a3',
        '-4': '32.a3',
        '-7': '49.a2',
        '-8': '256.a1',
        '-11': '121.b1',
        '-12': '36.a1',
        '-16': '32.a1',
        '-19': '361.a1',
        '-27': '27.a1',
        '-28': '49.a1',
        '-43': '1849.b1',
        '-67': '4489.b1',
        '-163': '26569.a1'
    }
    with open("modcurve_points.txt", "w") as Fout:
        _ = Fout.write("curve_label|curve_name|curve_level|curve_genus|curve_index|degree|residue_field|jorig|jinv|j_field|j_height|cm|quo_info|Elabel|isolated|conductor_norm|ainvs|coordinates|cusp|cardinality\ntext|text|integer|integer|integer|smallint|text|text|text|text|double precision|smallint|smallint[]|text|smallint|numeric|text|jsonb|boolean|integer\n\n")
        # Get total number of points to add
        with open("allpoints.txt") as F:
            for total, _ in enumerate(F,1):
                pass
        with open("allpoints.txt") as F:
            for ctr, line in enumerate(F):
                if ctr and ctr % 10000 == 0:
                    print(f"{ctr}/{total}")
                plabel, degree, field_of_definition, jorig, jinv, jfield, j_height, cm, Elabel, isolated, conductor_norm, ainvs = line.strip().split("|")
                gdat = gpdata[plabel]
                g, ind, level = gdat["genus"], gdat["index"], gdat["level"]
                gonlow = gonalities[to_coarse_label(plabel)][2][0]
                rank, simp, dims = gdat["rank"], gdat["simple"], gdat["dims"]
                name = gdat["name"]
                if name is None:
                    name = r"\N"
                # we can recompute isolated based on new gonalities
                if isolated in "01":
                    isolated = is_isolated(int(degree), g, rank, gonlow, simp, dims)
                if ainvs == "?":
                    ainvs = r"\N"
                # For cm points on coarse curves, we can often improve the ellipic curve conductor from the one propogated from the maximal point
                if degree == "1" and cm != "0" and "-" not in plabel:
                    Elabel = cm_Elabel[cm]
                jlookup = jinv if jorig == r"\N" else jorig
                coords = model_points.get((plabel, field_of_definition, jlookup), r"\N")
                card = get_card(coords)
                if degree == "1":
                    if card == r"\N":
                        num_pts[plabel] += 1 # There is at least one point over this j-invariant
                    else:
                        num_pts[plabel] += card
                _ = Fout.write("|".join([plabel, name, str(level), str(g), str(ind), degree, field_of_definition, jorig, jinv, jfield, j_height, cm, r"\N", Elabel, isolated, conductor_norm, ainvs, write_dict(coords), "f", str(card)]) + "\n")
        for (plabel, nflabel), coords in cusps.items():
            degree = nflabel.split(".")[0]
            gdat = gpcuspdata[plabel]
            g = gdat["genus"]
            ind = gdat["index"]
            level = gdat["level"]
            rank = gdat["rank"]
            simp = gdat["simple"]
            name = gdat["name"]
            if name is None:
                name = r"\N"
            card = get_card(coords)
            if degree == "1":
                if card == r"\N":
                    card = gdat["rational_cusps"]
                elif card != gdat["rational_cusps"]:
                    print(f"Rational cusp cardinality mismatch for {plabel} ({card} != {gdat['rational_cusps']})")
                num_pts[plabel] += card
            _ = Fout.write("|".join([plabel, name, str(level), str(g), str(ind), degree, nflabel, r"\N", r"\N", "1.1.1.1", "0", "0", r"\N", r"\N", r"\N", r"\N", r"\N", write_dict(coords), "t", str(card)]) + "\n")

    write_models_maps(data["C"], data["P"], data["H"], data["J"], data["F"])

    # Get lattice_models and lattice_x
    assert all(len(D) == 1 for D in data["L"].values())
    data["L"] = {label: L[0] for (label, L) in data["L"].items()}

    with open("gps_gl2zhat_fine.update", "w") as F:
        # TODO: May also want to upload number_rational_points
        _ = F.write("label|q_gonality|qbar_gonality|q_gonality_bounds|qbar_gonality_bounds|lattice_labels|lattice_x|num_known_degree1_points\ntext|integer|integer|integer[]|integer[]|text[]|integer[]|integer\n\n")
        default = r"\N|\N"
        for label, gon in gonalities.items():
            q, qbar, qbnd, qbarbnd = gon
            if q is None: q = r"\N"
            if qbar is None: qbar = r"\N"
            qbnd = "{%s,%s}" % qbnd
            qbarbnd = "{%s, %s}" % qbarbnd
            card = num_pts.get(label, 0)
            _ = F.write(f"{label}|{q}|{qbar}|{qbnd}|{qbarbnd}|{data['L'].get(label, default)}|{card}\n")

def update_lattice_only():
    folder = opj("..", "equations", "graphviz_out")
    with open("lattice.update", "w") as Fout:
        _ = Fout.write("label|lattice_labels|lattice_x\ntext|text[]|integer[]\n\n")
        for label in os.listdir(folder):
            with open(opj(folder, label)) as F:
                Fout.write(label + "|" + F.read().strip() + "\n")
    db.gps_gl2zhat_fine.update_from_file("lattice.update")

def fix_dollars():
    kinds = set()
    lvars = "xyzwtuvrsabcdefghiklmnopqj"
    with open("output") as F:
        with open("output_fixed", "w") as Fout:
            for line in F:
                if line[0] != "E" and "$" in line:
                    kinds.add(line[0])
                    for m in range(23,0,-1):
                        line = line.replace(f"$.{m}", lvars[m])
                    assert "$" not in line
                _ = Fout.write(line)
    return kinds

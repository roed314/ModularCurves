
import os
import time
import re
import sys
from collections import defaultdict
from sage.misc.cachefunc import cached_function
from sage.all import ZZ, QQ, PolynomialRing, NumberField, DiGraph
from sage.combinat.posets.posets import FinitePoset
from sage.misc.misc import cputime, walltime

opj = os.path.join
ope = os.path.exists
sys.path.append(os.path.expanduser(opj("~", "lmfdb")))
from lmfdb import db
dbtable = db.gps_gl2zhat_fine

@cached_function
def qlevels():
    return [n for n in range(71,400) if ZZ(n).is_prime_power()]

def lattice_query():
    # Currently, dbtable contains more info than we're going to include on the website, so we trim it here
    return {"contains_negative_one": True,
            "$or": [{"level": {"$lte": 70}},
                    {"level": {"$in": qlevels()}}]}

def model_query():
    return {"contains_negative_one": True,
            "$or": [{"level": {"$lt": 24}},
                    {"level": {"$lte": 70}, "genus": {"$lte": 14}}]}
def rat_query():
    return {"level": {"$lte": 70}}

@cached_function
def rational_poset_query():
    # We need to also include prime levels since ec_nfcurve has prime level galois_images, and many of the hand-curated low-degree points are on curves of prime level
    ecnf_primes = sorted(set(sum(db.ec_nfcurves.distinct('nonmax_primes'), [])))
    return {"$and": [
        {"$or": [{"level": {"$lte": 70}},
                 {"level": {"$in": qlevels()}}]},
        #{"$or": [{"pointless": False}, {"pointless": {"$exists":False}}, {"level": {"$in": ecnf_primes}}]},
    ]}

def inbox(label):
    """
    Whether this label lies within the box where we're running the model calculations
    """
    N, i, g = label.split(".")[:3]
    N = int(N)
    g = int(g)
    if N < 24:
        return g <= 24
    if N <= 70:
        return g <= 14
    return False
    #if N <120:
    #    return g <= 14
    #return g <= 6

def psl2_query():
    # This doesn't include the test for containing negative one since that column isn't there yet.
    return {"$or": [
        {"level": {"$lte": 70}},
        {"level": {"$in": qlevels()}},
        {"genus": {"$lte": 24}}]}

def pslbox(label):
    """
    Whether this sl2-label can show up as a psl2label (and thus needed for pictures)
    """
    if "-" in label:
        return False
    N, i, g = label.split(".")[:3]
    N = ZZ(N)
    g = int(g)
    return N <= 70 or N.is_prime_power() or g <= 24

@cached_function
def get_lattice_poset():
    t0 = walltime()
    R = []
    for rec in dbtable.search(lattice_query(), ["label", "parents"]):
        for olabel in rec["parents"]:
            R.append([olabel, rec["label"]]) # Use backward direction so that breadth first search is faster
    print(f"DB data loaded in {walltime() - t0:.2f}s")
    t0 = cputime()
    D = DiGraph()
    D.add_edges(R, loops=False)
    print(f"Edges added to graph in {cputime() - t0:.2f}s")
    t0 = cputime()
    P = FinitePoset(D)
    print(f"Poset created in {cputime() - t0:.2f}s")
    return P

@cached_function
def get_rational_poset():
    # The poset of modular curves that might have rational points, omitting X(1)
    t0 = walltime()
    nodes = []
    R = []
    for rec in dbtable.search(rational_poset_query(), ["label", "parents", "coarse_label"], silent=True):
        if rec["label"] == "1.1.0.a.1": continue
        nodes.append(rec["label"])
        parents = [label for label in rec["parents"] if label != "1.1.0.a.1"]
        if rec["label"] != to_coarse_label(rec["label"]) and to_coarse_label(rec["label"]) != "1.1.0.a.1":
            parents += [to_coarse_label(rec["label"])]
        for olabel in parents:
            R.append([rec["label"], olabel]) # note that this is the opposite direction of edges from lattice_poset
    print(f"DB data loaded in {walltime() - t0:.2f}s")
    t0 = cputime()
    D = DiGraph([nodes, R], format='vertices_and_edges')
    print(f"Edges added to graph in {cputime() - t0:.2f}s")
    t0 = cputime()
    P = FinitePoset(D)
    print(f"Poset created in {cputime() - t0:.2f}s")
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

def load_gl2zhat_rational_data():
    return {rec["label"]: rec for rec in db.gps_gl2zhat_tmp.search(rational_poset_query(), ["label", "genus", "simple", "rank", "dims", "name", "level", "index", "q_gonality_bounds", "coarse_label"], silent=True)}

def to_coarse_label(label):
    if label.count(".") == 4:
        return label
    # N.i.g-M.a.m.n
    fine, coarse = label.split("-")
    N, i, g = fine.split(".")
    j = int(i)//2
    M, a, m, n = coarse.split(".")
    return f"{M}.{j}.{g}.{a}.{m}"

def get_output_data():
    for i in range(3):
        fname = f"output{i}"
        if ope(fname):
            with open(fname) as F:
                for line in F:
                    yield line

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

def load_ecq_data(cm_data_file):
    print("Loading CM data over Q...", end="")
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
    print(f" done in {walltime() - t0:.2f}s")
    print("Loading modm_images from ec_curvedata...", end="")
    sys.stdout.flush()
    t0 = walltime()

    for rec in db.ec_curvedata.search({}, ["lmfdb_label", "jinv", "cm", "conductor", "modm_images", "ainvs"], silent=True):
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
    print(f" done in {walltime() - t0:.2f}s")
    return ecq_db_data

def load_ecnf_data(fname="ecnf_data.txt"):
    # Galois images are stored for NF curves using Sutherland labels
    t0 = time.time()
    from_Slabel = {
        rec["Slabel"] : rec["label"]
        for rec in dbtable.search(
                {"Slabel": {"$exists":True}},
                ["Slabel", "label"],
                silent=True,
        )
    }
    print(f"Constructed Sutherland label lookup table in {time.time() - t0:.2f}s")

    t0 = time.time()
    with open(fname) as F:
        for line in F:
            Slabels, degree, field_of_definition, jorig, jinv, jfield, j_height, cm, Elabel, conductor_norm, ainvs = line.strip().split("|")
            for Slabel in Slabels.split(","):
                if not ("[" in Slabel or S_LABEL_RE.fullmatch(Slabel)):
                    print("Warning: invalid Slabel", Slabel)
                if Slabel in from_Slabel:
                    label = from_Slabel[Slabel]
                    yield label, int(degree), field_of_definition, jorig, jinv, jfield, j_height, int(cm), Elabel, False, conductor_norm, ainvs
    print(f"Loaded ECNF data from file in {time.time() - t0:.2f}s")

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
                    field_labels.add(pieces[2].strip())
                    field_labels.add(pieces[4].strip())

    nfs, sub_lookup, embeddings = load_nf_data(list(field_labels))

    ans = []
    query = rat_query()
    query["name"] = {"$like": "X0%"}
    X0s = {rec["name"]: rec["label"] for rec in dbtable.search(query, ["name", "label"], silent=True)}
    RSZB_lookup = {rec["RSZBlabel"]: rec["label"] for rec in dbtable.search({"name": {"$exists": True}, "RSZBlabel": {"$exists":True}}, ["label", "RSZBlabel"])}
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
        #if level >= 24: continue
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

def trim_modm_images(images):
    """
    Takes partially defined labels from the modm_images column of ec_curvedata and
    only keeps fully-defined images that are maximal (for level-divisibility)
    """
    #images = [label for label in images if "?" not in label and int(label.split(".")[0]) < 24]
    images = [label for label in images if "?" not in label]
    Ns = [int(label.split(".")[0]) for label in images]
    locs = [i for i in range(len(Ns)) if not any(Ns[j] % Ns[i] == 0 for j in range(len(Ns)) if i != j)]
    return [images[i] for i in locs]

def get_j_height(jinv, j_field, nfs):
    K = nfs[j_field]
    j = [QQ(c) for c in jinv.split(",")]
    j += [0] * (K.degree() - len(j))
    j = K(j)
    return j.global_height()

def load_nf_data(field_labels=None):
    print("Loading nf data...")
    t0 = time.time()
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

    print(f"Constructed number field lookup tables in {time.time() - t0:.2f}s")
    return nfs, sub_lookup, embeddings

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

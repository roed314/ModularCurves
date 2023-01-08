
import os
import sys
from collections import defaultdict
from sage.misc.cachefunc import cached_function
from sage.all import ZZ, DiGraph
from sage.combinat.posets.posets import FinitePoset
from sage.misc.misc import cputime, walltime

opj = os.path.join
ope = os.path.exists
sys.path.append(os.path.expanduser(opj("~", "lmfdb")))
from lmfdb import db
dbtable = db.gps_gl2zhat_tmp

def lattice_query():
    # Currently, dbtable contains more info than we're going to include on the website, so we trim it here
    qlevels = [n for n in range(71,400) if ZZ(n).is_prime_power()]
    return {"contains_negative_one": True,
            "$or": [{"level": {"$lte": 70}},
                    {"level": {"$in": qlevels}}]}

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
                 {"level": {"$in": qlevels}}]},
        {"$or": [{"pointless": False}, {"pointless": None}, {"level": {"$in": ecnf_primes}}]}]}

@cached_function
def get_lattice_poset():
    t0 = walltime()
    R = []
    for rec in dbtable.search(lattice_query(), ["label", "parents"]):
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
    return {rec["label"]: rec for rec in dbtable.search(rational_poset_query(), ["label", "genus", "simple", "rank", "dims", "name", "level", "index", "q_gonality_bounds", "coarse_label"], silent=True)}

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

def get_output_data():
    for i in range(3):
        fname = f"output{i}"
        if ope(fname):
            with open(fname) as F:
                for line in F:
                    yield line

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

def pslbox(label):
    """
    Whether this sl2-label can show up as a psl2label (and thus needed for pictures)
    """
    if "-" in label:
        return False
    N = label.split(".")[0]
    N = ZZ(N)
    return N <= 70 or N.is_prime_power()

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


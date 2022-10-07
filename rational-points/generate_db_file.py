# Can be run from Sage after executing `from lmfdb import db` using %attach
import os
import re
from collections import defaultdict, Counter
from sage.all import QQ, NumberField, PolynomialRing

S_LABEL_RE = re.compile(r"^(\d+)(G|B|Cs|Cn|Ns|Nn|A4|S4|A5)(\.\d+){0,3}$")
LABEL_RE = re.compile(r"^\d+\.\d+\.\d+\.\d+$")
QQ_RE = re.compile(r"^-?\d+(/\d+)?$")
ZZ_RE = re.compile(r"^(-?\d+)|\\N$")
QQ_LIST_RE = re.compile(r"^-?\d+(/\d+)?(,-?\d+(/\d+)?)*$") # can't be empty
NN_LIST_RE = re.compile(r"^(\d+(,\s*\d+)*)?$") # can be empty


def load_points_files(data_folder):
    ans = []
    X0s = {rec["name"]: rec["label"] for rec in db.gps_gl2zhat_test.search({"name": {"$like": "X0%"}}, ["name", "label"], silent=True)}
    skipped = set()
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
                    name = label = pieces[0].strip()
                    if label.startswith("X0"):
                        label = X0s.get(label)
                        if label is None:
                            # We haven't added X0(56) yet....
                            if name not in skipped:
                                print(f"Skipping name {name}")
                                skipped.add(name)
                            continue
                    field_of_definition = pieces[2].strip()
                    degree = field_of_definition.split(".")[0]
                    jinv = pieces[3].replace(" ", "").replace("[", "").replace("]", "")
                    field_of_j = pieces[4].strip()
                    jorig = r"\N" if field_of_j in ["1.1.1.1", field_of_definition] else None
                    cm = pieces[6].strip()
                    quo_info = pieces[7].strip().replace("[", "{").replace("]", "}")
                    assert LABEL_RE.match(label), f"Invalid curve label {label}"
                    assert ZZ_RE.match(degree), f"Invalid degree {degree} for {label}"
                    assert LABEL_RE.match(field_of_definition), f"Invalid field of definition {field_of_definition} for {label}"
                    assert QQ_LIST_RE.match(jinv), f"Invalid j-invariant {jinv} for {label}"
                    assert LABEL_RE.match(field_of_j), f"Invalid field of j {field_of_j} for {label}"
                    assert ZZ_RE.match(cm), f"Invalid CM discriminant {cm} for {label}"
                    assert quo_info == r"\N" or NN_LIST_RE.match(quo_info[1:-1]), f"Invalid quotient information {quo_info} for {label}"
                    ans.append((label, int(degree), field_of_definition, jorig, jinv, field_of_j, cm, quo_info, r"\N", True, r"\N"))
    return ans

def generate_db_files(data_folder):
    lit_data = load_points_files(data_folder)
    lit_fields = sorted(set([datum[2] for datum in lit_data]))
    print("Loaded tables from files")

    # Galois images are stored for NF curves using Sutherland labels
    from_Slabel = {
        rec["Slabel"] : rec["label"]
        for rec in db.gps_gl2zhat_test.search(
                {"Slabel": {"$exists":True}},
                ["Slabel", "label"],
                silent=True,
        )
    }
    print("Constructed Sutherland label lookup table")

    R = PolynomialRing(QQ, 'x')
    field_data = list(db.nf_fields.search({"label": {"$in": db.ec_nfcurves.distinct("field_label") + lit_fields}},
                                          ["label", "coeffs", "subfields", "degree", "disc_abs"], silent=True))
    subs = [[int(c) for c in sub.split(".")] for sub in set(sum((rec["subfields"] for rec in field_data), []))]
    sub_data = list(db.nf_fields.search({"$or": [{"coeffs": sub} for sub in subs]}, ["degree", "disc_abs", "label", "coeffs"], silent=True))
    if len(subs) != len(sub_data):
        raise RuntimeError("Sub not labeled or discriminant clash")
    sub_lookup = {(rec["degree"], rec["disc_abs"]) : (rec["label"], R(rec["coeffs"])) for rec in sub_data}
    by_coeffs = {tuple(rec["coeffs"]): rec["label"] for rec in sub_data}
    sub_lookup[1, 1] = ("1.1.1.1", R.gen() - 1)
    nfs = {}
    embeddings = {}
    nf_subs = defaultdict(dict)
    for rec in field_data:
        f = R(rec["coeffs"])
        nfs[rec["label"]] = L = NumberField(f, 'a')
        sub_lookup[rec["degree"], rec["disc_abs"]] = (rec["label"], f)
        for sub in rec["subfields"]:
            sub = [ZZ(c) for c in sub.split(".")]
            g = R(sub)
            embeddings[by_coeffs[tuple(sub)], rec["label"]] = g.roots(L, multiplicities=False)[0]
    def get_j_height(jinv, j_field):
        K = nfs[j_field]
        j = [QQ(c) for c in jinv.split(",")]
        j += [0] * (K.degree() - len(j))
        j = K(j)
        return j.global_height()

    print("Constructed number field lookup tables")

    immediate_parents = {}
    gpdata = {}
    for rec in db.gps_gl2zhat_test.search({"level": {"$ne": 1}}, ["label", "parents", "contains_negative_one", "genus", "gonality_bounds", "simple", "rank", "name", "level", "index"], silent=True):
        immediate_parents[rec["label"]] = [x for x in rec["parents"] if x.split(".")[0] != "1"]
        gpdata[rec["label"]] = rec

    all_parents = defaultdict(list)
    for k in sorted(immediate_parents,
                    key=lambda x: [int(c) for c in x.split(".")]):
        all_parents[k] = sorted(
            set(
                immediate_parents[k]
                + sum([all_parents[j] for j in immediate_parents[k]], [])
            ),
            key=lambda x: [int(c) for c in x.split(".")]
        )
    print("Constructed GL(2, Zhat) lattice table")

    skipped = set()
    ecq_db_data = []
    for rec in db.ec_curvedata.search({}, ["elladic_images", "lmfdb_label", "ainvs", "jinv", "cm", "conductor"], silent=True):
        for label in rec["elladic_images"]:
            if label not in all_parents:
                # Don't have the label yet
                # This is unfortunate, since we can thus miss points of lower level coming from this curve
                if label not in skipped:
                    print(f"Skipping elladic image {label}")
                    skipped.add(label)
                continue
            Elabel = rec["lmfdb_label"]
            if rec["jinv"][1] == 1:
                jinv = str(rec["jinv"][0])
            else:
                jinv = "%s/%s" % tuple(rec["jinv"])
            ecq_db_data.append((label, 1, "1.1.1.1", r"\N", jinv, "1.1.1.1", rec["cm"], r"\N", Elabel, False, str(rec["conductor"])))
    print("Loaded elliptic curves over Q")

    ecnf_db_data = []
    total = db.ec_nfcurves.count()
    for progress, rec in enumerate(db.ec_nfcurves.search({}, ["galois_images", "degree", "field_label", "jinv", "cm", "label", "conductor_norm"], silent=True)):
        if progress and progress % 10000 == 0:
            print(f"ECNF: {progress}/{total}")
        if not rec["galois_images"]:
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
        for Slabel in rec["galois_images"]:
            if "[" in Slabel: # these have nonsurjective determinant
                continue
            p = int(S_LABEL_RE.fullmatch(Slabel).group(1))
            if p > 127: # Don't have level larger than this yet
                continue
            #if Slabel == "2C2": # broken label from an old mistake
            #    Slabel = "2B"
            #elif Slabel == "3C2.1.1": # broken label from an old mistake
            #    Slabel = "3B.1.1"
            #elif Slabel == "7Cs2": # broken label from an old mistake; not sure what's right
            #    continue
            if Slabel not in from_Slabel:
                if Slabel not in skipped:
                    print(f"Skipping Slabel {Slabel}")
                    skipped.add(Slabel)
                continue
            label = from_Slabel[Slabel]
            Elabel = rec["label"]
            ecnf_db_data.append((label, rec["degree"], rec["field_label"], jorig, jinv, jfield, rec["cm"], r"\N", Elabel, False, str(rec["conductor_norm"])))
    print("Loaded elliptic curves over number fields")

    # Check for overlap as we add points
    jinvs_seen = defaultdict(set)
    point_counts = defaultdict(Counter)
    # Things to add: isolated, coordinates in terms of model, LMFDB curve label (when not containing -1
    with open(os.path.join(data_folder, "modcurve_ratpoints.txt"), "w") as F:
        _ = F.write("curve_label|curve_name|curve_level|curve_genus|curve_index|degree|residue_field|jorig|jinv|j_field|j_height|cm|quo_info|Elabel|isolated|conductor_norm\ntext|text|integer|integer|integer|smallint|text|text|text|text|double precision|smallint|smallint[]|text|smallint|bigint\n\n")
        for ctr, (label, degree, field_of_definition, jorig, jinv, field_of_j, cm, quo_info, Elabel, known_isolated, conductor_norm) in enumerate(ecq_db_data + ecnf_db_data + lit_data):
            if ctr and ctr % 10000 == 0:
                print(f"{ctr}/{len(ecq_db_data) + len(ecnf_db_data) + len(lit_data)}")
            for plabel in [label] + all_parents[label]:
                if (field_of_j, jinv) not in jinvs_seen[plabel]:
                    jinvs_seen[plabel].add((field_of_j, jinv))
                    point_counts[plabel][degree] += 1
                    if jorig is None:
                        # Recover the j-invariant in the residue field from our chosen embedding.
                        K = nfs[field_of_j]
                        j = [QQ(c) for c in jinv.split(",")]
                        j += [0] * (K.degree() - len(j))
                        j = K(j)
                        L = nfs[field_of_definition]
                        root = embeddings[field_of_j, field_of_definition]
                        emb = K.hom([root])
                        jorig = ",".join(str(c) for c in list(emb(j)))
                    j_height = get_j_height(jinv, field_of_j)
                    gdat = gpdata[plabel]
                    g = gdat["genus"]
                    ind = gdat["index"]
                    level = gdat["level"]
                    gonlow = gdat["gonality_bounds"][0]
                    rank = gdat["rank"]
                    simp = gdat["simple"]
                    name = gdat["name"]
                    # We encode the isolatedness in a small integer, p + a, where
                    # p = 3,0,-3 for P1 isolated/unknown/parameterized and
                    # a = 1,0,-1 for AV isolated/unknown/parameterized
                    # 4 = isolated (both P1 isolated and AV isolated)
                    # 0 = unknown for both
                    # -4 = both P1 and AV parameterized
                    if label == plabel and known_isolated: # both AV and P1
                        isolated = "4"
                    elif degree == 1:
                        if g == 0:
                            # Always P1 parameterized and AV isolated
                            isolated = "-2"
                        elif g == 1 and rank > 0:
                            # Always P1 isolated and AV parameterized
                            isolated = "2"
                        else:
                            isolated = "4"
                    elif degree < QQ(gonlow) / 2 or degree < gonlow and (rank == 0 or simp and degree < g):
                        isolated = "4"
                    elif degree > g:
                        # Always P1 parameterized; AV parameterized if and only if rank positive
                        if rank > 0:
                            isolated = "-4"
                        else:
                            isolated = "-2"
                    elif degree == g and rank > 0:
                        isolated = "-1" # AV parameterized; can compute if P1 parameterized by Riemann Roch with a model
                    else:
                        if rank == 0 or degree <= min(dims): # for second part, using degree < g
                            # Actually only need to check the minimum of the dimensions where the rank is positive
                            # Always AV isolated; can try to computed whether P1 parameterized by Riemann roch
                            isolated = "1"
                        else:
                            isolated = "0"
                    # Construct the divisor given by the galois orbit on the Q-curve, then compute Dimension(RiemannRochSpace(D)).  If dim > 1 then P1 parameterized, otherwise not.  If rank = 0 then not AV-parameterized
                    _ = F.write("|".join([plabel, name, str(level), str(g), str(ind), str(degree), field_of_definition, jorig, jinv, field_of_j, str(j_height), str(cm), quo_info, Elabel, isolated, conductor_norm]) + "\n")
    with open(os.path.join(data_folder, "modcurve_ptcount_update.txt"), "w") as F:
        _ = F.write("label|" + "|".join(f"known_degree{d}_points" for d in range(1,7)) + "\ntext" + "|smallint"*6 + "\n\n")
        for label, cnts in point_counts.items():
            _ = F.write(label + "|" + "|".join(str(cnts[d]) for d in range(1, 7)) + "\n")

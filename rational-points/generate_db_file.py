# Can be run from Sage after executing `from lmfdb import db` using %attach
import os
import re
from collections import defaultdict, Counter
from sage.all import QQ, NumberField, PolynomialRing

S_LABEL_RE = re.compile(r"(\d+)(G|B|Cs|Cn|Ns|Nn|A4|S4|A5)(\.\d+){0,3}")

def load_points_files(data_folder):
    ans = []
    X0s = {rec["name"]: rec["label"] for rec in db.gps_gl2zhat_test.search({"name": {"$like": "X0%"}}, ["name", "label"])}
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
                            print(f"Skipping name {name}")
                            continue
                    field_of_definition = pieces[2].strip()
                    degree = field_of_definition.split(".")[0]
                    jinv = pieces[3].replace(" ", "").replace("[", "").replace("]", "")
                    field_of_j = pieces[4].strip()
                    cm = pieces[6].strip()
                    quo_info = pieces[7].strip().replace("[", "{").replace("]", "}")
                    ans.append((label, int(degree), field_of_definition, jinv, field_of_j, cm, quo_info, r"\N", True))
    return ans

def generate_db_files(data_folder):
    # Galois images are stored for NF curves using Sutherland labels
    from_Slabel = {
        rec["Slabel"] : rec["label"]
        for rec in db.gps_gl2zhat_test.search(
                {"Slabel": {"$exists":True}},
                ["Slabel", "label"]
        )
    }
    print("Constructed Sutherland label lookup table")

    R = PolynomialRing(QQ, 'x')
    field_data = list(db.nf_fields.search({"label": {"$in": db.ec_nfcurves.distinct("field_label")}},
                                          ["label", "coeffs", "subfields", "degree", "disc_abs"]))
    subs = [[int(c) for c in sub.split(".")] for sub in set(sum((rec["subfields"] for rec in field_data), []))]
    sub_lookup = {(rec["degree"], rec["disc_abs"]) : (rec["label"], R(rec["coeffs"])) for rec in db.nf_fields.search({"$or": [{"coeffs": sub} for sub in subs]}, ["degree", "disc_abs", "label", "coeffs"])}
    if len(subs) != len(sub_lookup):
        raise RuntimeError("Sub not labeled or discriminant clash")
    sub_lookup[1, 1] = ("1.1.1.1", x - 1)
    nfs = {}
    nf_subs = defaultdict(dict)
    for rec in field_data:
        f = R(rec["coeffs"])
        nfs[rec["label"]] = NumberField(f, 'a')
        sub_lookup[rec["degree"], rec["disc_abs"]] = (rec["label"], f)

    print("Constructed number field lookup tables")

    immediate_parents = {}
    gpdata = {}
    for rec in db.gps_gl2zhat_test.search({"level": {"$ne": 1}}, ["label", "parents", "contains_negative_one", "genus", "gonality_bounds", "simple", "rank"]):
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

    lit_data = load_points_files(data_folder)
    print("Loaded tables from files")

    ecq_db_data = []
    for rec in db.ec_curvedata.search({}, ["elladic_images", "lmfdb_label", "ainvs", "jinv", "cm"]):
        for label in rec["elladic_images"]:
            if label not in all_parents:
                # Don't have the label yet
                # This is unfortunate, since we can thus miss points of lower level coming from this curve
                print(f"Skipping elladic image {label}")
                continue
            Elabel = rec["lmfdb_label"]
            if rec["jinv"][1] == 1:
                jinv = str(rec["jinv"][0])
            else:
                jinv = "%s/%s" % tuple(rec["jinv"])
            ecq_db_data.append((label, 1, "1.1.1.1", jinv, "1.1.1.1", rec["cm"], r"\N", Elabel, False))
    print("Loaded elliptic curves over Q")

    ecnf_db_data = []
    total = db.ec_nfcurves.count()
    for progress, rec in enumerate(db.ec_nfcurves.search({}, ["galois_images", "degree", "field_label", "jinv", "cm", "label"])):
        if progress and progress % 10000 == 0:
            print(f"ECNF: {progress}/{total}")
        if not rec["galois_images"]:
            continue
        if rec["jinv"].endswith(",0" * (rec["degree"] - 1)):
            jfield = "1.1.1.1"
            jinv = rec["jinv"].split(",")[0]
        else:
            K = nfs[rec["field_label"]]
            j = K([QQ(c) for c in rec["jinv"].split(",")])
            Qj, jinc = K.subfield(j)
            if Qj.degree() == rec["degree"]:
                jfield = rec["field_label"]
                jinv = rec["jinv"]
            else:
                jfield, f = sub_lookup[Qj.degree(), Qj.discriminant().abs()]
                jinv = ",".join(str(c) for c in f.roots(Qj, multiplicities=False)[0].coordinates_in_terms_of_powers()(Qj.gen()))
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
                print(f"Skipping Slabel {Slabel}")
                continue
            label = from_Slabel[Slabel]
            Elabel = rec["label"]
            ecnf_db_data.append((label, rec["degree"], rec["field_label"], jinv, jfield, rec["cm"], r"\N", Elabel, False))
    print("Loaded elliptic curves over number fields")

    # Check for overlap as we add points
    jinvs_seen = defaultdict(set)
    point_counts = defaultdict(Counter)
    # Things to add: isolated, coordinates in terms of model, LMFDB curve label (when not containing -1
    with open(os.path.join(data_folder, "modcurve_ratpoints.txt"), "w") as F:
        _ = F.write("label|degree|residue_field|jinv|j_field|cm|quo_info|Elabel|isolated\ntext|smallint|text|text|text|smallint|smallint[]|text|smallint\n\n")
        for (label, degree, field_of_definition, jinv, field_of_j, cm, quo_info, Elabel, known_isolated) in ecq_db_data + ecnf_db_data + lit_data:
            for plabel in [label] + all_parents[label]:
                if (field_of_j, jinv) not in jinvs_seen[plabel]:
                    jinvs_seen[plabel].add((field_of_j, jinv))
                    point_counts[plabel][degree] += 1
                    gdat = gpdata[plabel]
                    g = gdat["genus"]
                    gonlow = gdat["gonality_bounds"][0]
                    rank = gdat["rank"]
                    simp = gdat["simple"]
                    Enow = r"\N" if gdat["contains_negative_one"] else Elabel
                    if label == plabel and known_isolated:
                        isolated = "1"
                    elif degree == 1:
                        isolated = "-1" if (g == 0 or g == 1 and rank > 0) else "1"
                    elif degree < QQ(gonlow) / 2 or degree < gonlow and (rank == 0 or simp and degree < g):
                        isolated = "1"
                    elif degree > g:
                        isolated = "-1"
                    else:
                        isolated = r"0"
                    _ = F.write("|".join([plabel, str(degree), field_of_definition, jinv, field_of_j, str(cm), quo_info, Enow, isolated]) + "\n")
    with open(os.path.join(data_folder, "modcurve_ptcount_update.txt"), "w") as F:
        _ = F.write("label|" + "|".join(f"known_degree{d}_points" for d in range(1,7)) + "\ntext" + "|smallint"*6 + "\n\n")
        for label, cnts in point_counts.items():
            _ = F.write(label + "|" + "|".join(str(cnts[d]) for d in range(1, 7)) + "\n")

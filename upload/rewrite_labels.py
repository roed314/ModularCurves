import re
from lmfdb import db
ope = os.path.exists

tables = dict(coarse="gps_gl2zhat_coarse",
              fine="gps_gl2zhat_fine",
              models="modcurve_models",
              modelmaps="modcurve_modelmaps",
              points="modcurve_points",
              pictures="modcurve_pictures",
)

def class_to_int(k):
    if k.isdigit():
        return int(k)
    elif k.isalpha() and k.islower():
        kk = [string.ascii_lowercase.index(ch) for ch in k]
    elif k.isalpha() and k.isupper():
        kk = [string.ascii_uppercase.index(ch) for ch in k]
    else:
        raise ValueError("Invalid class", k)
    kk.reverse()
    return sum(kk[i] * 26 ** i for i in range(len(kk)))
def sort_key(label):
    return [class_to_int(c) for c in re.split(r"\.|\-", label)]

def rewrite_labels(labelfile="modcurve_match.txt",
                   do_upload=False,
                   delete_files=None,
                   coarse_in="gps_gl2zhat_coarse.in",
                   coarse_out="gps_gl2zhat_coarse.out",
                   fine_in="gps_gl2zhat_fine.in",
                   fine_out="gps_gl2zhat_fine.out",
                   models_in="modcurve_models.in", # todo: some of these should have _test
                   models_out="modcurve_models.out",
                   modelmaps_in="modcurve_modelmaps.in",
                   modelmaps_out="modcurve_modelmaps.out",
                   points_in="modcurve_points.in",
                   points_out="modcurve_points.out",
                   pictures_in="modcurve_pictures.in",
                   pictures_out="modcurve_pictures.out"):
    assert ope(labelfile)
    if delete_files is None:
        delete_files = do_upload
    print("Building label lookup table")
    lookup = {}
    new_gens = {}
    with open(labelfile) as F:
        for i, line in enumerate(F):
            if i % 200000 == 0: print(f"Lookup {i}")
            RSZBlabel, NewLabel, OldLabel, hsh, newgens, oldgens = line.strip().split(":")
            lookup[OldLabel] = NewLabel
            new_gens[NewLabel] = newgens
    def replace_list(s):
        L = s[1:-1].split(",")
        L = [lookup[x] for x in L]
        L.sort(key=sort_key)
        return "{%s}" % (",".join(L))
    for name, tblname in tables.items():
        fname = locals()[name+"_in"]
        if not(ope(fname)):
            print(f"Copying {tblname} to {fname}")
            db[tblname].copy_to(fname, include_id=False)
    # Coarse table
    for name, tblname in tables.items():
        print(f"Rewriting {name} table")
        iname = locals()[name+"_in"]
        oname = locals()[name+"_out"]
        with open(iname) as F:
            with open(oname, "w") as Fout:
                for i, line in enumerate(F):
                    if i == 0:
                        cols = line.strip().split("|")
                    elif i > 2:
                        if i % 200000 == 0: print(f"{name} {i}")
                        D = dict(zip(cols, line.strip().split("|")))
                        # Now the actual changes
                        if name == "coarse":
                            new_label = D["label"] = lookup[D["label"]]
                            D["coarse_num"] = new_label.rsplit(".", 1)[1]
                            D["parents"] = replace_list(D["parents"])
                            D["lattice_labels"] = replace_list(D["lattice_labels"])
                            D["psl2label"] = lookup[D["psl2label"]]
                            D["sl2label"] = lookup[D["sl2label"]]
                            D["canonical_generators"] = new_gens[new_label]
                        elif name == "fine":
                            new_label = D["label"] = lookup[D["label"]]
                            D["coarse_num"] = new_label.rsplit(".", 2)[1]
                            D["fine_num"] = new_label.rsplit(".", 1)[1]
                            D["parents"] = replace_list(D["parents"])
                            D["lattice_labels"] = replace_list(D["lattice_labels"])
                            D["psl2label"] = lookup[D["psl2label"]]
                            D["sl2label"] = lookup[D["sl2label"]]
                            D["canonical_generators"] = new_gens[new_label]
                        elif name == "models":
                            D["modcurve"] = lookup[D["modcurve"]]
                        elif name == "modelmaps":
                            D["domain_label"] = lookup[D["domain_label"]]
                            D["codomain_label"] = lookup[D["codomain_label"]]
                        elif name == "points":
                            D["curve_label"] = lookup[D["curve_label"]]
                        elif name == "pictures":
                            D["psl2label"] = lookup[D["psl2label"]]
                        line = "|".join([D[col] for col in cols]) + "\n"
                    _ = Fout.write(line)
    if do_upload:
        for name, tblname in tables.items():
            print(f"Uploading {name}")
            oname = locals()[name+"_out"]
            db[tblname].reload(oname)
    if delete_files:
        for name in tables.items():
            print(f"Deleting files for {name}")
            iname = locals()[name+"_in"]
            oname = locals()[name+"_out"]
            os.remove(iname)
            os.remove(oname)

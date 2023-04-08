#!/usr/bin/env -S sage -python

import os
opj = os.path.join
import sys
import argparse
parser = argparse.ArgumentParser("Compute which curves descend to an intermediate field")
parser.add_argument("nf", help="number field, base for elliptic curves")

sys.path.append(os.path.expanduser(opj("~", "lmfdb")))

from sage.all import EllipticCurve, NumberField, PolynomialRing, ZZ, QQ
from lmfdb import db
from collections import defaultdict

args = parser.parse_args()

R = PolynomialRing(ZZ, name="x")
Kdata = db.nf_fields.lookup(args.nf, ["coeffs", "subfields"])
coeffs = [[ZZ(c) for c in K.split(".")] for K in Kdata["subfields"]]
subfields = [NumberField(R(clist), "a") for clist in coeffs]
subfield_labels = [db.nf_fields.lucky({"coeffs": clist}, "label") for clist in coeffs]
by_jinvs = []
for K, Klabel in zip(subfields, subfield_labels):
    by_jinvs.append(defaultdict(list))
    for rec in db.ec_nfcurves.search({"field_label": Klabel}, ["label", "jinv", "ainvs"]):
        j = K([QQ(c) for c in rec["jinv"].split(",")])
        ainvs = [K([QQ(c) for c in a.split(",")]) for a in rec["ainvs"].split(";")]
        E = EllipticCurve(ainvs)
        by_jinvs[-1][j].append((E, rec["label"]))
L = NumberField(R(Kdata["coeffs"]), "b")
embss = [K.embeddings(L) for K in subfields]
with open(opj("ecnf_bc", args.nf), "w") as F:
    if subfields:
        for rec in db.ec_nfcurves.search({"field_label": args.nf}, ["label", "ainvs"]):
            ainvs = [L([QQ(c) for c in a.split(",")]) for a in rec["ainvs"].split(";")]
            E = EllipticCurve(ainvs)
            for K, embs, by_jinv in zip(subfields, embss, by_jinvs):
                Edesc = E.descend_to(K, embs[0])
                desc_labels = set()
                i = 0
                while len(desc_labels) < len(Edesc) and i < len(embs):
                    if i != 0:
                        Edesc = E.descend_to(K, embs[i])
                    i += 1
                    for EK in Edesc:
                        j = EK.j_invariant()
                        if j in by_jinv:
                            for EK1, label1 in by_jinv[j]:
                                if EK.is_isomorphic(EK1):
                                    desc_labels.add(label1)
                                    break
                if Edesc:
                    missing = "missing" if (len(desc_labels) < len(Edesc)) else "found"
                    _ = F.write(f"{rec['label']}|{K.defining_polynomial()}|{[Ed.ainvs() for Ed in Edesc]}|{desc_labels}|{missing}\n")
    _ = F.write("Done")

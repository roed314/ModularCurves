#!/usr/bin/env -S sage -python

import os
opj = os.path.join
import sys
import argparse
parser = argparse.ArgumentParser("Compute which curves descend to an intermediate field")
parser.add_argument("nf", help="number field, base for elliptic curves")

sys.path.append(os.path.expanduser(opj("~", "lmfdb")))

from sage.all import EllipticCurve, NumberField, PolynomialRing, QQ
from lmfdb import db

args = parser.parse_args()

R = PolynomialRing(QQ, name="x")
Kdata = db.nf_fields.lookup(args.nf, ["coeffs", "subfields"])
subfields = [NumberField(R([QQ(c) for c in K.split(".")]), "a") for K in Kdata["subfields"]]
K0 = NumberField(R(Kdata["coeffs"]), "b")
with open(opj("ecnf_bc", args.nf), "w") as F:
    if subfields:
        for rec in db.ec_nfcurves.search({"base_change":[], "field_label": args.nf}, ["label", "ainvs"]):
            ainvs = [K0([QQ(c) for c in a.split(",")]) for a in rec["ainvs"].split(";")]
            E = EllipticCurve(ainvs)
            for K in subfields:
                Edesc = E.descend_to(K)
                if Edesc:
                    _ = F.write(f"{rec['label']}|{K.defining_polynomial()}|{[Ed.ainvs() for Ed in Edesc]}\n")
    _ = F.write("Done")

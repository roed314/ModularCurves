

import os
import sys
import re
import argparse
from collections import defaultdict
from sage.all import ZZ, QQ, gcd, PolynomialRing, ceil, NumberField
from sage.databases.cremona import class_to_int

opj = os.path.join
ope = os.path.exists
sys.path.append(os.path.expanduser(opj("~", "lmfdb")))
from lmfdb import db
from cloud_common import load_gl2zhat_rational_data, load_gl2zhat_cusp_data, get_lattice_poset, index_iterator, to_coarse_label, get_output_data, dbtable, is_isolated

def get_gonalities(model_gonalities=None):
    P = get_lattice_poset()
    H = P._hasse_diagram
    gonalities = {P._element_to_vertex(rec["label"]): rec["q_gonality_bounds"] + rec["qbar_gonality_bounds"] for rec in db.gps_gl2zhat_coarse.search({}, ["label", "q_gonality_bounds", "qbar_gonality_bounds"])}
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
            msg = []
            for gon in range(low, high):
                # Try to rule out gon as a possible gonality using Castelnuovo–Severi (Theorem 6.0.1 in overleaf)
                csdg = [d for d in dg if gcd(d, gon) == 1]
                csdg = [(d,g) for d in csdg for g in dg[d] if (genus - d*g) / (d - 1) + 1 > gon]
                if csdg:
                    msg.append("%s:%s" % csdg[0])
                    gonalities[x][bar] = gon + 1
                else:
                    break
            if msg:
                msg = ",".join(msg)
                _ = F.write(f"C|{bar}|{P._vertex_to_element(x)}|{gon}|{msg}|{gonalities[x][bar] - low}\n")

    def get_bars(bounds):
        return ([] if bounds[0] == bounds[1] else [0]) + ([] if bounds[2] == bounds[3] else [2])
    # We record the changes so that we can write about them
    with open("gon_improvements.txt", "w") as F:
        # Import the gonalities from models
        if model_gonalities is not None:
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
                index = ig[x][0]
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
                index = ig[x][0]
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

def create_db_uploads(execute=False):
    data = defaultdict(lambda: defaultdict(list))
    for line in get_output_data():
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

    def show_gon(gon):
        q, qbar, qbnd, qbarbnd = gon
        if q is None: q = r"\N"
        if qbar is None: qbar = r"\N"
        qbnd = "{%s,%s}" % qbnd
        qbarbnd = "{%s,%s}" % qbarbnd
        return f"{q}|{qbar}|{qbnd}|{qbarbnd}"
    with open("gps_gl2zhat_coarse.update", "w") as F:
        _ = F.write("label|q_gonality|qbar_gonality|q_gonality_bounds|qbar_gonality_bounds|lattice_labels|lattice_x|num_known_degree1_points\ntext|integer|integer|integer[]|integer[]|text[]|integer[]|integer\n\n")
        default = r"\N|\N"
        for label, gon in gonalities.items():
            gon = show_gon(gon)
            card = num_pts.get(label, 0)
            _ = F.write(f"{label}|{gon}|{data['L'].get(label, default)}|{card}\n")
    refinements = defaultdict(list)
    for rec in db.gps_gl2zhat_fine.search({"contains_negative_one":False}, ["label", "coarse_label"]):
        refinements[rec["coarse_label"]].append(rec["label"])
    with open("gps_gl2zhat_fine.update", "w") as F:
        _ = F.write("label|q_gonality|qbar_gonality|q_gonality_bounds|qbar_gonality_bounds\ntext|integer|integer|integer[]|integer[]\n\n")
        for coarse_label, gon in gonalities.items():
            gon = show_gon(gon)
            for label in refinements[coarse_label]:
                _ = F.write(f"{label}|{gon}\n")

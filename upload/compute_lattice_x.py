#!/usr/bin/env -S sage -python
import subprocess
import argparse
import os
import sys
from collections import defaultdict
from sage.misc.cachefunc import cached_function
from sage.all import ZZ, Poset, DiGraph
from sage.combinat.posets.posets import FinitePoset
from sage.misc.misc import cputime, walltime
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
def get_poset():
    t0 = walltime()
    R = []
    for rec in db.gps_gl2zhat_test.search({}, ["label", "parents"]):
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
    #return Poset(([],R), cover_relations=True)

@cached_function
def distinguished_vertices():
    return {rec["label"]: rec["name"] for rec in db.gps_gl2zhat_test.search({"name":{"$ne":""}}, ["label", "name"])}

Xfams = ['X', 'X0', 'X1', 'Xsp', 'Xns', 'Xsp+', 'Xns+', 'XS4']

@cached_function
def intervals_to_save(max_size=60):
    P = get_poset()
    H = P._hasse_diagram
    t0 = cputime()
    DV = distinguished_vertices()
    D = [P._element_to_vertex(d) for d in DV]
    trimmed = {}
    intervals = {}
    for d in D:
        trimmed[d] = T = {}
        intervals[d] = I = {}
        for x in H.breadth_first_search(d):
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
            by_fam = defaultdict(dict)
            for d in ints:
                fam = DV[d].split("(")[0]
                n = ZZ(DV[d].split("(")[1].split(")")[0])
                by_fam[fam][n] = d
            S = []
            for fam, ns in by_fam.items():
                for n, d in ns.items():
                    if len([m for m in ns if n.divides(m)]) == 1:
                        i = int(d.split(".")[1])
                        # Sort by index (reversed), then family
                        S.append((-i, Xfams.index(fam), d))
            S.sort()
            I = J = set([x] + P.upper_covers(x)).union(ints[S[0][2]])
            num_tops[x] = 1
            for i, f, d in S[1:]:
                I = I.union(ints[d])
                if len(I) > max_size:
                    break;
                num_tops[x] += 1
                J = I
        else:
            J = list(ints.values())[0].union(P.upper_covers(x))
            num_tops[x] = 1
        if len(J) <= max_size:
            J = sorted(J, key=sort_key)
            stored_intervals[x] = J
    print("Stored in", cputime() - t0)
    return stored_intervals, num_tops

def display(label):
    DV = distinguished_vertices()
    if label in DV:
        return DV[label]
    return "%s_%s^%s" % tuple(label.split(".")[:3])

def get_rank(label):
    return sum(e for (p,e) in ZZ(label.split(".")[1]).factor())

def sort_key(label):
    return [-get_rank(label)] + [ZZ(c) for c in label.split(".")]

def save_graphviz(label):
    P = get_poset()
    D, num_tops = intervals_to_save()
    print("Constructing graphviz file")
    t0 = cputime()
    if label not in D:
        return {}
    nodes = D[label]
    PP = P.subposet(nodes)
    edges = defaultdict(list)
    for a,b in PP.cover_relations():
        edges[a].append(b)
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
    infile = f"/tmp/graph{label}.in"
    outfile = f"/tmp/graph{label}.out"
    with open(infile, "w") as F:
        _ = F.write(graph)
    print("Constructed in", cputime() - t0)
    t0 = walltime()
    subprocess.run(["dot", "-Tplain", "-o", outfile, infile], check=True)
    print("Subprocess run in", walltime() - t0)
    t0 = cputime()
    xcoord = {}
    with open(outfile) as F:
        maxx = 0
        minx = 10000
        for line in F:
            if line.startswith("graph"):
                scale = float(line.split()[2])
            elif line.startswith("node"):
                pieces = line.split()
                short_label = pieces[1].replace('"', '')
                diagram_x = int(round(10000 * float(pieces[2]) / scale))
                xcoord[short_label] = diagram_x
                if diagram_x > maxx:
                    maxx = diagram_x
                if diagram_x < minx:
                    minx = diagram_x
    os.remove(infile)
    os.remove(outfile)
    print("Finished in", cputime() - t0)
    return xcoord

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

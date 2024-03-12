#!/usr/bin/env sage
"""
make_modular_curve_picture.sage - make pictures of modular curves

Given an N and a subgroup H of GL(2, Z/NZ) (by a set of generators), this makes
a picture. The picture is formed by taking translates of triangles in the
hyperbolic plane.

In practice, one either calls `make_picture_by_label` or
`make_picture_by_label_and_gens`. For mass production, create an input list of
levels and generators by reading from the database, and then parallelize calls
to `make_picture_by_label_and_gens`.


Before calling `make_picture_by_label`, ensure that the lmfdb is in the
PYTHONPATH. For example, calling the equivalent of

    import sys
    sys.path.append("/scratch/home/davidlowryduda/lmfdb")

and then loading this with either `attach` or `load` from a sage session.



# LICENSE #

Below is boilerplate license code. I include this header from a template file.

# **********************************************************************
#       Copyright (c) 2022 David Lowry-Duda <david@lowryduda.com>
#       All Rights Reserved.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see
#                 <http://www.gnu.org/licenses/>.
# **********************************************************************
"""
import os
import time
import argparse
from sage.misc.decorators import options, rename_keyword
from sage.plot.hyperbolic_polygon import HyperbolicPolygon
opj = os.path.join


parser = argparse.ArgumentParser("Compute pictures for modular curves")
#parser.add_argument("job", type=int, help="job number: 0 to n-1, where n is the number of parallel threads used")
#parser.add_argument("num_jobs", type=int, help="total number of jobs n")
parser.add_argument("input_file")
parser.add_argument("output_file")
args = parser.parse_args()


GL2 = GL(2, ZZ)
SL2 = SL(2, ZZ)
Sid = SL2([[1, 0], [0, 1]])
Sidneg = SL2([[-1, 0], [0, -1]])
T = SL2([[1, 1], [0, 1]])
Tinv = SL2([[1, -1], [0, 1]])
S = SL2([[0, -1], [1, 0]])


# Poincare disk model
PD = HyperbolicPlane().PD()


# blue-green color palette from https://colorbrewer2.org/#type=sequential&scheme=YlGnBu&n=5
COLOR_PALETTE = ["#a1dab4", "#2c7fb8", "#41b6c4"]  # blue-green colors
COLOR1 = COLOR_PALETTE[0]
COLOR2 = COLOR_PALETTE[1]
CCOLOR = COLOR_PALETTE[2]


def make_picture_by_label(label):
    import sys
    sys.path.append(os.path.expanduser(opj("~", "lmfdb")))
    from lmfdb import db
    table = db.gps_gl2zhat_fine
    print(f"Making picture for {label}")
    if label == '1.1.0.a.1':
        g = make_sl2z_picture_disk()
        g.save(f"mcportrait.{label}.png", figsize=[4,4])
    else:
        curvedb = table.lucky({'label': label})
        N = curvedb['level']
        rawgens = curvedb['generators']
        print(rawgens)
        matgens = []
        while rawgens:
            a, b, c, d = rawgens[0]
            rawgens = rawgens[1:]
            matgens.append([[a, b], [c, d]])
        g = make_picture_disk(N, matgens)
        g.save(f"mcportrait.{label}.png", figsize=[4,4])


def make_picture_by_label_and_gens(label, level, gens):
    print(f"Making picture for {label}")
    if label == '1.1.0.a.1':
        g = make_sl2z_picture_disk()
        g.save(f"mcportrait.{label}.png", figsize=[4,4])
    else:
        g = make_picture_disk(level, gens)
        g.save(f"mcportrait.{label}.png", figsize=[4,4])

def make_picture_strings(input_file, output_file):
    sys.path.append("/Users/roed/sage/lmfdb")
    from lmfdb.utils import encode_plot
    with open(input_file) as F:
        with open(output_file, "w") as Fout:
            _ = Fout.write(f"label|image\ntext|text\n\n")
            for line in F:
                label, level, gens = line.strip().split(":")
                level = ZZ(level)
                gens = sage_eval(gens)
                if label == '1.1.0.a.1':
                    g = make_sl2z_picture_disk()
                else:
                    g = make_picture_disk(level, gens)
                s = encode_plot(g, remove_axes=True, figsize=[4,4])
                _ = Fout.write(f"{label}|{s}\n")

@rename_keyword(color='rgbcolor')
@options(alpha=1, fill=True, thickness=0, rgbcolor="blue", zorder=2, linestyle='solid')
def my_hyperbolic_polygon(pts, model="PD", resolution=200,
        circlecolor='black', add_circle=False, **options):
    r"""
    Return a hyperbolic polygon in the hyperbolic plane with vertices ``pts``.

    This is on the poincare disk, but doesn't add random black circles
    repeatedly like the default version.

    INPUT:

    - ``pts`` -- a list or tuple of complex numbers

    OPTIONS:

    - ``alpha`` -- default: 1

    - ``fill`` -- default: ``False``

    - ``thickness`` -- default: 1

    - ``rgbcolor`` -- default: ``'blue'``

    - ``linestyle`` -- (default: ``'solid'``) the style of the line, which is
      one of ``'dashed'``, ``'dotted'``, ``'solid'``, ``'dashdot'``, or
      ``'--'``, ``':'``, ``'-'``, ``'-.'``, respectively
    """
    if not model == "PD":
        raise ValueError("Only the disk model is supported")
    from sage.plot.all import Graphics
    g = Graphics()
    g._set_extra_kwds(g._extract_kwds_for_show(options))

    g.add_primitive(HyperbolicPolygon(pts, model, options))
    g.set_aspect_ratio(1)
    if add_circle:
        g = g + circle((0, 0), 1, rgbcolor=circlecolor)
    return g


def relevant_circle(rgbcolor='black'):
    return circle((0, 0), 1, rgbcolor=rgbcolor)


def make_sl2z_picture_disk(with_circle=True, circle_color=CCOLOR, **kwargs):
    g = Graphics()
    A = CC(0, 1)
    B = CC(1/2, sqrt(3)/2.)
    C = CC(-1/2, sqrt(3)/2.)
    D = infinity
    Apt = 0.9999*cayley(A) + 1e-12j
    Bpt = 0.9999*cayley(B) + 1e-12j
    Cpt = 0.9999*cayley(C) + 1e-12j
    Dpt = 0.9999*cayley(D) + 1e-12j
    g += my_hyperbolic_polygon((Apt, Bpt, Dpt), fill=True, color=COLOR1,
            model="PD", **kwargs)
    g += my_hyperbolic_polygon((Apt, Cpt, Dpt), fill=True, color=COLOR2,
            model="PD", **kwargs)
    d = g.get_minmax_data()
    g.set_axes_range(-1, 1, -1, 1)
    if with_circle:
        g += relevant_circle(rgbcolor=circle_color)
    g.axes(False)
    return g


def make_picture_disk(N, subgroup_gens, with_circle=True, circle_color=CCOLOR,
        usealpha=True, **kwargs):
    """
    Make a graphics object for modular curve corresponding to subgroup H of
    GL(2, Z/NZ) generated by `subgroup_gens`.
    """
    gln = GL(2, Zmod(N))
    subgroup_gens = list(map(lambda mat: gln(mat), subgroup_gens))
    H = gln.subgroup(subgroup_gens)
    Hsl = find_SL2_subgroup(N, H)
    cosets = find_SL2Z_cosets(N, Hsl, limit=384)
    idx = 0
    while idx < len(cosets):
        cs = cosets[idx]
        if Sidneg * cs in cosets:
            cosets.pop(idx)
        else:
            idx += 1

    g = Graphics()
    A = CC(0, 1)
    B = CC(1/2, sqrt(3)/2.)
    C = CC(-1/2, sqrt(3)/2.)
    D = infinity

    numcosets = len(cosets)
    for idx, mat in enumerate(cosets):
        if idx <= 128 or not usealpha:
            alpha = 1
        else:
            alpha = 1 - (idx - 128)/(numcosets - 128)
        Apt = 0.9999*cayley(act(mat, A)) + 1e-12j
        Bpt = 0.9999*cayley(act(mat, B)) + 1e-12j
        Cpt = 0.9999*cayley(act(mat, C)) + 1e-12j
        Dpt = 0.9999*cayley(act(mat, D)) + 1e-12j
        g += my_hyperbolic_polygon((Apt, Bpt, Dpt), fill=True, color=COLOR1,
                model="PD", alpha=alpha, **kwargs)
        g += my_hyperbolic_polygon((Apt, Cpt, Dpt), fill=True, color=COLOR2,
                model="PD", alpha=alpha, **kwargs)
    d = g.get_minmax_data()
    g.set_axes_range(-1, 1, -1, 1)
    if with_circle:
        g += relevant_circle(rgbcolor=circle_color)
    g.axes(False)
    return g


def find_boundary_edges(N, subgroup_gens):
    gln = GL(2, Zmod(N))
    subgroup_gens = list(map(lambda mat: gln(mat), subgroup_gens))
    H = gln.subgroup(subgroup_gens)
    Hsl = find_SL2_subgroup(N, H)
    cosets = find_SL2Z_cosets(N, Hsl)
    # remove cosets whose negative are in the list
    idx = 0
    while idx < len(cosets):
        cs = cosets[idx]
        if Sidneg * cs in cosets:
            cosets.pop(idx)
        else:
            idx += 1

    B = CC(1/2, sqrt(3)/2.)
    C = CC(-1/2, sqrt(3)/2.)
    D = infinity

    edges = []

    for mat in cosets:
        Bpt = cayley(act(mat, B))
        Cpt = cayley(act(mat, C))
        Dpt = cayley(act(mat, D))
        add_edge_to_edges((Bpt, Cpt), edges)
        add_edge_to_edges((Cpt, Dpt), edges)
        add_edge_to_edges((Dpt, Bpt), edges)

    return edges


def order_boundary_edges(input_edges):
    """
    Given a list of tuples of points representing edges, compute a single
    boundary path. This means finding an ordering of the edges such that the
    tail of an edge is the head of the next edge.
    """
    edges = input_edges.copy()

    # we order the edges to find an appropriate orientation
    for idx, edge in enumerate(edges):
        left, right = edge
        if abs(real(right)) < 0.0001 and abs(imag(right) - 1) < 0.0001:
            left, right = right, left
        if abs(real(left)) < 0.0001 and abs(imag(left) - 1) < 0.0001:
            if real(right) < 0:
                edges = edges[idx:] + edges[:idx]
                edges.pop(0)
                circuit = [(left, right)]
                break
    while edges:
        tail = circuit[-1][-1]
        for idx in range(len(edges)):
            cleft, cright = edges[idx]
            if near(cleft, tail):
                circuit.append((cleft, cright))
                edges.pop(idx)
                break
            if near(cright, tail):
                circuit.append((cright, cleft))
                edges.pop(idx)
                break
    return circuit


def add_edge_to_edges(cand_edge, edges):
    left, right = cand_edge
    for idx in range(len(edges)):
        eleft, eright = edges[idx]
        if near(eleft, left) and near(eright, right):
            removed = edges.pop(idx)
            return
        if near(eleft, right) and near(eright, left):
            removed = edges.pop(idx)
            return
    edges.append((left, right))
    return


def near(pt1, pt2, tol=1e-6):
    if abs(pt1 - pt2) < tol:
        return True
    return False


def make_manual_svg(N, gens, filename="testmanual.svg"):
    scalefactor = 250
    boundary_edges = find_boundary_edges(N, gens)
    ordered_boundary = order_boundary_edges(boundary_edges)
    segments = []
    for bstart, bend in ordered_boundary:
        segments.append(Segment(bstart, bend))
    svg_string = ["""<?xml version="1.0" standalone="no"?>
<svg width="10cm" height="10cm" viewBox="0 0 500 500"
     xmlns="http://www.w3.org/2000/svg" version="1.1">"""]

    first_segment = segments[0]
    svg_string.append(f"""<path d="M{first_segment.starting_location(scalefactor)}""")
    for segment in segments:
        svg_string.append(segment.svg_piece(scalefactor))
    svg_string.append("""  z" fill="#016c59" stroke="none" />""")
    svg_string.append("""  <circle cx="250" cy="250" r="250" stroke="#016c59"
    stroke-width="2" fill="none" />
</svg>""")
    svg_raw = "\n".join(svg_string)
    with open(filename, "w", encoding="utf8") as outfile:
        outfile.write(svg_raw)


def find_SL2_subgroup(N, H):
    """
    Return the intersection of H with SL(2, Z/NZ), as a sage object.
    """
    sln = SL(2, Zmod(N))
    Hsl = H.intersection(sln)
    return Hsl


def find_SL2Z_cosets(N, Hsl, limit=256):
    """
    Give a set of coset representatives for the action of a subgroup `Hsl` of
    SL(2, Z/NZ) on the upper halfplane.
    """
    sln = SL(2, Zmod(N))
    queue = [Sid]
    seen = set()
    cosets = []
    while queue and len(cosets) < limit:
        cand = queue.pop(0)
        proj_cand = sln(cand)

        is_new = True
        if proj_cand in seen:
            continue
        for proj_found in seen:
            if not is_new:
                continue
            if proj_found * (proj_cand^(-1)) in Hsl:
                is_new = False
        if not is_new:
            continue
        seen.add(proj_cand)
        cosets.append(cand)
        queue.append(cand * T)
        queue.append(cand * Tinv)
        queue.append(cand * S)
    return cosets


def act(slnmat, z):
    """
    Raise slnmat to GL2, act on z, and return result.
    """
    mat = GL2(slnmat)
    [a, b], [c, d] = mat.list()
    if z == infinity:
        if c == 0:
            return infinity
        return a / c
    return (a*z + b) / (c*z + d)


def cayley(z):
    if z == infinity:
        return CC(0, 1)
    return (z - CC(0, 1)) / (CC(0, -1)*z + 1)

def encode_mcurve_plot(P, transparent=True):
    from io import BytesIO as IO
    from matplotlib.backends.backend_agg import FigureCanvasAgg
    from base64 import b64encode
    from urllib.parse import quote

    virtual_file = IO()
    fig = P.matplotlib(axes_pad=None)
    ax = fig.axes[0]
    ax.set_xlim(xmin=-1, xmax=1)
    ax.set_ylim(ymin=-1, ymax=1)
    fig.set_canvas(FigureCanvasAgg(fig))
    fig.set_size_inches(2.5, 2.5) # images are 200 x 200 on the website
    fig.savefig(virtual_file, format='png', bbox_inches='tight', transparent=transparent, dpi=120)
    virtual_file.seek(0)
    buf = virtual_file.getbuffer()
    return "data:image/png;base64," + quote(b64encode(buf))

make_picture_strings(args.input_file, args.output_file)

# t0 = time.time()
# os.makedirs("pictures", exist_ok=True)
# with open(opj("pictures", str(args.job)), "w") as Fout:
#     with open("picture_labels.txt") as F:
#         for i, line in enumerate(F):
#             if i % args.num_jobs == args.job:
#                 label = line.strip()
#                 if label == "1.1.0.a.1":
#                     g = make_sl2z_picture_disk()
#                 else:
#                     level = ZZ(label.split(".")[0])
#                     with open(opj("..", "equations", "psl2_input_data", label)) as Finp:
#                         matgens = []
#                         gens = Finp.read()
#                         if gens: # 2.6.0.a.1 = X(2) has no generators
#                             gens = gens.split(",")
#                             for j in range(0, len(gens), 4):
#                                 try:
#                                     matgens.append([[ZZ(gens[j]), ZZ(gens[j+1])], [ZZ(gens[j+2]), ZZ(gens[j+3])]])
#                                 except TypeError:
#                                     print("Error!", label)
#                                     raise
#                     g = make_picture_disk(level, matgens)
#                 pngstr = encode_mcurve_plot(g)
#                 _ = Fout.write(f"{label}|{pngstr}\n")
# print(f"Total time {time.time() - t0}")

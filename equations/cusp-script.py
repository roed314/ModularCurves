from lmfdb import db

def label_to_cusps(label):
    return list(db.modcurve_points.search({'curve_label':label, 'cusp':True}))

def string_to_nf_elt(s, basis):
    K = basis[0].parent()
    s_spl = s.split(',')
    assert len(basis) == len(s_spl)
    return sum([K(s_spl[i])*basis[i] for i in range(len(basis))])

def coord_string_to_coords(coords, basis):
   return [string_to_nf_elt(el, basis) for el in coords.split(':')]

def cusp_orbits_to_tuples(rec):
    nf_rec = db.nf_fields.lookup(rec['residue_field'])
    R = PolynomialRing(QQ, 'x')
    x = R.gens()[0]
    K = NumberField(R(nf_rec['coeffs']), 'a')
    a = K.gens()[0]
    basis = [K(el) for el in nf_rec['zk']]
    coord_strs = rec['coordinates']['0'] # '0' means canonical model
    return [coord_string_to_coords(el, basis) for el in coord_strs]

# this is the top-level function
def label_to_cusp_tuples(label):
    cusps = label_to_cusps(label)
    return [cusp_orbits_to_tuples(rec) for rec in cusps]

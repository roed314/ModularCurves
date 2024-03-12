from lmfdb import db

def gonality_bounds(rec):
    if rec.get('q_gonality'):
        return [rec['q_gonality'] for i in range(2)]
    if rec.get('q_gonality_bounds'):
        return rec['q_gonality_bounds']

def target_curves(lbound=3, ubound=6):
    low = []
    for rec in db.gps_gl2zhat_coarse.search({'genus':{'$gte':4}}):
        L, U = gonality_bounds(rec)
        if (lbound <= L) and (U <= ubound):
            low.append(rec['label'])
    return low

def has_canonical_no_plane(label):
    models = db.modcurve_models.search({'modcurve':label})
    can_bool = False
    plane_bool = False
    for model in models:
        if model['model_type'] == 0:
            can_bool = True
        if model['model_type'] == 2:
            plane_bool = True
    return (can_bool and not plane_bool)


#def has_plane_model(label):
#    models = db.modcurve_models.search({'modcurve':label})
#    for model in models:
#        if model['model_type'] == 2:
#            return True
#    return False

def curves_with_missing_model():
    missing = []
    low = target_curves()
    print("low has size %d" % len(low))
    for lab in low:
        if has_canonical_no_plane(lab):
            missing.append(lab)
    return missing

#def few_models():
#    few = []
#    models = db.modcurve_models.search({'modcurve':label})
#    if len(models) in [0,1]:
#        few.append(label)
#    return False

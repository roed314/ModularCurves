from lmfdb import db

s = db.modcurve_models.search(query={}, projection={'modcurve', 'model_type', 'number_variables', 'equation'})
Crvs = dict()
for c in s:
	if not(c['modcurve'] in Crvs):
		Crvs[c['modcurve']] = dict()
	Crvs[c['modcurve']][c['model_type']] = [ c['number_variables'], c['equation'] ]

s = db.modcurve_points.search(query={'cusp' : True}, projection={'residue_field', 'coordinates', 'curve_label'})
Pts = dict()
FldLabels = dict()
AllFldLabels = set()
for p in s:
	if not(p['curve_label'] in Pts):
		Pts[p['curve_label']] = []
	Pts[p['curve_label']].append(p['coordinates'])
	if not(p['curve_label'] in FldLabels):
		FldLabels[p['curve_label']] = []
	FldLabels[p['curve_label']].append(p['residue_field'])
	AllFldLabels.add(p['residue_field'])

s = db.nf_fields.search(query={'label' : {'$in' : list(AllFldLabels)}}, projection={'label', 'coeffs'})
FldCoeffs = dict()
for f in s:
	FldCoeffs[f['label']] = f['coeffs']

OutputString = ""
for id in Crvs:
	C = Crvs[id]
	for i in C:
		OutputString += '<"' + str(id) + '",' + str(i) + '>\n'
		if not(id in Pts):
			continue
		OutputString += '['
		isFirst = True
		for j,Pt in enumerate(Pts[id]):
			if not(str(i) in Pt):
				continue
			if not(isFirst):
				OutputString += ','
				isFirst = False
			OutputString += '<' + str(FldCoeffs[FldLabels[id][j]]) + ',' + str(Pt[str(i)]).replace("'", '"') + '>'
		OutputString += ']\n'

with open("outputfile.txt", "w") as f:
	_ = f.write(OutputString)

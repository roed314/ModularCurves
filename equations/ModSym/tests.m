AttachSpec("ModCrv.spec");

load "magma_gl2zhat.m";
SetVerbose("ModularCurves", 1);
vprintf ModularCurves, 1:
    "Filtering groups of genus at least 2...";
high_genus := [x : x in magma_gl2zhat | StringToInteger(Split(x[1], ".")[3]) ge 2];
vprint ModularCurves, 1: "Done!\n";
max_level := Maximum([StringToInteger(Split(x[1], ".")[1]) : x in high_genus]);
vprintf ModularCurves, 1:
    "Orgainzing by level...";
by_level := [[x : x in high_genus | StringToInteger(Split(x[1], ".")[1]) eq N]
		: N in [1..max_level]];
vprint ModularCurves, 1: "Done!\n";
for level in [1..max_level] do
    for grp in by_level[level] do
	G := grp[2];
	PG := PSL2Subgroup(G);
	if IsOfRealType(PG) then
	    vprintf ModularCurves, 1: "Computing the canonical model...\n";
	    X<[x]>, fs := ModularCurve(PG);
	    vprint ModularCurves, 1: "Done!\n";
	    vprintf ModularCurves, 1: "Computing the j-map...\n";
	    E4, E6, j := JMap(PG, fs, AbsolutePrecision(fs[1]));
	    vprint ModularCurves, 1: "Done!\n";
	end if;
	print grp[1];
    end for;
end for;

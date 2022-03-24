AttachSpec("ModCrv.spec");

load "magma_gl2zhat.m";
high_genus := [x : x in magma_gl2zhat | StringToInteger(Split(x[1], ".")[3]) ge 2];
max_level := Maximum([StringToInteger(Split(x[1], ".")[1]) : x in high_genus]);
by_level := [[x : x in high_genus | StringToInteger(Split(x[1], ".")[1]) eq N]
		: N in [1..max_level]];

for level in [1..max_level] do
    for grp in by_level[level] do
	G := grp[2];
	PG := PSL2Subgroup(G);
	if IsOfRealType(PG) then
	    X<[x]>, fs := ModularCurve(PG);
	    E4, E6, j := JMap(PG, fs, AbsolutePrecision(fs[1]));
	end if;
	print grp[1];
    end for;
end for;

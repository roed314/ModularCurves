// Usage: magma -b level:=N gens:=&cat[Eltseq(g) : g in gens] name:=fname GetModel.m

AttachSpec("ModCrv.spec");

gens := [StringToInteger(x) : x in Split(gens, ",")];
// Should be a list of 2x2 matrices, so number of elements divisible by 4.
assert #gens mod 4 eq 0;
gens := [gens[4*(i-1)+1..4*i] : i in [1..#gens div 4]];
G := sub<GL(2, Integers(StringToInteger(level))) | gens>;
PG := PSL2Subgroup(GetRealConjugate(G));
// This code only works for groups that are of real type
assert IsOfRealType(PG);
// This code only works for groups of genus at least 2
assert Genus(PG) ge 2;
X<[x]>, fs := ModularCurve(PG);
E4, E6, j := JMap(PG, fs, AbsolutePrecision(fs[1]));
WriteModel(X, fs, E4, E6, name);

exit;

// Usage: ls input_data | parallel --timeout 600 magma -b label:={1} GetModelLMFDB.m
// where input_data is a folder containing one file for each label, consisting of the generators as a comma-separated list of integers

System("mkdir -p output_data");
SetColumns(0);
AttachSpec("ModCrv.spec");
SetVerbose("ModularCurves", 1);

level := StringToInteger(Split(label, ".")[1]);
gens := [StringToInteger(x) : x in Split(Read("input_data/" * label), ",")];
// Should be a list of 2x2 matrices, so number of elements divisible by 4.
assert #gens mod 4 eq 0;
gens := [gens[4*(i-1)+1..4*i] : i in [1..#gens div 4]];
G := sub<GL(2, Integers(level)) | gens>;
PG := PSL2Subgroup(GetRealConjugate(G));
// This code only works for groups that are of real type
assert IsOfRealType(PG);
// This code only works for groups of genus at least 2
assert Genus(PG) ge 2;
X<[x]>, fs, type := ModularCurve(PG);
LogCanonical := false;
if type eq "hyperelliptic" then
    vprintf ModularCurves, 1:
	"Curve is hyperelliptic, finding a log-canonical model for the j-map...\n";
    X<[x]>, fs := ModularCurve(PG : Al := "LogCanonical");
    LogCanonical := true;
end if;
E4, E6, j := JMap(PG, fs, AbsolutePrecision(fs[1])
		  : LogCanonical := LogCanonical);
LMFDBWriteModel(X, fs, E4, E6, "output_data/" * label);

exit;

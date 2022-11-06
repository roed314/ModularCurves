AttachSpec("ModCrv.spec");
import "ModularCurves.m" : CreateModularCurveRec, FindModelOfXG;

System("mkdir -p ../output_data");
SetColumns(0);

level := StringToInteger(Split(label, ".")[1]);
input := Read("../input_data/" * label);
input_lines := Split(input, "\n");
gens := [StringToInteger(x) : x in Split(input_lines[1], ",")];
// Should be a list of 2x2 matrices, so number of elements divisible by 4.
assert #gens mod 4 eq 0;
gens := [gens[4*(i-1)+1..4*i] : i in [1..#gens div 4]];
M := CreateModularCurveRec(level, gens);
assert M`genus ge 3;
prec := RequiredPrecision(M);
X := FindModelOfXG(M, prec);
E4, E6, j := JMap(X);
LMFDBWriteModel(X, E4, E6, "../output_data/" * label);
exit;

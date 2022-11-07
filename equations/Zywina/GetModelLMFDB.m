// Usage: ls input_data | parallel --timeout 600 magma -b label:={1} GetModelLMFDB.m
// where input_data is a folder containing one file for each label, consisting of the generators as a comma-separated list of integers

AttachSpec("ModCrv.spec");
import "findjinvmap.m" : FindJMapInv, GetPrecisionAndDegrees;
import "ModularCurves.m" : CreateModularCurveRec, FindCanonicalModel;

if (not assigned label) then
  printf "This script assumes that label, the label of the X_H to compute, is given as a command line paramter.\n";
  printf "Something like magma label:=7.168.3.1 findjmap.m\n";
  quit;  
end if;

System("mkdir -p ../output_data");
SetColumns(0);

level := StringToInteger(Split(label, ".")[1]);
input := Read("../input_data/" * label);
input_lines := Split(input, "\n");
gens := [StringToInteger(x) : x in Split(input_lines[1], ",")];
// Should be a list of 2x2 matrices, so number of elements divisible by 4.
assert #gens mod 4 eq 0;
// Here we transpose the matrices, because Zywina's code uses the 
// transposed convention of Galois action
gens := [[gens[4*i-3],gens[4*i-1],gens[4*i-2],gens[4*i]] : i in [1..#gens div 4]];
M := CreateModularCurveRec(level, gens);
assert M`genus ge 3;
prec, mind, maxd := GetPrecisionAndDegrees(M);
// X := FindModelOfXG(M, prec);
printf "Starting model computation.\n";
ttemp := Cputime();
flag, psi, F := FindCanonicalModel(M, prec);
if flag then
    M`k := 2;
    M`F0 := F;
    M`psi := psi;
else
    printf "The modular curve with label %o is geometrically hyperelliptic.\n",label;
    quit;
end if;
modeltime := Cputime(ttemp);
printf "Done. Time taken was %o.\n",modeltime;
printf "Model time = %o.\n",modeltime;
j := New(JMapData);
jmap, num, denom := FindJMapInv(M, prec, mind, maxd);
printf "Skipping E4, E6 computation.\n";
// eis_time := Cputime();
// j`E4, j`E6, _ := JMap(M);
// printf "E4,E6 time taken was %o. \n", eis_time;
j`J := num / denom;
LMFDBWriteModel(M, j, "../output_data/" * label);
exit;

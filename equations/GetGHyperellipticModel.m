// Usage: magma -b label:={1} GetGHyperellipticModel.m >> stdout/{1} 2>&1

load "hyperelliptic/load.m";
load "hyperelliptic/code.m";
SetColumns(0);
//SetVerbose("User1", 1);
//SetDebugOnError(true);
g := StringToInteger(Split(label, ".")[3]);
if not assigned prec then
    prec := 100;
else
    prec := StringToInteger(prec);
end if;
if g lt 3 then
    label cat ":genus too small";
    exit;
end if;
C := HyperellipticModelFromLabel(label : prec:=prec);
Write("ghyp_models/" * label, StripWhiteSpace(Sprint(DefiningEquations(C))));
exit;

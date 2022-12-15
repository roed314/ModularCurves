// Run after GetModelLMFDB.m
// Usage: magma -b label:={1} GetPlaneAndGonality.m >> stdout/{1} 2>&1

AttachSpec("equations.spec");
SetColumns(0);
SetDebugOnError(true);
if (not assigned label) then
    printf "This script assumes that label, the label of the X_H to compute, is given as a command line paramter.\n";
    printf "Something like magma label:=7.168.3.a.1 GetPlaneAndGonality.m\n";
    quit;
end if;

X, g, model_type, jnum, jden, cusps := LMFDBReadCanonicalModel(label);
Cs := LMFDBReadPlaneModel(label);
gon_bounds, Cs := PlaneModelAndGonalityBounds(X, Cs, g, (model_type eq -1), cusps);
LMFDBWriteGonalityBounds(gon_bounds, label);
if #Cs gt 0 then
    C := Curve(Proj(Parent(Cs[1][1])), Cs[1][1]);
    proj := Cs[1][2];
    LMFDBWritePlaneModel(C, proj, label);
end if;
exit;

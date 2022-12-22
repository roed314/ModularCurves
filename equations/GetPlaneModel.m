// Run after GetModelLMFDB.m
// Usage: magma -b label:={1} GetPlaneAndGonality.m >> stdout/{1} 2>&1

AttachSpec("equations.spec");
SetColumns(0);
if assigned verbose or assigned debug then
    SetVerbose("User1", 1);
end if;
if assigned debug then
    SetDebugOnError(true);
end if;
if (not assigned label) then
    printf "This script assumes that label, the label of the X_H to compute, is given as a command line paramter.\n";
    printf "Something like magma label:=7.168.3.a.1 GetPlaneModel.m\n";
    quit;
end if;

Cs := HighGenusPlaneModel(label::MonStgElt); // writes output to file
exit;

// Run after GetModelLMFDB.m, and ideally after finalizing a plane model
// Usage: magma -b label:={1} GetCuspCoordinates.m >> stdout/{1} 2>&1

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
    printf "Something like magma label:=7.168.3.a.1 GetCuspCoordinates.m\n";
    quit;
end if;

t0 := ReportStart(label, "pushing forward cusps");
X, model_type, g, cusps := LMFDBReadCusps(label);
Cs := LMFDBReadPlaneModel(label);
X := Curve(Proj(Universe(X)), X);
C := 0; // stupid magma needs this defined even if not used.
if #Cs gt 0 then
    C := Curve(Proj(Parent(Cs[1][1])), Cs[1][1]);
end if;
ans := [* *];
for cusp in cusps do
    K := Universe(cusp);
    P1K := ProjectiveSpace(K, 1);
    XK := ChangeRing(X, K);
    pt := XK!cusp;
    Append(~ans, <model_type, pt>);
    if #Cs gt 0 then
        CK := ChangeRing(C, K);
        T := ChangeRing(Universe(Cs[1][2]), K);
        CprojK := map<XK -> CK| [T!f : f in Cs[1][2]]>;
        Append(~ans, <2, pt @ CprojK>);
    end if;
end for;
LMFDBWriteCuspCoords(ans, label);
ReportEnd(label, "pushing forward cusps", t0);
exit;


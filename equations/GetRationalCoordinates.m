// Run after GetModelLMFDB.m (and, optionally, after GetPlanAndGonality.m)
// Usage: magma -b label:={1} GetRationalCoordinates.m >> stdout/{1} 2>&1

AttachSpec("equations.spec");
SetColumns(0);
if (not assigned label) then
    printf "This script assumes that label, the label of the X_H to compute, is given as a command line paramter.\n";
    printf "Something like magma label:=7.168.3.a.1 GetRationalCoordinates.m\n";
    quit;
end if;

jinvs := LMFDBReadJinvPts(label);
ans := [];
if #jinvs gt 0 then
    X, g, model_type, jnum, jden, cusps := LMFDBReadCanonicalModel(label);
    Cs := LMFDBReadPlaneModel(label);
    X := Curve(Proj(Universe(X)), X);
    if #Cs gt 0 then
        C := Curve(Proj(Parent(Cs[1][1])), Cs[1][1]);
    end if;
    P1K := AssociativeArray();
    XK := AssociativeArray();
    projK := AssociativeArray();
    for pair in jinvs do
        j, isolated := Explode(pair);
        K := Parent(j);
        if not IsDefined(P1K, K) then
            P1K[K] :=ProjectiveSpace(K, 1);
            XK[K] := ChangeRing(X, K);
            projK[K] := map<XK[K] -> P1K[K] | [jnum, jden]>;
            if #Cs gt 0 then
                CK[K] := ChangeRing(C, K);
                CprojK[K] := map<XK[K] -> CK[K]| [ChangeRing(f, K) : f in Cs[1][2]]>;
            end if;
        end if;
        P1pt := P1K[K]![j,1];
        Xpt := P1pt @@ (projK[K]);
        Xcoords := RationalPoints(Xpt);
        if #Xcoords eq 0 then
            printf "Error: no point on %o above j=%o!\n", label, j;
            continue;
        end if;
        /*
        if Abs(isolated) le 1 then
            // We were unable to determine externally whether this point was P1-isolated
            // We first see if an improved gonality bound can solve the problem
            gon_bounds := LMFDBReadGonalityBounds(label);
            gon_low := gon_bounds[1];
            degree := Degree(K);
            if degree lt gon_low / 2 then
                isolated := 4;
            else
                // TODO
            end if;
        end if;
        */
        for coords in Xcoords do
            Append(~ans, <0, j, coords>);
        end for;
        if #Cs gt 0 then
            Cpt := Xpt @ (CprojK[K]);
            Ccoords := RationalPoints(Cpt);
            for coords in Ccoords do
                Append(~ans, <2, j, coords>);
            end for;
        end if;
    end for;
    LMFDBWriteJinvCoords(ans, label);
end if;
exit;

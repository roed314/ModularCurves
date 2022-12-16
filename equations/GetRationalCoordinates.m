// Run after GetModelLMFDB.m (and, optionally, after GetPlaneAndGonality.m)
// Usage: magma -b label:={1} GetRationalCoordinates.m >> stdout/{1} 2>&1

AttachSpec("equations.spec");
SetColumns(0);
//SetVerbose("User1", 1);
//SetDebugOnError(true);
if (not assigned label) then
    printf "This script assumes that label, the label of the X_H to compute, is given as a command line paramter.\n";
    printf "Something like magma label:=7.168.3.a.1 GetRationalCoordinates.m\n";
    quit;
end if;

jinvs := LMFDBReadJinvPts(label);
ans := [* *];
if #jinvs gt 0 then
    t0 := ReportStart(label, "pulling back j-invariants");
    QQ := Rationals();
    X, g, model_type, jnum, jden, cusps := LMFDBReadCanonicalModel(label);
    Cs := LMFDBReadPlaneModel(label);
    X := Curve(Proj(Universe(X)), X);
    if #Cs gt 0 then
        C := Curve(Proj(Parent(Cs[1][1])), Cs[1][1]);
    end if;
    P1K := AssociativeArray();
    XK := AssociativeArray();
    projK := AssociativeArray();
    CK := AssociativeArray();
    CprojK := AssociativeArray();
    function AsNF(K)
        if K eq QQ then
            return RationalsAsNumberField();
        else
            return K;
        end if;
    end function;
    procedure AddNF(~P1K, ~XK, ~projK, ~CK, ~CprojK, Cs, K)
        k := AsNF(K);
        if not IsDefined(P1K, k) then
            P1K[k] :=ProjectiveSpace(K, 1);
            XK[k] := ChangeRing(X, K);
            projK[k] := map<XK[k] -> P1K[k] | [jnum, jden]>;
            if #Cs gt 0 then
                CK[k] := ChangeRing(C, K);
                T := ChangeRing(Universe(Cs[1][2]), K);
                CprojK[k] := map<XK[k] -> CK[k]| [T!f : f in Cs[1][2]]>;
            end if;
        end if;
    end procedure;
    for pair in jinvs do
        j, isolated := Explode(pair);
        K := Parent(j);
        AddNF(~P1K, ~XK, ~projK, ~CK, ~CprojK, Cs, K);
        k := AsNF(K);
        P1pt := P1K[k]![j,1];
        Xpt := P1pt @@ (projK[k]);
        t1 := ReportStart(label, Sprintf("computing rational points above j=%o", j));
        Xcoords := RationalPoints(Xpt);
        ReportEnd(label, Sprintf("computing rational points above j=%o", j), t1);
        // Throw out points that actually lie in a subfield
        Xcoords := [pt : pt in Xcoords | Degree(sub<K | Eltseq(pt)>) eq Degree(K)];
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
        for pt in Xcoords do
            Append(~ans, <0, j, pt>);
        end for;
        if #Cs gt 0 then
            // This produces extra points, which I think are singular
            //Cpt := Xpt @ (CprojK[k]);
            //Ccoords := RationalPoints(Cpt);
            //for coords in Ccoords do
            //    Append(~ans, <2, j, coords>);
            //end for;
            for pt in Xcoords do
                Append(~ans, <2, j, (XK[k]!pt) @ CprojK[k]>);
            end for;
        end if;
    end for;
    // Add the cusps
    for cusp in cusps do
        K := Universe(cusp);
        AddNF(~P1K, ~XK, ~projK, ~CK, ~CprojK, Cs, K);
        k := AsNF(K);
        pt := XK[k]!cusp;
        Append(~ans, <0, "oo", pt>);
        if #Cs gt 0 then
            Append(~ans, <2, "oo", pt @CprojK[k]>);
        end if;
    end for;

    LMFDBWriteJinvCoords(ans, label);
    ReportEnd(label, "pulling back j-invariants", t0);
end if;
exit;

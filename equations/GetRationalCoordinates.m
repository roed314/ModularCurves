// Run after GetModelLMFDB.m, and ideally after finalizing a plane model
// Usage: magma -b label:={1} GetRationalCoordinates.m >> stdout/{1} 2>&1

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
    printf "Something like magma label:=7.168.3.a.1 GetRationalCoordinates.m\n";
    quit;
end if;

jinvs := LMFDBReadJinvPts(label);
ans := [* *];
if #jinvs gt 0 then
    t0 := ReportStart(label, "pulling back j-invariants");
    QQ := Rationals();
    X, model_type, codomain, j := LMFDBReadJMap(label);
    Cs := LMFDBReadPlaneModel(label);
    if #codomain eq 0 then
        Y := ProjectiveSpace(QQ, 1);
        jinvs := [* <[pair[1], 1], pair[2]> : pair in jinvs *];
    else
        Y, gY, modtY := LMFDBReadXGModel(codomain);
        Y := Curve(Proj(Universe(Y)), Y);
        Ycoords := LMFDBReadJinvCoords(codomain : can_only:=true);
        // The field of definition may be different for Y and X, so we need to track embeddings of these fields
        new_jinvs := [* *];
        roots := AssociativeArray();
        for Lpair in jinvs do
            jL, isolated := Explode(Lpair);
            L := Parent(jL);
            fL := DefiningPolynomial(L);
            for K -> clist in Ycoords do
                fK := DefiningPolynomial(K);
                if IsDefined(roots, <fK, fL>) then
                    rts := roots[<fK, fL>];
                else
                    rts := Roots(fK, L);
                    roots[<fK, fL>] := rts;
                end if;
                for Kpair in clist do
                    for r in rts do
                        emb := hom<K -> L | r>;
                        jK, Kcoord := Explode(Kpair);
                        if emb(jK) eq jL then
                            Append(~new_jinvs, <jL, [emb(c) : c in Kcoord]>);
                            // There may be multiple embeddings of K into L that map the j-invariant correctly; we only one one of them since we only want one representative per Galois orbit.
                            break;
                        end if;
                    end for;
                end for;
            end for;
        end for;
        jinvs := new_jinvs;
    end if;
    X := Curve(Proj(Universe(X)), X);
    if #Cs gt 0 then
        C := Curve(Proj(Parent(Cs[1][1])), Cs[1][1]);
    end if;
    auts := AssociativeArray();
    for pair in jinvs do
        jL, isolated := Explode(pair);
        L := Universe(jL);
        if L eq QQ then
            autL := [];
        elif IsDefined(auts, L) then
            autL := auts[L];
        else
            autL := [sigma : sigma in Automorphisms(L) | sigma(L.1) ne L.1];
            auts[L] := autL;
        end if;
        YL := ChangeRing(Y, L);
        XL := ChangeRing(X, L);
        projL := map<XL -> YL | j>;
        if #Cs gt 0 then
            CL := ChangeRing(C, L);
            T := ChangeRing(Universe(Cs[1][2]), L);
            CprojL := map<XL -> CL| [T!f : f in Cs[1][2]]>;
        end if;
        Ypt := YL!jL;
        Xpt := Ypt @@ (projL);
        t1 := ReportStart(label, Sprintf("computing rational points above j=%o", jL));
        Xcoords := RationalPoints(Xpt);
        ReportEnd(label, Sprintf("computing rational points above j=%o", jL), t1);
        Xcoords := [Eltseq(pt) : pt in Xcoords];
        // Throw out points that actually lie in a subfield
        if L ne QQ then
            Xcoords := [pt : pt in Xcoords | Degree(sub<L | pt>) eq Degree(L)];
        end if;
        // Only keep one point from each Galois orbit
        if #autL gt 0 and #Xcoords gt 1 then
            trimmed := [];
            while #Xcoords gt 0 do
                pt := Xcoords[1];
                Remove(~Xcoords, 1);
                Append(~trimmed, pt);
                for sigma in autL do
                    Exclude(~Xcoords, [sigma(c) : c in pt]); // We're assuming that the coordinates are normalized so that we can just test equality of eltseq
                end for;
            end while;
            Xcoords := trimmed;
        end if;
        if #Xcoords eq 0 then
            printf "Error: no point on %o above j=%o!\n", label, jL;
            continue;
        end if;
        /*
        if Abs(isolated) le 1 then
            // We were unable to determine externally whether this point was P1-isolated
            // We first see if an improved gonality bound can solve the problem
            gon_bounds := LMFDBReadGonalityBounds(label);
            gon_low := gon_bounds[1];
            degree := Degree(L);
            if degree lt gon_low / 2 then
                isolated := 4;
            else
                // TODO
            end if;
        end if;
        */
        for pt in Xcoords do
            Append(~ans, <model_type, jL, pt>);
        end for;
        if #Cs gt 0 then
            // This produces extra points, which I think are singular
            //Cpt := Xpt @ (CprojL);
            //Ccoords := RationalPoints(Cpt);
            //for coords in Ccoords do
            //    Append(~ans, <2, j, coords>);
            //end for;
            for pt in Xcoords do
                Append(~ans, <2, jL, (XL!pt) @ CprojL>);
            end for;
        end if;
    end for;
    LMFDBWriteJinvCoords(ans, label);
    ReportEnd(label, "pulling back j-invariants", t0);
end if;
exit;

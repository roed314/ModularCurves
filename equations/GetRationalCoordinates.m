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
        // For now, we ignore isolatedness
        // Instead, the first coordinate is the j-invariant, and the second is the X-Y coordinates on P1.
        jinvs := [* <pair[1], [pair[1], 1]> : pair in jinvs *];
    else
        Y, gY, modtY := LMFDBReadXGModel(codomain);
        Y := Curve(Proj(Universe(Y)), Y);
        // The computation of rational points on the codomain may have timed out,
        // in which case we just want to exit.
        try
            Ycoords := LMFDBReadJinvCoords(codomain : can_only:=true);
        catch e
            print "Rational points not computed in codomain";
            exit;
        end try;
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
    base_points := AssociativeArray();
    base_points_dict := AssociativeArray();
    XLD := AssociativeArray();
    YLD := AssociativeArray();
    projLD := AssociativeArray();
    for pair in jinvs do
        jL, cod_coord := Explode(pair);
        L := Parent(jL);
        fL := DefiningPolynomial(L); // We cache using fL since it works for QQ as well as number fields
        RL := Parent(fL);
        AssignCanonicalNames(~RL);
        if IsDefined(auts, fL) then
            autL := auts[fL];
            YL := YLD[fL];
            XL := XLD[fL];
            projL := projLD[fL];
            bp := base_points[fL];
            bpd := base_points_dict[fL];
        else
            autL := [sigma : sigma in Automorphisms(L) | sigma(L.1) ne L.1];
            auts[fL] := autL;
            YL := ChangeRing(Y, L);
            YLD[fL] := YL;
            XL := ChangeRing(X, L);
            XLD[fL] := XL;
            projL := map<XL -> YL | j>;
            projLD[fL] := projL;
            t1 := ReportStart(label, Sprintf("computing j-map on base points for L=%o", sprint(fL)));
            bp := [pt : pt in BasePoints(projL) | L eq QQ or Degree(sub<L | Eltseq(pt)>) eq Degree(L)];
            base_points[fL] := bp;
            bpd := AssociativeArray();
            for P in bp do
                val := P @ projL;
                if not IsDefined(bpd, val) then
                    bpd[val] := [];
                end if;
                Append(~bpd[val], Eltseq(P));
            end for;
            base_points_dict[fL] := bpd;
            ReportEnd(label, Sprintf("computing j-map on base points for L=%o", fL), t1);
        end if;
        if #Cs gt 0 then
            CL := ChangeRing(C, L);
            T := ChangeRing(Universe(Cs[1][2]), L);
            CprojL := map<XL -> CL| [T!f : f in Cs[1][2]]>;
        end if;
        Ypt := YL!cod_coord;
        Xpt := Ypt @@ (projL);
        t1 := ReportStart(label, Sprintf("computing rational points above j=%o", jL));
        Xcoords := RationalPoints(Xpt);
        ReportEnd(label, Sprintf("computing rational points above j=%o", jL), t1);
        // Xpt contains everything in the indeterminacy locus, so they may not all map to the correct j-invariant
        Xcoords := [Eltseq(pt) : pt in Xcoords | not (pt in bp) and (L eq QQ or Degree(sub<L | Eltseq(pt)>) eq Degree(L))] cat Get(bpd, Ypt, []);
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

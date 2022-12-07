intrinsic IdentifyAffinePatch(KC::FldFunFracSch) -> Any
  {Return the index of the variable used to create affine patch, i.e., the one used as a denominator}
  dens := [Denominator(ProjectiveRationalFunction(KC.i)) : i in [1..Rank(KC)]];
  R := Parent(dens[1]);
  proj_vars := GeneratorsSequence(R);
  ds := [el : el in dens | el in proj_vars];
  assert #Seqset(ds) eq 1; // should all have same denominator, if it's one of the variables
  return Index(proj_vars,ds[1]);
end intrinsic;

intrinsic MakeAffineVariableList(KC::FldFunFracSch, ind::RngIntElt) -> Any
  {}
  return [KC.i : i in [1..(ind-1)]] cat [KC!1] cat [KC.i : i in [ind..Rank(KC)]];
end intrinsic;

intrinsic RationalFunctionToFunctionFieldElement(C::Crv, j::FldFunRatMElt) -> Any
  {Convert FldFunRatMElt to FldFunFracSchElt}
  KC := FunctionField(C);
  ind := IdentifyAffinePatch(KC);
  j_Cs := [];
  for f in [Numerator(j), Denominator(j)] do
    f_C := Evaluate(f, MakeAffineVariableList(KC,ind));
    Append(~j_Cs,f_C);
  end for;
  return j_Cs[1]/j_Cs[2];
end intrinsic;

intrinsic JMapSanityCheck(j::FldFunFracSchElt) -> BoolElt
  {Make sure that the j-map is only ramified above 0, 1728, oo}

  pts, mults := Support(Divisor(Differential(j)));
  for el in pts do
    val := j(RepresentativePoint(el));
    if not ((val eq 0) or (val eq 1728) or (val eq Infinity())) then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic DegreeLowerBound(g::RngIntElt) -> RngIntElt
  {A lower bound for the degree of the plane model for a curve of genus g}
  assert g ge 0;
  if g eq 0 then
    return 1;
  elif g eq 1 then
    return 3;
  else
    return Ceiling((3+Sqrt(1+8*g)/2));
  end if;
end intrinsic;

intrinsic DegreeUpperBound(g::RngIntElt) -> RngIntElt
  {A upper bound for the degree of the plane model for a curve of genus g, embedded using}
  assert g ge 4;
  return 4*(g-1)-3;
end intrinsic;

intrinsic PlaneModelFromQExpansions(rec::Rec : prec:=0) -> BoolElt, Crv
{rec should be of type ModularCurveRec, genus larger than 3 and not hyperelliptic}
    if prec eq 0 then
        prec := rec`prec;
    end if;
    if not assigned rec`F then
        rec := FindModularForms(2,rec,prec);
    end if;
    if not assigned rec`F0 then
        rec := FindCuspForms(rec);
    end if;

    found_bool := false;
    //m := 5;
    m := DegreeLowerBound(rec`genus);
    U := DegreeUpperBound(rec`genus);
    while (not found_bool) and (m le U) do
        printf "Plane model: trying relations of degree = %o\n", m;
        rels := FindRelations((rec`F0)[1..3],m);
        if #rels gt 0 then
            print "Plane model: relation found!";
            found_bool := true;
        end if;
        m +:= 1;
    end while;
    if #rels eq 0 then
        print "No relations found!";
        return false, _;
    end if;

    f := rels[1];
    C := Curve(Proj(Parent(f)), f);
    print "Plane model: curve found!";
    print C;
    // assert Genus(C) eq rec`genus; // sanity check
    return true, C;
end intrinsic;

intrinsic PlaneModelAndGonalityBounds(X::SeqEnum, C::SeqEnum, g::RngIntElt, ghyp::BoolElt, cusps::SeqEnum : try_gonal_map:=true) -> Tup, SeqEnum
{
    Input:
            X:     equations for the modular curve as produced by GetModelLMFDB.m
            C:     a sequence of length 0 or 1 of known plane models (provided as a polynomial in X,Y,Z).  If given, the map from X will
                   just be projection onto the first three coordinates
            g:     the genus of X
            ghyp:  whether X is geometrically hyperelliptic
            cusps: the rational cusps on X
    Output:
            bounds a 4-tuple giving gonality bounds: q_low, q_high, qbar_low, qbar_high
            C:     a sequence of length 0 or 1 of known plane models (provided as a tuple, with first entry the defining polynomial and the second entry a sequence of three polynomials giving the map from X to C)
}
    P := Parent(X[1]);
    opts := [* <f, [P.1, P.2, P.3]> : f in C *];
    procedure add_opt(mp)
        f := DefiningEquation(Codomain(mp));
        R := Parent(f);
        AssignNames(~R, ["X","Y","Z"]);
        Append(~opts, <f, DefiningEquations(mp)>);
    end procedure;

    // Get gonality in low genus
    q_low := 2; // overwritten in some cases
    qbar_low := 2; // overwritten in some cases
    degrees := [[Degree(X[j], P.i): i in [1..Ngens(P)]]: j in [1..#X]];
    q_high := Min([Min([d: d in degrees[j] | d ne 0]): j in [1..#X]]);
    if g eq 0 then
        q_low := q_high; // Rakvi's code will give a conic precisely when there are no points
        qbar_low := 1;
        qbar_high := 1;
    elif g eq 1 then
        qbar_high := 2;
       // don't change q_high: a genus 1 curve can require an arbitrarily large extension to acquire a point
    elif g eq 2 then
        q_high := 2;
        qbar_high := 2;
    else
        if g le 6 and try_gonal_map then
            ambient := ProjectiveSpace(P);
            curve := Curve(ambient, X);
            if g eq 3 then
	        qbar_low, gonal_map := Genus3GonalMap(curve : IsCanonical:=not ghyp);
            elif g eq 4 then
	        qbar_low, gonal_map := Genus4GonalMap(curve : IsCanonical:=not ghyp);
            elif g eq 5 then
	        qbar_low, gonal_map := Genus5GonalMap(curve : IsCanonical:=not ghyp);
            else
	        qbar_low, _, gonal_map := Genus6GonalMap(curve : IsCanonical:=not ghyp);
            end if;
            q_low := qbar_low;
            qbar_high := qbar_low;
            // If gonal map is rational, get q_high as well
            F := BaseField(Domain(gonal_map));
            if F eq Rationals() then
	        q_high := qbar_high;
                P1<s,t> := Codomain(gonal_map);
                X_aff := AffinePatch(curve, 1);
                gonal_map_polys := [AlgebraMap(gonal_map)(g) : g in [s,t]];
                gonal_aff := [Evaluate(p, [1] cat GeneratorsSequence(CoordinateRing(X_aff))) : p in gonal_map_polys];
                FFX := FunctionField(curve);
                gonal_ffx := FFX!gonal_aff[1] / FFX!gonal_aff[2];
                f := MinimalPolynomial(gonal_ffx);
                if q_high eq 3 then
                    ; // We can eliminate the quadratic term to get y^3 + g(x)y = f(x), then clear denominators
                end if;
                // TODO: Need to use f to get a model, together with maps

            end if;
        elif ghyp then
            qbar_high := 2;
            hyp, H, h_map := IsHyperelliptic(curve);
            if hyp then
                q_high := 2;
                // TODO: include H in opts, together with a map
            else
                q_low := 4;
                q_high := 4;
                // Use IsGeometricallyHyperelliptic or Edgar and Raymond's code to find model as double cover of conic
            end if;
        else
            // Everything is between 2 and q_high
            qbar_low := 2;
            qbar_high := q_high;
        end if;
    end if;

    // Use rational cusps (and maybe a short rational point search?) to project

    if g eq 5 then
        ok, f := Genus5PlaneCurveModel(X : IsCanonical:=not ghyp);
        if ok then add_opt(f); end if;
    end if;
    // Sam suggests Ciaran's code for improving coefficients: https://github.com/SamSchiavone/Gm-Reduce/blob/main/linear-program.m#L218
    function pick_best(L)
        _, i := Min([#sprint(pair[1]) : pair in L]);
        return L[i];
    end function;
    if #opts gt 1 then
        opts := [pick_best(opts)];
    end if;
    return <q_low, q_high, qbar_low, qbar_high>, [pair : pair in opts];
end intrinsic;

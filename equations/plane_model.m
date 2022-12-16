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


// Several methods for checking whether the projection onto the plane curve is birational.
// It is possible that some of these methods might claim that a projection is invalid when
// it is actually valid (if we hit some bad points), but the claim that a projection is
// valid does not rely on avoiding bad points.
reduction_prime := 997; // should be larger than the level

intrinsic HasIndeterminacy(Igens::SeqEnum, lin_forms::SeqEnum) -> BoolElt
{Checks whether there is a common zero locus for the linear forms defining the projection.}
    I := Ideal(Igens cat lin_forms);
    return not IsProper(I);
end intrinsic;

intrinsic ValidPlaneModel(f::RngMPolElt, g::RngIntElt) -> BoolElt
{A quick check for whether the plane curve defined by f is a valid reduction}
    p := reduction_prime;
    fbar := ChangeRing(f, GF(p));
    return IsIrreducible(fbar) and Genus(Curve(Proj(Parent(f)), f)) eq g;
end intrinsic;

intrinsic ValidPlaneModel2(f::RngMPolElt, X::Crv, proj::ModMatRngElt) -> BoolElt
{A quick check for whether the plane curve defined by f is a valid reduction}
    p := reduction_prime;
    fbar := ChangeRing(f, GF(p));
    if not IsIrreducible(fbar) then return false; end if;
    C := Curve(Proj(Parent(f)), f);
    R := Parent(DefiningEquations(X)[1]);
    Rgens := [R.i : i in [1..NumberOfGenerators(R)]];
    coords := [&+[Rgens[i] * proj[j,i] : i in [1..#Rgens]] : j in [1..3]];
    pi := map<X -> C | coords>;
    return Degree(pi) eq 1;
end intrinsic;

intrinsic ValidPlaneModel3(f::RngMPolElt, X::Crv, proj::ModMatRngElt) -> BoolElt
{A quick check for whether the plane curve defined by f is a valid reduction}
    p := reduction_prime;
    fbar := ChangeRing(f, GF(p));
    if not IsIrreducible(fbar) then return false; end if;
    C := Curve(Proj(Parent(fbar)), fbar);
    P := Random(C(GF(p)));
    Igens := DefiningEquations(X);
    R := ChangeRing(Parent(Igens[1]), GF(p));
    Igens := [R!g : g in Igens];
    coords := [&+[R.i * proj[j,i] : i in [1..NumberOfGenerators(R)]] : j in [1..3]];
    // If there is some point on the canonical model where all three linear forms vanish, then
    // computing the degree by counting preimages is not necessarily right
    if HasIndeterminacy(Igens, coords) then return false; end if;
    Igens cat:= [coords[j] - P[j] : j in [1..3]];
    I := Ideal(Igens);
    // If there's only one preimage (as a point over Fpbar), then the degree will be 1.
    return IsMaximal(I) and #(R / I) eq p;
end intrinsic;

intrinsic F0Combination(F0::SeqEnum, M::ModMatRngElt) -> SeqEnum
{F0 is as in ModularCurveRec, M is a 3 by n matrix over the integers with full rank, where n is the length of F0.
Applies the matrix M to the expansions, projecting F0 onto 3 modular forms (given by expansions at cusps as normal)}
    // I can't get matrix vector multiplication working reasonably, so we do this by hand
    //vecs := [Vector([F0[i][j] : i in [1..#F0]]) : j in [1..#F0[1]]];
    //vec3s := [v * Transpose(M) : v in vecs];
    //return [[vec3s[i][j] : i in [1..#vec3s]] : j in [1..3]];
    ans := [[Parent(F0[1][1])!0 : a in [1..#F0[1]]] : j in [1..3]];
    for a in [1..#F0[1]] do
        for j in [1..3] do
            for i in [1..#F0] do
                ans[j][a] +:= M[j][i] * F0[i][a];
            end for;
        end for;
    end for;
    return ans;
end intrinsic;

ProjectorRec := recformat<n, poss_pivots, cur_idx_pivots, max_idx_pivots, nonpiv_vecmax, nonpiv_ctr>;

intrinsic InitProjectorRec(n::RngIntElt) -> Rec
{INPUT: n >= 4,
Initializes the state object for iterating over certain full-rank 3xn matrices}
    poss_pivots := [Reverse(x) : x in Sort([Reverse(SetToSequence(pivs)) : pivs in Subsets({1..n}, 3)])];
    return rec<ProjectorRec | n:=n, poss_pivots:=poss_pivots, cur_idx_pivots:=1, max_idx_pivots:=2, nonpiv_vecmax:=[0 : _ in [1..#poss_pivots]], nonpiv_ctr:=[0 : _ in [1..#poss_pivots]]>;
end intrinsic;

intrinsic NextProjector(~state::Rec, ~M::ModMatRngElt)
{Updates M to be the next projector matrix, as iterated through by the state object}
    pividx := state`cur_idx_pivots;
    pivots := state`poss_pivots[pividx];
    v := state`nonpiv_ctr[pividx];
    vmax := state`nonpiv_vecmax[pividx];
    if vmax eq 0 then
        nonpivs := [];
    else
        nonpivs := IntegerToSequence(v, 2*vmax + 1);
        for j in [1..#nonpivs] do
            if nonpivs[j] mod 2 eq 1 then
                nonpivs[j] := 1 + (nonpivs[j] div 2);
            else
                nonpivs[j] := -nonpivs[j] div 2;
            end if;
        end for;
    end if;
    nonpivs cat:= [0 : _ in [1..3*state`n - 9]];
    ML := [[0 : i in [1..state`n]] : j in [1..3]];
    for j in [1..3] do
        ML[j][pivots[j]] := 1;
    end for;
    npctr := 1;
    for i in [1..state`n] do
        if i in pivots then continue; end if;
        for j in [1..3] do
            ML[j][i] := nonpivs[npctr];
            npctr +:= 1;
        end for;
    end for;
    M := Matrix(ML);

    // Now we update the state
    if v eq (2*vmax+1)^(3*state`n - 9) - 1 then
        state`nonpiv_vecmax[pividx] +:= 1;
        state`nonpiv_ctr[pividx] := 2*state`nonpiv_vecmax[pividx] - 1;
    else
        repeat
            state`nonpiv_ctr[pividx] +:= 1;
        until Max(IntegerToSequence(state`nonpiv_ctr[pividx], 2*state`nonpiv_vecmax[pividx]+1)) ge 2*state`nonpiv_vecmax[pividx] - 1;
    end if;
    if pividx eq state`max_idx_pivots then
        if state`max_idx_pivots lt #state`poss_pivots then
            state`max_idx_pivots +:= 1;
        end if;
        state`cur_idx_pivots := 1;
    else
        state`cur_idx_pivots +:= 1;
    end if;
end intrinsic;

intrinsic PlaneModelFromQExpansions(rec::Rec, Can::Crv, label::MonStgElt : prec:=0) -> BoolElt, Crv, SeqEnum
{rec should be of type ModularCurveRec, genus larger than 3 and not hyperelliptic}
    assert reduction_prime gt rec`level;
    t0 := ReportStart(label, "PlaneModelFromQExpansions");
    if prec eq 0 then
        prec := rec`prec;
    end if;
    if not assigned rec`F then
        rec := FindModularForms(2,rec,prec);
    end if;
    if not assigned rec`F0 then
        rec := FindCuspForms(rec);
    end if;

    g := rec`genus;
    low := DegreeLowerBound(g);
    high := DegreeUpperBound(g);
    rels := [];
    state := InitProjectorRec(g);
    M := ZeroMatrix(Integers(), 3, g);
    valid := [];
    R<X,Y,Z> := PolynomialRing(Rationals(), 3);
    trel := 0;
    tval := 0;
    t0 := ReportStart(label, "searching for plane models");
    repeat
        NextProjector(~state, ~M);
        MF := F0Combination(rec`F0, M);
        for m in [low..high] do
            ttmp := Cputime();
            rels := FindRelations(MF, m);
            trel +:= Cputime() - ttmp;
            if #rels gt 0 then
                ttmp := Cputime();
                //vld := ValidPlaneModel(rels[1], g);
                vld := ValidPlaneModel3(R!rels[1], Can, M);
                tval +:= Cputime() - ttmp;
                if vld then
                    vprint User1: Sprintf("Plane model: found valid model of degree = %o", m);
                    Append(~valid, <R!rels[1], Eltseq(M)>);
                else
                    vprint User1: Sprintf("Plane model: invalid model of degree = %o", m);
                end if;
                break;
            end if;
        end for;
    until #valid ge 25 or state`nonpiv_ctr[1] ge 728 or (#valid gt 0 and Cputime() - t0 gt 120);
    ReportEnd(label, "searching for plane models", t0);
    ReportEnd(label, "plane model relations", 0 : elapsed:=trel);
    ReportEnd(label, "plane model validation", 0 : elapsed:=tval);
    if #valid eq 0 then
        return false, _, _;
    end if;
    // Pick the best
    sorter := [];
    rescaled := [* *];
    ttmp := ReportStart(label, "plane model reduction");
    adjusted := 0;
    QQ := Rationals();
    for i in [1..#valid] do
        f, adjust := reducemodel_padic(valid[i][1]);
        if f eq valid[i][1] then
            // reducemodel_padic seems to produce giant coefficients in cases where it does nothing
            adjust := [1 : _ in adjust];
        else
            adjust := [1 / QQ!a : a in adjust];
            adjusted +:= 1;
        end if;
        Append(~sorter, <#sprint(f), Max([#sprint(a) : a in adjust])>);
        Append(~rescaled, <f, [valid[i][2][j+1] * adjust[1 + (j div g)] : j in [0..3*g-1]]>);
    end for;
    ReportEnd(label, "plane model reduction", ttmp);
    tred := Cputime() - ttmp;
    _, i := Min(sorter);

    f, M := Explode(rescaled[i]);
    C := Curve(Proj(Parent(f)), f);
    vprint User1: Sprintf("Plane model: %o model(s) found\n", #valid);
    vprint User1: Sprintf("Plane model: %o adjusted, max projection size %o\n", adjusted, Max([#Sprint(x) : x in M]));
    vprint User1: valid[i][1];
    vprint User1: Sprintf("Plane model: shortened by %o\n", #sprint(valid[i][1]) - sorter[i][1]);
    vprint User1: f;
    vprint User1: Sprintf("Plane model: chosen %o\n", #[x : x in valid[i][2] | x ne 0] - 3);
    vprint User1: Matrix(Integers(), 3, g, valid[i][2]);
    return true, C, M;
end intrinsic;

intrinsic PlaneModelAndGonalityBounds(X::SeqEnum, C::SeqEnum, g::RngIntElt, ghyp::BoolElt, cusps::SeqEnum, label::MonStgElt : try_gonal_map:=true) -> Tup, SeqEnum
{
    Input:
            X:     equations for the modular curve as produced by GetModelLMFDB.m
            C:     a sequence of length 0 or 1 of known plane models (provided as a tuple, with first entry the defining polynomial in X,Y,Z and second entry a sequence of three polynomials giving the map from X to C).
            g:     the genus of X
            ghyp:  whether X is geometrically hyperelliptic
            cusps: the rational cusps on X
    Output:
            bounds a 4-tuple giving gonality bounds: q_low, q_high, qbar_low, qbar_high
            C:     a sequence of length 0 or 1 of known plane models (provided as a tuple, with first entry the defining polynomial and the second entry a sequence of three polynomials giving the map from X to C)
}
    P := Parent(X[1]);
    opts := [* f : f in C *];
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
            try
                t0 := ReportStart(label, "gonality");
                if g eq 3 then
	            qbar_low, gonal_map := Genus3GonalMap(curve : IsCanonical:=not ghyp);
                elif g eq 4 then
	            qbar_low, gonal_map := Genus4GonalMap(curve : IsCanonical:=not ghyp);
                elif g eq 5 then
	            qbar_low, gonal_map := Genus5GonalMap(curve : IsCanonical:=not ghyp);
                else
	            qbar_low, _, gonal_map := Genus6GonalMap(curve : IsCanonical:=not ghyp);
                end if;
                ReportEnd(label, "gonality", t0);
                q_low := qbar_low;
                qbar_high := qbar_low;
                // If gonal map is rational, get q_high as well
                F := BaseField(Domain(gonal_map));
                if F eq Rationals() then
	            q_high := qbar_high;
                /*
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
                */
                end if;
            catch e
                qbar_high := q_high;
                print Sprint(e) * "\n";
            end try;
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

    /*
    if g eq 5 then
        ok, f := Genus5PlaneCurveModel(X : IsCanonical:=not ghyp);
        if ok then add_opt(f); end if;
    end if;*/
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

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

// These two methods were slower approaches for checking whether a plane model was valid

intrinsic ValidPlaneModel(f::RngMPolElt, g::RngIntElt) -> BoolElt
{A quick check for whether the plane curve defined by f is a valid reduction}
    p := reduction_prime;
    fbar := ChangeRing(f, GF(p));
    return IsIrreducible(fbar) and Genus(Curve(Proj(Parent(f)), f)) eq g;
end intrinsic;
/*
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
*/

intrinsic ValidModel(proj::MapSch) -> BoolElt
{
Input:
    proj - a map between irreducible curves
Output:
    whether proj is birational.  Can return a false negative with low probability but shouldn't return false positives
}
    p := reduction_prime;
    X := Domain(proj);
    C := Codomain(proj);
    Xbar := ChangeRing(X, GF(p));
    Cbar := ChangeRing(C, GF(p));
    if not IsIrreducible(Cbar) then return false; end if;
    P := Random(Cbar(GF(p)));
    Igens := DefiningEquations(X);
    R := ChangeRing(Universe(Igens), GF(p));
    Igens := [R!g : g in Igens];
    coords := [R!g : g in DefiningEquations(proj)];
    if HasIndeterminacy(Igens, coords) then return false; end if;
    Igens cat:= [coords[j] - P[j] : j in [1..#coords]];
    I := Ideal(Igens);
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

function planemodel_gonbound(f)
    fP := Parent(f);
    degrees := [Degree(f, fP.i): i in [1..Ngens(fP)]];
    return Min([d: d in degrees | d ne 0]);
end function;

intrinsic planemodel_sortkey(f::RngMPolElt) -> Tup
{}
    return <planemodel_gonbound(f), #sprint(f)>;
end intrinsic;

intrinsic RecordPlaneModel(fproj::Tup, X::SeqEnum, best::SeqEnum, bestkey::Tup, label::MonStgElt : warn_invalid:=true) -> SeqEnum, Tup, BoolElt, FldReElt, FldReElt
{
Input:
    fproj - a pair, with the first value a polynomial in X,Y,Z defining a plane curve, and the second a sequence of length 3 giving the projection map from the canonical model
    X - the sequence of defining equations for the canonical model (or some other smooth model in the hyperelliptic case)
    best - the current best option, as a sequence of length 0 or 1 of records like fproj
    bestkey - the value of planemodel_sortkey for the best option
    label - the label of the modular curve (for writing to disc)
    warn_invalid - whether a warning should be printed if the model is invalid
Output:
    best - the new best option, which may be fproj or the old best option
    bestkey - the value of planemodel_sortkey on the best option
    valid - whether fproj was a valid model
    time_val - time spent on model validation
    time_red - time spent on reducemodel_padic
File input:
    gonality bounds from LMFDBReadGonalityBounds
File output:
    If the model is better than the currently known model, writes to disc using LMFDBWritePlaneModel
    If gonality bounds are improved, writes new ones using LMFDBWriteGonalityBounds
}
    f, proj := Explode(fproj);
    // First check whether the model is valid (to catch bugs elsewhere)
    XC := Curve(Proj(Universe(X)), X);
    C := Curve(Proj(Parent(f)), f);
    tval := Cputime();
    try
        projection := map<XC -> C | proj>;
    catch e
        print e;
        return best, bestkey, false, Cputime(tval), 0.0;
    end try;
    valid := ValidModel(projection);
    tval := Cputime(tval);
    if not valid then
        if warn_invalid then
            // We want the traceback
            try
                error "Invalid model";
            catch e
                print e`traceback;
            end try;
        end if;
        return best, bestkey, false, tval, 0.0;
    end if;
    tred := Cputime();
    f, adjust := reducemodel_padic(f);
    tred := Cputime(tred);
    skey := planemodel_sortkey(f);
    if #best eq 0 or skey lt bestkey then
        gonbounds := LMFDBReadGonalityBounds(label);
        QQ := Rationals(); // entries of adjust may be in degree 1 extension of Q
        proj := [proj[i] / QQ!adjust[i] : i in [1..3]];
        best := [<f, proj>];
        bestkey := skey;
        LMFDBWritePlaneModel(f, proj, label);
        if skey[1] lt gonbounds[2] then // improvement to the Q-gonality (and possibly Qbar-gonality)
            gonbounds[2] := skey[1];
            gonbounds[4] := Min(gonbounds[4], skey[1]);
            LMFDBWriteGonalityBounds(gonbounds, label);
        end if;
    end if;
    return best, bestkey, true, tval, tred;
end intrinsic;

intrinsic PlaneModelFromQExpansions(rec::Rec, Can::Crv, label::MonStgElt : prec:=0) -> BoolElt, Crv, SeqEnum
{rec should be of type ModularCurveRec, genus larger than 3 and not hyperelliptic}
    assert reduction_prime gt rec`level;
    t0 := ReportStart(label, "PlaneModelFromQExpansions");
    if prec eq 0 then
        prec := rec`prec;
    end if;
    if not assigned rec`F0 then
        if not assigned rec`F then
            rec := FindModularForms(2,rec,prec);
        end if;
        rec := FindCuspForms(rec);
    end if;

    g := rec`genus;
    low := DegreeLowerBound(g);
    high := DegreeUpperBound(g);
    rels := [];
    state := InitProjectorRec(g);
    M := ZeroMatrix(Integers(), 3, g);
    nvalid := 0;
    R<X,Y,Z> := PolynomialRing(Rationals(), 3);
    Rg := PolynomialRing(Rationals(), g); // variable names assigned in LMFDBWritePlaneModel
    CanEqs := DefiningEquations(Can);
    trel := 0.0;
    tval := 0.0;
    tred := 0.0;
    t0 := ReportStart(label, "searching for plane models");
    best := [];
    bestkey := <>;
    repeat
        NextProjector(~state, ~M);
        MF := F0Combination(rec`F0, M);
        for m in [low..high] do
            //ttmp := ReportStart(label, Sprintf("plane relation"));
            ttmp := Cputime();
            rels := FindRelations(MF, m);
            //ReportEnd(label, Sprintf("plane relation"), ttmp);
            trel +:= Cputime() - ttmp;
            if #rels gt 0 then
                f := R!rels[1];
                proj := [&+[M[i,j] * Rg.j : j in [1..g]] : i in [1..3]];
                best, bestkey, vld, tmpval, tmpred := RecordPlaneModel(<f, proj>, CanEqs, best, bestkey, label : warn_invalid:=false);
                tval +:= tmpval; tred +:= tmpred;
                if vld then
                    vprint User1: Sprintf("Plane model: found valid model of degree = %o", m);
                    nvalid +:= 1;
                else
                    vprint User1: Sprintf("Plane model: invalid model of degree = %o", m);
                end if;
                break;
            end if;
        end for;
    until nvalid ge 25 or state`nonpiv_ctr[1] ge 728 or (nvalid gt 0 and Cputime() - t0 gt 120);
    ReportEnd(label, "searching for plane models", t0);
    ReportEnd(label, "plane model relations", trel : elapsed:=trel);
    ReportEnd(label, "plane model validations", tval : elapsed:=tval);
    ReportEnd(label, "plane model reductions", tred : elapsed:=tred);
    if #best eq 0 then
        return false, _, _;
    end if;

    f, M := Explode(best[1]);
    C := Curve(Proj(Parent(f)), f);
    vprint User1: Sprintf("Plane model: %o model(s) found\n", nvalid);
    return true, C, M;
end intrinsic;

intrinsic planemodel_gonalitybound(X::Crv) -> Tup, RngIntElt
{
    Input:
            X:          a canonically embedded curve X, as returned by ProcessModel()
    Output:
            mp:         a tuple consisting of an equation defining a plane model C of X, and equations defining a map from X to C
            q_high:     a bound on the gonality of X coming from the x-coordinate on the plane model C
}
    FFX<[x]> := FunctionField(X);
    gens_FFX := Generators(FFX);
    newgens_FFX := [];
    for xx in gens_FFX do
        s := Sprint(xx);
        if s[[1,2,#s]] eq "x[]" then
            try
                _ := StringToInteger(s[3..#s-1]);
                Append(~newgens_FFX,xx);
            catch e;
            end try;
        end if;
    end for;
    if #newgens_FFX eq 1 then
        xx := newgens_FFX[1];
        yy := x[#x];
        minpolyy := MinimalPolynomial(yy);
        q_high := Degree(minpolyy);
        if q_high eq 1 then
            xx := x[#x];
            yy := newgens_FFX[1];
            minpolyy := MinimalPolynomial(yy);
            q_high := Degree(minpolyy);
        end if;
        coeffs := [[Coefficients(Numerator(c)),Coefficients(Denominator(c))] : c in Coefficients(minpolyy)];
        P2<[u]> := ProjectiveSpace(Rationals(),2);
        dens := [&+([0] cat [c[2][i]*u[1]^(i-1) : i in [1..#c[2]]]) : c in coeffs];
        lcmdens := LCM(dens);
        nums := [&+([0] cat [c[1][i]*u[1]^(i-1) : i in [1..#c[1]]]) : c in coeffs];
        plane_eqn := Parent(u[1]) ! &+[nums[i]*(lcmdens/dens[i])*u[2]^(i-1) : i in [1..#coeffs]];
        maxdeg := Degree(plane_eqn);
        monos_coeffs, monos := CoefficientsAndMonomials(plane_eqn);
        plane_eqn := &+[monos_coeffs[i]*monos[i]*u[3]^(maxdeg-Degree(monos[i])) : i in [1..#monos]];
/*
        plane_model := Curve(P2,plane_eqn);
        mp := map<X->plane_model | [xx,yy,1]>;
        return mp, q_high;
*/
        AssignNames(~P2,["X","Y","Z"]);
        xxmaptoP1 := map<X->ProjectiveSpace(Rationals(),1) | [xx,1]>;
        defeqsxx := DefiningEquations(xxmaptoP1);
        yymaptoP1 := map<X->ProjectiveSpace(Rationals(),1) | [yy,1]>;
        defeqsyy := DefiningEquations(yymaptoP1);
        lcmofdens := LCM(defeqsxx[2],defeqsyy[2]);
        return <plane_eqn, [defeqsxx[1]*lcmofdens/defeqsxx[2],defeqsyy[1]*lcmofdens/defeqsyy[2],lcmofdens]>, q_high;
    else
        return <1>, 1;
    end if;
end intrinsic;


function rational_interpolation(dat : denfac := 1, scalarbound := 2000000);
    if denfac ne 1 then
        datupdated := [<d[1],d[2]*Evaluate(denfac,d[1])> : d in dat];
        dat := datupdated;
    end if;
    Z := Integers();
    Q := Rationals();
    P := PolynomialRing(Rationals());
    test := Interpolation([Q ! d[1] : d in dat],[Q ! d[2] : d in dat]);
    if Degree(test) lt #dat/2 then
        return <P ! test,P ! denfac>;
    end if;
    nms := &cat[[[i,s-i] : i in [0..s]] : s in [0..100]];
    for nm in nms do
        n := nm[1];
        m := nm[2];
        interpolating_data_modp := [];
        for N := 10000 to 10100 do
            p := NthPrime(N);
            try
                datp := [<GF(p) ! d[1], GF(p) ! d[2]> : d in dat];
                Matp := Matrix(GF(p),#datp,m+n+2,[[d[1]^i : i in [0..n]] cat [d[2]*d[1]^i : i in [0..m]] : d in datp]);
                Matp := Transpose(Matp);
                kerp := Kernel(Matp);
                if Dimension(kerp) eq 0 then
                    continue nm;
                end if;
                assert Dimension(kerp) eq 1;
                v := Eltseq(kerp.1);
                ind := [i : i in [1..m+n+2] | v[i] ne 0][1];
                v := [Z ! (e/v[ind]) : e in v];
                Append(~interpolating_data_modp,<p,v>);
            catch e;
                continue N;
            end try;
        end for;
        vprint User1: Sprintf("The degrees of the numerator and denominator of the interpolating rational function are %o", nm);
        break;
    end for;

    for scal in [1..scalarbound] do
        interpolating_data := [CRT([scal*d[2][i] : d in interpolating_data_modp], [d[1] : d in interpolating_data_modp]) : i in [1..m+n+2]];
        l := LCM([d[1] : d in interpolating_data_modp]);
        result := [(Abs(r) lt Abs(l-r)) select r else r-l : r in interpolating_data];
        if #Sprint(result) lt 500 then
            return <-(P ! result[1..n+1]),(P ! result[n+2..m+n+2])*(P ! denfac)>;
        end if;
    end for;
end function;


intrinsic planemodel_fromgonalmap(gonal_map::MapSch) -> Tup
{
    Input:
            gonal_map:  a gonal map from a canonically embedded curve X, as returned by GenusNGonalMap for 3 <= N <= 6
    Output:
            result:     a tuple consisting of an equation defining a plane model C of X, and equations defining a map from X to C,
                        such that the x-coordinate on C corresponds to the given gonal map on X
}
    X := Domain(gonal_map);
    P<[x]> := AmbientSpace(X);
    Xeqs := Equations(X);
    P1 := Codomain(gonal_map);
    defeqs := DefiningEquations(gonal_map);
/*
    undefinedpts := PointsOverSplittingField(Scheme(P,Xeqs cat [defeqs[1]*defeqs[2]]));
*/
    n := Degree(gonal_map);

    FFX := FunctionField(X);
    f := FFX ! (defeqs[1]/defeqs[2]);

    V := CartesianPower([0,1],#x);
    V := [[w : w in v] : v in V];
    V := Sort(V, func<x,y|&+x-&+y>);

    for v in V do
        if &+v eq 0 then continue; end if;
        vprint User1: Sprintf("Trying %o", v);
        g := FFX ! ((&+[v[i]*x[i] : i in [1..#x]])/defeqs[2]);
        if f eq g then continue; end if;
        try
            allminpols := [];
            for i := 1 to 100 do
                pt := P1 ! [i,1];
                pullbk := PointsOverSplittingField(Pullback(gonal_map,pt));
                pullbk := SetToSequence(pullbk);
/*
                for invpt in pullbk do
                    try
                        feval := Evaluate(f,invpt);
                        if feval ne i then
                            Exclude(~pullbk,invpt);
                        end if;
                    catch e;
                        Exclude(~pullbk,invpt);
                    end try;
                end for;
*/
                actual_pullbk := [];
                for invpt in pullbk do
                    try
                        if gonal_map(invpt) eq pt then
                            Append(~actual_pullbk,invpt);
                        end if;
                    catch e;
                    end try;
                    if #actual_pullbk eq n then
                        pullbk := actual_pullbk;
                        break;
                    end if;
                end for;
                if #pullbk eq n then
                    try
                        minpol := &*{MinimalPolynomial(Evaluate(g,pt)) : pt in pullbk};
//                        minpol := MinimalPolynomial(Evaluate(g,pullbk[1]));
                    catch e;
                        continue i;
                    end try;
                    assert Degree(minpol) eq n;
                    Append(~allminpols,<i,minpol>);
                end if;
                if i mod 20 eq 0 then
                    vprint User1: Sprintf("Done computing %o pullbacks", i);
                end if;
            end for;
            vprint User1: "Done computing pullbacks, and minpolys of the value of g at the pullbacks";
            if #allminpols le 50 then continue v; end if;

            xs := [Rationals() ! dat[1] : dat in allminpols];
            coeffs := [[Coefficient(dat[2],i) : dat in allminpols] : i in [0..n]];
            vprint User1: "Trying to interpolate with rational function";
            coeffs_in_x := [];
            possible_denfac := 1;
            for i := n+1 to 1 by -1 do
                ithfunc := rational_interpolation([<xs[j],coeffs[i][j]> : j in [1..#xs]] : denfac := possible_denfac);
                if ithfunc[2] ne 1 then
                    possible_denfac := (ithfunc[2])/LeadingCoefficient(ithfunc[2]);
                end if;
                Append(~coeffs_in_x,ithfunc);
                vprint User1: Sprintf("Interpolated coefficient of Y^%o", i-1);
            end for;
            coeffs_in_x := Reverse(coeffs_in_x);

            P2<[u]> := ProjectiveSpace(Rationals(),2);
            lcmofdens := LCM([coe[2] : coe in coeffs_in_x]);
            clearing_dens := [PolynomialRing(Rationals()) ! (lcmofdens/coe[2]) : coe in coeffs_in_x];
            plane_eqn := &+[Evaluate(clearing_dens[i],u[1])*Evaluate(coeffs_in_x[i][1],u[1])*u[2]^(i-1) : i in [1..n+1]];
            maxdeg := Degree(plane_eqn);
            monos_coeffs, monos := CoefficientsAndMonomials(plane_eqn);
            plane_eqn := &+[monos_coeffs[i]*monos[i]*u[3]^(maxdeg-Degree(monos[i])) : i in [1..#monos]];
/*
            plane_model := Curve(P2,plane_eqn);
            P1 := ProjectiveSpace(Rationals(),1);
            mp := map<X->plane_model | [f,g,1]>;
            return mp
*/
            AssignNames(~P2,["X","Y","Z"]);
            result := <plane_eqn, [defeqs[1],&+[v[i]*x[i] : i in [1..#x]],defeqs[2]]>;
            return result;
        catch e;
//            printf "Error %o, for numerator of y-coordinate given by %o\n", e, v;
            continue v;
        end try;
    end for;
    error "No plane map computed from gonal map";
end intrinsic;

intrinsic planemodel_fromgonalmap2(gonal_map::MapSch, label::MonStgElt) -> Tup
{
    Input:
            gonal_map:  a gonal map from a canonically embedded curve X, as returned by GenusNGonalMap for 3 <= N <= 6
    Output:
            result:     a tuple consisting of an equation defining a plane model C of X, and equations defining a map from X to C,
                        such that the x-coordinate on C corresponds to the given gonal map on X
}
    X := Domain(gonal_map);
    P<[x]> := AmbientSpace(X);
    P1 := Codomain(gonal_map);
    n := Degree(gonal_map);
    defeqs := DefiningEquations(gonal_map);
    FFX := FunctionField(X);
    f := FFX ! (defeqs[1]/defeqs[2]);

    V := CartesianPower([0,1],#x);
    V := [[w : w in v] : v in V];
    V := Sort(V, func<x,y|&+x-&+y>);
    for v in V do
        if &+v eq 0 then continue; end if;
        vprint User1: Sprintf("Trying %o", v);
        g := FFX ! ((&+[v[i]*x[i] : i in [1..#x]])/defeqs[2]);
        if f eq g then continue; end if;
        try
            P2 := ProjectiveSpace(Rationals(),2);
            mp := map<X->P2 | [f,g,1]>;
            model := Image(mp);
            vprint User1: "Found map to P2";
            plane_eqn := Equations(model)[1];
            if ValidModel(Restriction(mp, X, model)) then
                AssignNames(~P2,["X","Y","Z"]);
                result := <plane_eqn, [defeqs[1],&+[v[i]*x[i] : i in [1..#x]],defeqs[2]]>;
                return result;
            elif ValidPlaneModel(plane_eqn, #x) then
                print  "Uncertain map validity", label;
                AA := Parent(plane_eqn);
                AssignCanonicalNames(~AA);
                CanEqs := DefiningEquations(X);
                Xpar := Universe(CanEqs);
                AssignCanonicalNames(~Xpar);
                print plane_eqn;
                print #x;
                print X;
            end if;
        catch e;
            print e;
            continue v;
        end try;
    end for;
end intrinsic;

function gonalitybound_fromfuncfield(eqs,ind);
    P := Parent(eqs[1]);
    ind2 := Random(Exclude([1..Rank(P)],ind));
    I := ideal<P|[Evaluate(Evaluate(pol,ind,1),ind2,1) : pol in eqs]>;
    G := GroebnerBasis(I);
    return &*[LeadingTotalDegree(G[i]) : i in [1..#G]];
end function;

intrinsic modelfromfuncfield_gonalitybound(X::Sch) -> Tup
{
    Input:
            X:          a canonically embedded curve X, as returned by ProcessModel()
    Output:
            model:      a model in P^n of X defined by generators and relations of its function field. n is small, but not necessarily 2.
            mp:         a map from X to P^n, with image cutting out the model
            q_high:     a bound on the gonality of X coming from a coordinate on the model C
}
    FFX<[x]> := FunctionField(X);
    gens_FFX := Generators(FFX) join {x[#x]};
    newgens_FFX := [];
    for xx in gens_FFX do
        s := Sprint(xx);
        if s[[1,2,#s]] eq "x[]" then
            try
                _ := StringToInteger(s[3..#s-1]);
                Append(~newgens_FFX,xx);
            catch e;
            end try;
        end if;
    end for;
//    newgens_FFX := newgens_FFX cat [x[#x]];
/*
    for xx in newgens_FFX do
        degxx := Degree(MinimalPolynomial(xx));
        if degxx eq 1 then
            first_coord := xx;
            Exclude(~newgens_FFX,xx);
            break;
        end if;
    end for;
    newgens_FFX := [first_coord] cat newgens_FFX;


//    q_high := &*[Degree(MinimalPolynomial(newgens_FFX[i])) : i in [2..#newgens_FFX]];
    s := Sprint(first_coord);
*/
    s := Sprint(newgens_FFX[1]);
    q_high := gonalitybound_fromfuncfield(Equations(X),StringToInteger(s[3..#s-1]));

    Pn := ProjectiveSpace(Rationals(),#newgens_FFX);
    mp := map<X->Pn | newgens_FFX cat [1]>;
    vprint User1: Sprintf("Found map to P%o using generators of function field", #newgens_FFX);
    model := Image(mp);
    vprint User1: Sprintf("Found image in P%o", #newgens_FFX);
/*
    mp := Restriction(mp,X,model);
    printf "Restricted map to image\n";
*/
    return model, mp, q_high;
/*
    Pn := ProjectiveSpace(Rationals(),#newgens_FFX);
    defeqs := [1 : i in [1..#newgens_FFX]];
    lcmofdens := 1;
    for i := 1 to #newgens_FFX do
        coordmaptoP1 := map<X->ProjectiveSpace(Rationals(),1) | [newgens_FFX[i],1]>;
        defeqscoord := DefiningEquations(coordmaptoP1);
        newmultiplier := defeqscoord[2]/GCD(lcmofdens,defeqscoord[2]);
        lcmofdens := LCM(lcmofdens,defeqscoord[2]);
        newgens_FFX[i] := defeqscoord[1];
        for j := 1 to i do
            newgens_FFX[j] := newgens_FFX[j]*newmultiplier;
        end for;
    end for;
    Append(~defeqs,lcmofdens);
    // To get the eqn of the new model, we do need to create the map from X to Pn
    return <eqn, [defeqsxx[1]*lcmofdens/defeqsxx[2],defeqsyy[1]*lcmofdens/defeqsyy[2],lcmofdens]>, q_high;
*/
end intrinsic;

intrinsic DefiningPolynomialsComposite(alpha, beta) -> SeqEnum
{Defining polynomials for alpha * beta}
    return [Evaluate(f,DefiningPolynomials(alpha)): f in DefiningPolynomials(beta)];
end intrinsic;

intrinsic projecttoplane(C::Sch, phi::MapSch, ratcusps::SeqEnum) -> Tup
{
    Input:
            C:          a model in P^n (n greater than 2) of the curve X returned by ProcessModel()
            phi:        a map from X to C
            ratcusps:   image under phi of the cusps on X returned by ProcessModel(), whenever rational
    Output:
            result:     a tuple consisting of an equation defining a plane model C of X, and equations defining a map from X to C
}
    if Dimension(AmbientSpace(C)) eq 2 then
        P2<X,Y,Z> := AmbientSpace(C);
        defeqsphi := DefiningEquations(phi);
        plane_eqn := DefiningEquation(C);
        return <plane_eqn, defeqsphi>; // TODO done
    end if;
    Pn := AmbientSpace(C);
    n := Dimension(Pn);
    Can := Domain(phi);
    vprint User1: Sprintf("The ambient space is now P%o", n);
    if ratcusps ne [] then
        cusp := ratcusps[1];
        ratcusps := ratcusps[2..#ratcusps];
        if IsSingular(C,cusp) then
            newmodel, projmap := Projection(C,cusp);
            vprint User1: "Computed new projection map";
        else
            newmodel, projmap, out3blowup := ProjectionFromNonsingularPoint(C,cusp);
            vprint User1: "Computed new projection map";
        end if;
        // newphi := phi*projmap;
        // defeqsnewphi := DefiningPolynomials(newphi);
        // invdefeqsnewphi := InverseDefiningPolynomials(newphi); This is only birational, so don't have inverse
        // return projecttoplane(newmodel, map<X->newmodel|defeqsnewphi,invdefeqsnewphi>, ratcusps);
    else
        pt := Pn ! ([1] cat [0 : i in [1..n]]);
        newmodel, projmap := Projection(C,pt);
        vprint User1: "Computed new projection map";
        // newphi := phi*projmap;
        // defeqsnewphi := DefiningPolynomials(newphi);
        // invdefeqsnewphi := InverseDefiningPolynomials(newphi); This is only birational, so don't have inverse
        // return projecttoplane(newmodel, map<X->newmodel|defeqsnewphi,invdefeqsnewphi>, []);
    end if;
    defeqsnewphi := DefiningPolynomialsComposite(phi, projmap);
    return projecttoplane(newmodel, map<Can->newmodel|defeqsnewphi>, ratcusps);
end intrinsic;

intrinsic planemodel_highgenus(X::Sch, cusps::SeqEnum) -> Tup
{
    Input:
            X:          a canonically embedded curve X, as returned by ProcessModel()
            cusps:      rational cusps on X, as returned by ProcessModel()
    Output:
            result:     a tuple consisting of an equation defining a plane model C of X, and equations defining a map from X to C
}
    C, map_XtoC, gonalitybound := modelfromfuncfield_gonalitybound(X);
    if Dimension(AmbientSpace(Codomain(map_XtoC))) eq 2 then
        return projecttoplane(C,map_XtoC,[]);
    end if;

    map_XtoC := Restriction(map_XtoC,X,C);
    defeqs := DefiningEquations(map_XtoC);
    vprint User1: "Found defining equations of the map";
    if #cusps gt 0 and Type(cusps[1]) eq CspDat then
        cuspsnew := <c`coords : c in cusps>;
        cusps := cuspsnew;
    end if;
    vprint User1: Sprintf("Extracted coordinates of the %o cusps", #cusps);

    singular_ratcusps_on_C := {};
    nonsingular_ratcusps_on_C := {};
    for i := 1 to #cusps do
        c_coords := Eltseq(cusps[i]);
        c_imagecoords := [Evaluate(pol,c_coords) : pol in defeqs];
        boo := exists(a){coord : coord in c_imagecoords | coord ne 0};
        if not boo then continue i; end if;
        c_imageaffinecoords := [x/a : x in c_imagecoords];
        for x in c_imageaffinecoords do
            if not x in Rationals() then
                continue i;
            end if;
        end for;
        c := C ! c_imageaffinecoords;
        if IsSingular(C,c) then
            Include(~singular_ratcusps_on_C,c);
        else
            Include(~nonsingular_ratcusps_on_C,c);
        end if;
    end for;
    singular_ratcusps_on_C := SetToSequence(singular_ratcusps_on_C);
    nonsingular_ratcusps_on_C := SetToSequence(nonsingular_ratcusps_on_C);
    vprint User1: Sprintf("Projected rational cusps down from the canonical model. Found %o singular ones and %o nonsingular ones\nThey are:\n%o\n%o", #singular_ratcusps_on_C, #nonsingular_ratcusps_on_C, singular_ratcusps_on_C, nonsingular_ratcusps_on_C);

    for c in singular_ratcusps_on_C do
        newmodel, projmap := Projection(C,c);
        vprint User1: "Computed projection map";
        projmap := Restriction(projmap,C,newmodel);
        vprint User1: "Restricted projection map";
        phi := map_XtoC*projmap;
        defeqsphi := DefiningEquations(phi);
        if Dimension(AmbientSpace(newmodel)) eq 2 then
            P2<X,Y,Z> := AmbientSpace(newmodel);
            plane_eqn := DefiningEquation(newmodel);
            return <plane_eqn, defeqsphi>; // TODO done
        else
            rational_imageofcusps := {};
            for cc in cusps do
                c_coords := Eltseq(cc);
                c_imagecoords := [Evaluate(pol,c_coords) : pol in defeqsphi];
                boo := exists(a){coord : coord in c_imagecoords | coord ne 0};
                if not boo then continue cc; end if;
                c_imageaffinecoords := [x/a : x in c_imagecoords];
                for x in c_imageaffinecoords do
                    if not x in Rationals() then
                        continue cc;
                    end if;
                end for;
                ccimage := newmodel ! c_imageaffinecoords;
                Include(~rational_imageofcusps,ccimage);
                // TODO done
            end for;
            rational_imageofcusps := SetToSequence(rational_imageofcusps);
            vprint User1: Sprintf("There are %o rational cusps after 1 projection.\nThey are:\n%o\nUsing these to project further (if needed)", #rational_imageofcusps, rational_imageofcusps);
            return projecttoplane(newmodel,map<X->newmodel|defeqsphi>,rational_imageofcusps);
            // TODO done
        end if;
    end for;

    for c in nonsingular_ratcusps_on_C do
        try
            newmodel, projmap, out3blowup := ProjectionFromNonsingularPoint(C,c);
            projmap := Restriction(projmap,C,newmodel);
            phi := map_XtoC*projmap;
            if not ValidModel(phi) then continue; end if;
            defeqsphi := DefiningEquations(phi);
            if Dimension(AmbientSpace(newmodel)) eq 2 then
                P2<X,Y,Z> := AmbientSpace(newmodel);
                plane_eqn := DefiningEquation(newmodel);
                return <plane_eqn, defeqsphi>; // TODO done
            else
                rational_imageofcusps := {};
                for cc in cusps do
                    c_coords := Eltseq(cc);
                    c_imagecoords := [Evaluate(pol,c_coords) : pol in defeqsphi];
                    boo := exists(a){coord : coord in c_imagecoords | coord ne 0};
                    if not boo then continue cc; end if;
                    c_imageaffinecoords := [x/a : x in c_imagecoords];
                    for x in c_imageaffinecoords do
                        if not x in Rationals() then
                            continue cc;
                        end if;
                    end for;
                    ccimage := newmodel ! c_imageaffinecoords;
                    Include(~rational_imageofcusps,ccimage);
                    // TODO done
                end for;
                rational_imageofcusps := SetToSequence(rational_imageofcusps);
                return projecttoplane(newmodel,map<X->newmodel|defeqsphi>,rational_imageofcusps);
                // TODO done
            end if;
        catch e;
            continue c;
        end try;
    end for;
    return projecttoplane(C,map_XtoC,[]);
    // TODO done
end intrinsic;

intrinsic HighGenusPlaneModel(label::MonStgElt) -> SeqEnum
{
Input: label of a modular curve.
File input: LMFDBWriteCanonicalModel must have been called, stored in canonical_models/<label>
Output: a sequence of length 0 or 1 of known plane models (provided as a tuple, with first entry the defining polynomial and the second entry a sequence of three polynomials giving the map from the canonical model X to C).  May be a model read from plane_models/<label>.
File output: Writes a plane model to plane_models/<label>, if the model is better than the one already present

High genus is a bit of a misnomer: this works as long as g > 0 and the canonical model is not already a plane model.
}
    X, model_type, g, cusps := LMFDBReadCusps(label : rational_only:=true);
    rcusps := [c : c in cusps];
    C, bestkey := LMFDBReadPlaneModel(label);
    P := Universe(X);
    curve := Curve(Proj(P), X);
    if g gt 0 and Rank(P) gt 3 then
        t0 := ReportStart(label, "planemodel_highgenus");
        fproj := planemodel_highgenus(curve, rcusps);
        ReportEnd(label, "planemodel_highgenus", t0);
        C, bestkey := RecordPlaneModel(fproj, X, C, bestkey, label);
    end if;
    return C;
end intrinsic;

intrinsic PlaneModelAndGonalityBounds(label::MonStgElt) -> Tup, SeqEnum
{
    Input:
            label: the label of a modular curve
    File input:
            canonical_models/<label>: as written by LMFDBWriteCanonicalModel
            gonality/<label>: comma separated q_low, q_high, qbar_low, qbar_high, as read by LMFDBReadGonalityBounds
            plane_models/<label>: as written by LMFDBWritePlaneModel (optional)
    Output:
            bounds: a 4-tuple giving gonality bounds <q_low, q_high, qbar_low, qbar_high>
            C:     a sequence of length 0 or 1 of known plane models (provided as a tuple, with first entry the defining polynomial and the second entry a sequence of three polynomials giving the map from X to C)
    File output:
            Writes gonality bounds using LMFDBWriteGonalityBounds
            Writes plane model using LMFDBWritePlaneModel when there is an improvement
            If hyperelliptic, writes to ghyp_models/<label> instead
}
    X, g, model_type := LMFDBReadXGModel(label);
    ghyp := (model_type eq -1);
    q_low, q_high, qbar_low, qbar_high := Explode(LMFDBReadGonalityBounds(label));
    C, bestkey := LMFDBReadPlaneModel(label);
    curve := Curve(Proj(Universe(X)), X);
    if #X eq 1 then
        q_high := Min(q_high, planemodel_gonbound(X[1]));
    else
        q_high := Min(q_high, Degree(curve));
    end if;

    if g gt 1 and ghyp then
        qbar_high := 2;
        if g eq 2 then
            q_high := 2;
        else
            if q_high ge 4 then
                q_high := 4;
            else
                q_high := 2;
            end if;
        end if;
        // We write the gonalities now, since the following may time out
        LMFDBWriteGonalityBounds(<q_low, q_high, qbar_low, qbar_high>, label);
        t0 := ReportStart(label, "IsHyperelliptic");
        hyp, H, h_map := IsHyperelliptic(curve);
        ReportEnd(label, "IsHyperelliptic", t0);
        if hyp then
            q_high := 2;
            H, r_map := ReducedMinimalWeierstrassModel(H);
            h_map := h_map * r_map;
            Hdef := DefiningEquation(H);
            HP := Parent(Hdef);
            AssignNames(~HP, ["X","Y","Z"]);
            Write("ghyp_models/" * label, Sprintf("%o|%o", sprint(Hdef), Join([sprint(coord) : coord in DefiningEquations(h_map)], ",")) : Overwrite);
        else
            q_low := 4;
            q_high := 4;
            // Later, we'll use Edgar and Raymond's code to find model as double cover of conic
        end if;
    end if;
    if g gt 1 and not ghyp then
        // not geometrically hyperelliptic
        qbar_low := Max(qbar_low, 3);
        q_low := Max(q_low, 3);
        LMFDBWriteGonalityBounds(<q_low, q_high, qbar_low, qbar_high>, label);
    end if;
    if g ge 3 and g le 6 and not ghyp then
        try
            t0 := ReportStart(label, "gonality");
            if g eq 3 then
	        qbar_low, gonal_map := Genus3GonalMap(curve : IsCanonical:=true);
            elif g eq 4 then
	        qbar_low, gonal_map := Genus4GonalMap(curve : IsCanonical:=true);
            elif g eq 5 then
	        qbar_low, gonal_map := Genus5GonalMap(curve : IsCanonical:=true);
            else
	        qbar_low, sec_type, gonal_map, aux_map := Genus6GonalMap(curve : IsCanonical:=true);
            end if;
            ReportEnd(label, "gonality", t0);
            q_low := qbar_low;
            qbar_high := qbar_low;
            F := BaseField(Domain(gonal_map));
            if F eq Rationals() then
                // If gonal map is rational, get q_high as well
                q_high := qbar_low;
                // We write the gonalities now, since the following may time out
                LMFDBWriteGonalityBounds(<q_low, q_high, qbar_low, qbar_high>, label);
                t0 := ReportStart(label, "planemodel_gonalitybound");
                eqsplanemap, gonality := planemodel_gonalitybound(curve);
                ReportEnd(label, "planemodel_gonalitybound", t0);
                if q_high eq gonality then
                    C, bestkey := RecordPlaneModel(eqsplanemap, X, C, bestkey, label);
                else
                    t0 := ReportStart(label, "planemodel_fromgonalmap2");
                    eqsplanemap := planemodel_fromgonalmap2(gonal_map, label);
                    ReportEnd(label, "planemodel_fromgonalmap2", t0);
                    C, bestkey := RecordPlaneModel(eqsplanemap, X, C, bestkey, label);
                end if;
            end if;
        catch e
            print Sprint(e) * "\n";
        end try;
    end if;
    LMFDBWriteGonalityBounds(<q_low, q_high, qbar_low, qbar_high>, label);
    return <q_low, q_high, qbar_low, qbar_high>, C;
end intrinsic;

declare type JMapData;
declare attributes JMapData: E4,E6,J;

intrinsic Print(X::JMapData)
  {Print X}
  // Code: Print X with no new line, via printf
  printf "j-map data\n";
  if assigned X`J then
    printf "J %o:\n", X`J;
  end if;
  if (assigned X`E4) and (assigned X`E6) then
    printf "E4 %o:\n", X`E4;
    printf "E6 %o:\n", X`E6;
  end if;
end intrinsic;

intrinsic remove_whitespace(X::MonStgElt) -> MonStgElt
{ Strips spaces and carraige returns from string; much faster than StripWhiteSpace. }
    return Join(Split(Join(Split(X," "),""),"\n"),"");
end intrinsic;

intrinsic sprint(X::.) -> MonStgElt
{ Sprints object X with spaces and carraige returns stripped. }
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return remove_whitespace(Sprintf("%o",X));
end intrinsic;

intrinsic PySplit(s::MonStgElt, sep::MonStgElt : limit:=-1) -> SeqEnum[MonStgElt]
{Splits using Python semantics (different when #sep > 1, and different when sep at beginning or end)}
    if #sep eq 0 then
        error "Empty separator";
    end if;
    i := 1;
    j := 0;
    ans := [];
    while limit gt 0 or limit eq -1 do
        if limit ne -1 then limit -:= 1; end if;
        pos := Index(s, sep, i);
        if pos eq 0 then break; end if;
        j := pos - 1;
        Append(~ans, s[i..j]);
        i := j + #sep + 1;
    end while;
    Append(~ans, s[i..#s]);
    return ans;
end intrinsic;

intrinsic ReplaceLetter(s::MonStgElt, x::MonStgElt, subs::MonStgElt) -> MonStgElt
{}
    split := Split(s, x: IncludeEmpty := true);
    res := split[1];
    for j in [2..#split] do
	res := res cat subs cat split[j];
    end for;
    // Even IncludeEmpty does not add "" when s ends with x
    if s[#s] eq x then
	res cat:= subs;
    end if;
    return res;
end intrinsic;

function get_uvars(rank)
    uvars := Eltseq("XYZWTUVRSABCDEFGHIKLMNOPQJ");
    if (#uvars lt rank) then
        uvars := [Sprintf("X%o", i) : i in [1..rank]];
    end if;
    return uvars[1..rank];
end function;

function get_lvars(rank)
    lvars := Eltseq("xyzwtuvrsabcdefghiklmnopqj");
    if (#lvars lt rank) then
        lvars := [Sprintf("x%o", i) : i in [1..rank]];
    end if;
    return lvars[1..rank];
end function;

function ReplaceVariables(s, nvars : upper:=false)
    variables := upper select get_uvars(nvars) else get_lvars(nvars);
    for i in [1..nvars] do
	s := ReplaceLetter(s, variables[i], "P." cat Sprint(i));
    end for;
    return s;
end function;

intrinsic AssignCanonicalNames(~R::Rng : upper:=false)
{Assign names in a standard order; R should be either a multivariate polynomial ring or a function field}
    if Type(R) eq FldFun then
        rank := 1;
    else
        rank := Rank(R);
    end if;
    if upper then
        AssignNames(~R, get_uvars(rank));
    else
        AssignNames(~R, get_lvars(rank));
    end if;
end intrinsic;

intrinsic ReadPoly(P::RngMPol, f::MonStgElt : upper:=false) -> RngMPolElt
{}
    nvars := Rank(P);
    return eval(ReplaceVariables(f, nvars : upper:=upper));
    // Note that this might be a fraction field element if there was division
end intrinsic;

function get_cusp_str(cusps)
    // We only write rational points over low degree fields
    // Change here if you want to modify this!
    max_deg := 6;
    cusps_to_write := [c : c in cusps | Degree(c`field) le max_deg];
    coords := Join([sprint(c`coords) : c in cusps_to_write] , ",");
    Qx<x> := PolynomialRing(Rationals());
    fields := Join([sprint(Qx!DefiningPolynomial(c`field)) : c in cusps] , ","); // Need to keep all fields since the variable names are indexed by the original ordering
    return Sprintf("{%o}|{%o}", coords, fields);
end function;

intrinsic LMFDBWriteJMap(j::SeqEnum, cusps::SeqEnum[CspDat], codomain::MonStgElt, model_type::RngIntElt, label::MonStgElt)
{Write the j-map and cusps to a file; codomain is the label of the codomain (always canonical model) or empty (for absolute map)}
    // We clear denominators uniformly across j
    ZZ := Integers();
    nums := [];
    dens := [];
    degs := {};
    for coord in j do
        Include(~degs, Degree(coord));
        coeffs := Coefficients(coord);
        Append(~dens, LCM([Denominator(c) : c in coeffs]));
        Append(~nums, GCD([Numerator(c) : c in coeffs]));
    end for;
    scale := LCM(dens) / GCD(nums);
    for i in [1..#j] do
        j[i] := scale * j[i];
    end for;
    S := Universe(j);
    AssignCanonicalNames(~S);
    if #{Degree(coord) : coord in j} ne 1 then
        printf "Nonhomogeneous warning: %o", j;
    end if;
    System("mkdir -p jcusps");
    fname := Sprintf("jcusps/%o", label);
    if #codomain gt 0 then
        Write(fname, Sprintf("%o|%o|{%o}|%o", model_type, codomain, Join([sprint(jcoord) : jcoord in j], ","), get_cusp_str(cusps)));
    else
        assert #j eq 2;
        Write(fname, Sprintf("%o|{%o,%o}|%o", model_type, sprint(j[1]), sprint(j[2]), get_cusp_str(cusps)) : Overwrite);
    end if;
end intrinsic;

intrinsic LMFDBReadCusps(label::MonStgElt : rational_only:=false) -> SeqEnum, RngIntElt, RngIntElt, List
{Returns XG model, model_type, genus, and cusps}
    X, g, model_type := LMFDBReadXGModel(label);
    data := Split(Read(Sprintf("jcusps/%o", label)), "\n")[1];
    data := Split(data, "|");
    if #data eq 5 then
        mtype, codomain, j, cusps, fields := Explode(data);
        assert StringToInteger(mtype) eq model_type;
    elif #data eq 4 then
        codomain := "";
        mtype, j, cusps, fields := Explode(data);
        assert StringToInteger(mtype) eq model_type;
    else
        error "Invalid jcusp format";
    end if;
    if #cusps gt 2 then
        cusps := Split(cusps[2..#cusps-1], ",");
        QQ := Rationals();
        R<x> := PolynomialRing(QQ);
        fields := Split(fields[2..#fields-1], ",");
        by_i := AssociativeArray();
        for i in [0..#fields] do by_i[i] := []; end for;
        for cusp in cusps do
            if not ("a" in cusp) then
                Append(~by_i[0], cusp);
            elif not rational_only then
                first := Index(cusp, "_") + 1;
                last := first;
                while cusp[last+1] in "0123456789" do
                    last +:= 1;
                end while;
                i := StringToInteger(cusp[first..last]);
                Append(~by_i[i], cusp);
            end if;
        end for;
        cusps := [* [StringToRational(c) : c in Split(cusp[2..#cusp-1], ":")] : cusp in by_i[0] *];
        if not rational_only then
            for i in [1..#fields] do
                poly := eval fields[i];
                K := NumberField(poly);
                var := Sprintf("a_%o", i);
                AssignNames(~K, [var]);
                a := K.1;
                for cusp in by_i[i] do
                    subbed := Join(PySplit(cusp, var), "a");
                    subbed := [eval c : c in Split(subbed[2..#subbed-1], ":")];
                    Append(~cusps, subbed);
                end for;
            end for;
        end if;
    else
        cusps := [* *];
    end if;
    return X, model_type, g, cusps;
end intrinsic;

intrinsic LMFDBReadJMap(label::MonStgElt) -> SeqEnum, RngIntElt, MonStgElt, SeqEnum
{Returns XG model, model_type, label of codomain, and j-map}
    // We want to be able to read the j-map even in the case of P1, where the model is not stored
    if OpenTest(Sprintf("canonical_models/%o", label), "r") then
        X, g, model_type := LMFDBReadXGModel(label);
        P := Universe(X);
    else
        assert Split(label, ".")[3] eq "0";
        X := [];
        model_type := 1;
        P := PolynomialRing(RationalField(), 2);
    end if;
    nvars := Rank(P);
    data := Split(Read(Sprintf("jcusps/%o", label)), "|");
    if #data eq 5 then
        jtype, codomain, j, cusps, fields := Explode(data);
    else
        codomain := "";
        jtype, j, cusps, fields := Explode(data);
    end if;
    j := Split(j[2..#j-1], "," : IncludeEmpty:=true);
    j := [ReadPoly(P, jcoord) : jcoord in j];
    return X, model_type, codomain, j;
end intrinsic;

intrinsic LMFDBReadRelativeJCodomain(label::MonStgElt) -> BoolElt, RngIntElt, MonStgElt, SeqEnum
{
Input:
    label - the label of a modular curve
File input:
    cod/<label> - Written by the get_relj_codomains() function in the preparation scripts
Output:
    absolute - whether the j-map from this curve should be computed to X(1) or not
    max_index - the maximum relative index of any model mapping to this one, passed in to FindModelOfXG for the codomain of relative j-maps so that there is enough precision to find relations between lifted modular forms
    codomain - if absolute is false, the codomain for the relative j-map; otherwise the emptry string
    conjugator - if absolute is false, a sequence of 4 integers giving a matrix that conjugates this GL2-subgroup into the one for the codomain
}
    g := StringToInteger(Split(label, ".")[3]);
    if g lt 3 then
        return true, 1, "", _;
    end if;
    fname := Sprintf("cod/%o", label);
    if OpenTest(fname, "r") then
        codomain, data := Explode(Split(Read(fname), "|"));
        if codomain eq label then
            max_index := StringToInteger(data);
            return true, max_index, "", _;
        end if;
        conjugator := [StringToInteger(c) : c in Split(data, ",")];
        fname := Sprintf("cod/%o", codomain);
        _, max_index := Explode(Split(Read(fname), "|"));
        max_index := StringToInteger(max_index);
        return false, max_index, codomain, conjugator;
    else // hyperelliptic
        return true, 1, "", _;
    end if;
end intrinsic;

intrinsic LMFDBWriteXGModel(X::Crv, model_type::RngIntElt, label::MonStgElt)
{Write the model produced by FindModelOfXG}
    DP := DefiningPolynomials(X);
    // In genus 0, there are examples with denominators, which we want to clear
    for i in [1..#DP] do
        DP[i] := ClearDenominators(DP[i]);
        if LeadingCoefficient(DP[i]) lt 0 then
            DP[i] := -DP[i];
        end if;
    end for;
    R := Universe(DP);
    AssignCanonicalNames(~R);
    System("mkdir -p canonical_models");
    fname := Sprintf("canonical_models/%o", label);
    Write(fname, Sprintf("%o|{%o}|%o", Rank(R), Join([sprint(f) : f in DP], ","), model_type) : Overwrite);
    if model_type eq 5 then
        g := Split(label, ".")[3];
        // This should always be 1, but just in case
        if g eq "1" then
            E := EllipticCurve(X);
            cremona_label := CremonaReference(E);
            Write("curve_labels/" * label, cremona_label);
        end if;
    end if;
end intrinsic;

intrinsic LMFDBReadXGModel(label::MonStgElt) -> SeqEnum, RngIntElt, RngIntElt
{}
    g := StringToInteger(Split(label, ".")[3]);
    fname := Sprintf("canonical_models/%o", label);
    nvars, X, model_type := Explode(Split(Read(fname), "|"));
    nvars := StringToInteger(nvars);
    P := PolynomialRing(Rationals(), nvars);
    AssignCanonicalNames(~P);
    X := [ReadPoly(P, f) : f in Split(X[2..#X-1], ",")];
    return X, g, StringToInteger(model_type);
end intrinsic;

intrinsic LMFDBWritePlaneModel(f::RngMPolElt, proj::SeqEnum, alg::MonStgElt, label::MonStgElt)
{}
    assert #proj eq 3;
    System("mkdir -p plane_models");
    fname := Sprintf("plane_models/%o", label);
    if Type(proj[1]) eq FldFunRatMElt then
        proj := [Numerator(proj[1])*Denominator(proj[2])*Denominator(proj[3]), Numerator(proj[2])*Denominator(proj[3])*Denominator(proj[1]), Numerator(proj[3])*Denominator(proj[1])*Denominator(proj[2])];
    end if;
    S := Parent(f);
    AssignCanonicalNames(~S);
    R := Universe(proj);
    nvars := Rank(R);
    g := StringToInteger(Split(label, ".")[3]);
    // Some of the plane model functions use x[1], x[2], etc in the function field
    // We need to replace these with X,Y,Z,W,...
    AssignCanonicalNames(~R);
    // Determine whether the model is smooth
    // Definitely not if g not triangular g = n(n+1)/2 ==> n^2 + n - 2g = 0 ==> 1 + 8g square
    if IsSquare(8*g + 1) then
        // Need to construct the curve and check if singular
        C := Curve(Proj(Parent(f)), f);
        smooth := IsNonsingular(C) select "t" else "f";
    else
        smooth := "f";
    end if;
    Write(fname, Sprintf("%o|%o|%o|%o|%o", sprint(f), Join([sprint(c) : c in proj], ","), nvars, smooth, alg) : Overwrite);
end intrinsic;

intrinsic LMFDBReadPlaneModel(label::MonStgElt) -> SeqEnum, Tup
{}
    fname := Sprintf("plane_models/%o", label);
    if OpenTest(fname, "r") then
        f, proj, g, smooth := Explode(Split(Read(fname), "|"));
        g := StringToInteger(g);
        P3 := PolynomialRing(Rationals(), 3);
        AssignCanonicalNames(~P3);
        f := ReadPoly(P3, f);
        Pg := PolynomialRing(Rationals(), g);
        AssignCanonicalNames(~Pg);
        proj := [ReadPoly(Pg, h) : h in Split(proj, ",")];
        return [<f, proj>], planemodel_sortkey(f);
    else
        return [], <>;
    end if;
end intrinsic;

intrinsic LMFDBWriteHyperellipticModel(H::Any, h_map::SeqEnum, label::MonStgElt)
{H can be either a hyperelliptic curve or a sequence of polynomials defining a double cover of a conic}
    if Type(H) eq CrvHyp then
        Hdef := DefiningEquations(H);
    else
        Hdef := H;
    end if;
    HP := Universe(Hdef);
    AssignCanonicalNames(~HP);
    s := "{" * Join([sprint(heq) : heq in Hdef], ",") * "}";
    if #h_map ne 0 then
        n := Rank(Universe(h_map));
        s := Sprintf("%o|{%o}|%o", s, "|" * Join([sprint(coord) : coord in h_map], ","), n);
    end if;
    Write("ghyp_models/" * label, Sprintf("%o|%o", sprint(Hdef), Join([sprint(coord) : coord in DefiningEquations(h_map)], ",")) : Overwrite);
    if Type(H) eq CrvHyp and Split(label, ".")[3] eq "2" then
        // Try to recognize the model in the LMFDB database
        g2invs := G2Invariants(H);
        fname := "g2invs/h" * Join([Sprintf("%o_%o", Numerator(c), Denominator(c)) : c in g2invs], ".");
        if OpenTest(fname, "r") then
            R := PolynomialRing(Rationals());
            for poss in Split(Read(fname), "\n") do
                lmfdb_label, HH := Explode(Split(poss, "|"));
                HH := eval HH;
                HH := HyperellipticCurve([R!h : h in HH]);
                if IsIsomorphic(H, HH) then
                    Write("curve_labels/" * label, lmfdb_label);
                    break;
                end if;
            end for;
        end if;
    end if;
end intrinsic;

intrinsic LMFDBReadHyperellipticModel(label::MonStgElt) -> SeqEnum, SeqEnum
{}
    fname := "ghyp_models/" * label;
    if OpenTest(fname, "r") then
        s := Split(Read(fname), "\n")[1];
        if "|" in s then
            R3 := PolynomialRing(Rationals(), 3);
            AssignCanonicalNames(~R3);
            eqs, mp, n := Explode(Split(s, "|"));
            n := StringToInteger(n);
            Rn := PolynomialRing(Rationals(), n);
            AssignCanonicalNames(~Rn);
            eqs := [ReadPoly(R3, f) : f in Split(eqs[2..#eqs-1], ",")];
            mp := [ReadPoly(Rn, f) : f in Split(mp[2..#mp-1], ",")];
            return eqs, mp;
        end if;
        R4 := PolynomialRing(Rationals(), 4);
        AssignCanonicalNames(~R4);
        return [ReadPoly(R4, f) : f in Split(s, ",")];
    end if;
    return [], [];
end intrinsic;

intrinsic LMFDBWriteGonalityBounds(gon_bounds::Tup, label::MonStgElt)
{}
    fname := Sprintf("gonality/%o", label);
    if gon_bounds[1] gt gon_bounds[2] or gon_bounds[3] gt gon_bounds[4] or gon_bounds[4] gt gon_bounds[2] or gon_bounds[3] gt gon_bounds[1] then
        // Annoyingly, user errors don't give tracebacks, so we get one
        try
            x := 1/(1-1);
        catch e
            if assigned e`Traceback then
                print e`Traceback;
            end if;
        end try;
        error Sprintf("Invalid gonality bounds %o", sprint(gon_bounds));
    end if;
    Write(fname, Join([Sprint(c) : c in gon_bounds], ",") : Overwrite);
end intrinsic;

intrinsic LMFDBReadGonalityBounds(label::MonStgElt) -> Tup
{}
    fname := Sprintf("gonality/%o", label);
    return <StringToInteger(c) : c in Split(Read(fname), ",")>;
end intrinsic;

intrinsic LMFDBReadJinvPts(label::MonStgElt) -> List
{}
    fname := Sprintf("jinvs/%o", label);
    if OpenTest(fname, "r") then
        R := PolynomialRing(Rationals());
        lines := Split(Read(fname), "\n");
        jinvs := [* *];
        KD := AssociativeArray();
        KD[R![0,1]] := Rationals();
        for line in lines do
            j, coeffs, isolated := Explode(Split(line, "|"));
            f := R![StringToInteger(c) : c in Split(coeffs, ",")];
            if IsDefined(KD, f) then
                K := KD[f];
            else
                K := NumberField(f);
                KD[f] := K;
            end if;
            // The j-invariant might be a rational number in which case there are no commas
            if "," in j then
                j := K![StringToRational(c) : c in Split(j, ",")];
            else
                j := K!StringToRational(j);
            end if;
            isolated := StringToInteger(isolated);
            Append(~jinvs, <j, isolated>);
        end for;
        return jinvs;
    else
        return [* *];
    end if;
end intrinsic;

intrinsic LMFDBWriteJinvCoords(coords::List, label::MonStgElt)
{}
    fname := Sprintf("rats/%o", label);
    coord_strs := [];
    for trip in coords do
        model_type, j, coord := Explode(trip);
        coord := Eltseq(coord);
        j := Join([Sprint(a) : a in Eltseq(j)], ",");
        poly := DefiningPolynomial(Universe(Eltseq(coord)));
        R := Parent(poly);
        AssignNames(~R, ["x"]);
        poly := sprint(poly);
        coord := Join([Join([Sprint(a) : a in Eltseq(c)], ",") : c in coord], ":");
        Append(~coord_strs, Sprintf("%o|%o|%o|%o", poly, j, model_type, coord));
    end for;
    Write(fname, Join(coord_strs, "\n") : Overwrite);
end intrinsic;

intrinsic LMFDBReadJinvCoords(label::MonStgElt : can_only:=false) -> Assoc
{}
    fname := Sprintf("rats/%o", label);
    lines := Split(Read(fname), "\n");
    coords := AssociativeArray();
    R<x> := PolynomialRing(Rationals());
    for line in line do
        poly, j, model_type, coord := Explode(Split(line, "|"));
        model_type := StringToInteger(model_type);
        if can_only and model_type ne 0 then continue; end if;
        poly := eval(poly);
        if poly eq x-1 then
            K := RationalsAsNumberField();
        else
            K := NumberField(poly);
        end if;
        j := K![StringToRational(c) : c in Split(j, ",")];
        coord := [K![StringToRational(c) : c in Split(z, ",")] : z in Split(coord, ":")];
        if not IsDefined(coords, K) then
            coords[K] := [];
        end if;
        Append(~coords[K], <j, coord>);
    end for;
    return coords;
end intrinsic;

intrinsic LMFDBWriteCuspCoords(coords::List, label::MonStgElt)
{}
    fname := Sprintf("cusps/%o", label);
    coord_strs := [];
    for trip in coords do
        model_type, coord := Explode(trip);
        poly := DefiningPolynomial(Universe(Eltseq(coord)));
        R := Parent(poly);
        AssignNames(~R, ["x"]);
        coord := Join([Join([Sprint(a) : a in Eltseq(c)], ",") : c in Coordinates(coord)], ":");
        Append(~coord_strs, Sprintf("%o|%o|%o", sprint(poly), model_type, coord));
    end for;
    Write(fname, Join(coord_strs, "\n") : Overwrite);
end intrinsic;

function StringToPoly(s, R, name)
    i := 0;
    while (i lt #s) do
       i +:= 1;
       idx := Index(Names(R), s[i]);
       if idx gt 0 then
	   s := s[1..i-1] cat Sprintf("%o[%o]", name, idx) cat s[i+1..#s];
       end if;
   end while;
   return s;
end function;

intrinsic LMFDBReadModel(fname::MonStgElt) ->
	    Crv, JMapData
{Read the model, and JMapData from a file for input into the LMFDB database}
  input := Read(fname);
  input_lines := Split(input, "\n");
  r := input_lines[1];
  split_r := Split(r, "|");
  data := [Split(t[2..#t-1], ",") : t in split_r];
  rank := eval(data[1][1]);
  // no longer needed since we don't write the q-expansions
  /*
  cyc_ord := eval data[4][1];
  K := CyclotomicField(cyc_ord);
  if Type(K) ne FldRat then
      AssignNames(~K, ["zeta"]);
      zeta := K.1;
  end if;
 */
  uvars := Eltseq("XYZWTUVRSABCDEFGHIKLMNOPQJ");
  lvars := Eltseq("xyzwtuvrsabcdefghiklmnopqj");
  P<[x]> := ProjectiveSpace(Rationals(), rank-1);
  R := CoordinateRing(P);
  AssignNames(~R, uvars[1..rank]);
  polys := [R | eval StringToPoly(s, R, "x") : s in data[2]];
  C := Curve(P, polys);
  /*
  Kq<q> := PowerSeriesRing(K);
  qexps := [[eval f : f in Split(fs, ";")] : fs in data[2]];
 */
  S<[X]> := FieldOfFractions(PolynomialRing(Rationals(), rank));
  AssignNames(~S, lvars[1..rank]);
  rats_J := [eval StringToPoly(s, S, "X") : s in data[3]];
  j := New(JMapData);
  if (#rats_J ge 2) then
      j`E4 := rats_J[1];
      j`E6 := rats_J[2];
      j`J := rats_J[3];
  else
      j`J := rats_J[1];
  end if;
  return C, j;
end intrinsic;

intrinsic ReportStart(label::MonStgElt, job::MonStgElt) -> FldReElt
{}
    msg := "Starting " * job;
    PrintFile("timings/" * label, msg);
    vprint User1: msg;
    return Cputime();
end intrinsic;

intrinsic ReportEnd(label::MonStgElt, job::MonStgElt, t0::FldReElt : elapsed:=0)
{}
    if elapsed eq 0 then
        elapsed := Cputime() - t0;
    end if;
    msg := Sprintf("Finished %o in %o", job, elapsed);
    PrintFile("timings/" * label, msg);
    vprint User1: msg;
end intrinsic;

// Utility dictionary function

intrinsic Get(A::Assoc, k::Any, v::Any) -> Any
{}
    if IsDefined(A, k) then
        return A[k];
    end if;
    return v;
end intrinsic;

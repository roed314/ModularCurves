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
    uvars := Eltseq("XYZWTUVRSABCDEFGHIJKLMNOPQ");
    if (#uvars lt rank) then
        uvars := [Sprintf("X%o", i) : i in [1..rank]];
    end if;
    return uvars[1..rank];
end function;

function get_lvars(rank)
    lvars := Eltseq("xyzwtuvrsabcdefghijklmnopq");
    if (#lvars lt rank) then
        lvars := [Sprintf("x%o", i) : i in [1..rank]];
    end if;
    return lvars[1..rank];
end function;

function ReplaceVariables(s, nvars : upper:=true)
    variables := upper select get_uvars(nvars) else get_lvars(nvars);
    for i in [1..nvars] do
	s := ReplaceLetter(s, variables[i], "P." cat Sprint(i));
    end for;
    return s;
end function;

intrinsic AssignCanonicalNames(~R::Rng : upper:=true)
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

intrinsic ReadPoly(P::RngMPol, f::MonStgElt, nvars::RngIntElt : upper:=true, Homogenize:=false) -> RngMPolElt
{}
    g := eval(ReplaceVariables(f, nvars : upper:=upper));
    // Note that g might be a fraction field element if there was division
    if Homogenize then
        d := Max(Degree(Numerator(g)), Degree(Denominator(g)));
        g := Homogenization(Numerator(g), P.nvars, d) / Homogenization(Denominator(g), P.nvars, d);
    end if;
    return g;
end intrinsic;

intrinsic LMFDBWriteModel(X::Crv, j::JMapData, cusps::SeqEnum[CspDat],
                          model_type::RngIntElt, label::MonStgElt)
{Write the model and j-map to a file for input into the LMFDB}
    DP := DefiningPolynomials(X);
    R := Universe(DP);
    AssignCanonicalNames(~R);
    S := (assigned j`J) select Parent(j`J) else Parent(j`E4);
    AssignCanonicalNames(~S);
    E4_str := (assigned j`E4) select sprint(j`E4) else "";
    E6_str := (assigned j`E6) select sprint(j`E6) else "";
    j_str := (assigned j`J) select sprint(j`J) else "";
    // We only write rational points over low degree fields
    // Change here if you want to modify this!
    max_deg := 6;
    cusps_to_write := [c : c in cusps | Degree(c`field) le max_deg];
    coords := Join([sprint(c`coords) : c in cusps_to_write] , ",");
    Qx<x> := PolynomialRing(Rationals());
    fields := Join([sprint(Qx!DefiningPolynomial(c`field)) : c in cusps] , ","); // Need to keep all fields since the variable names are indexed by the original ordering
    System("mkdir -p canonical_models");
    fname := Sprintf("canonical_models/%o", label);
    Write(fname, Sprintf("%o|{%o}|{%o,%o,%o}|{%o}|{%o}|%o", Rank(R),
			 Join([sprint(f) : f in DP], ","), E4_str, E6_str, j_str,
			 coords,fields,model_type) : Overwrite);
end intrinsic;

intrinsic LMFDBReadCanonicalModel(label::MonStgElt) -> SeqEnum, RngIntElt, RngIntElt, SeqEnum, List
{}
    g := StringToInteger(Split(label, ".")[3]);
    fname := Sprintf("canonical_models/%o", label);
    nvars, X, E4E6j, cusps, fields, model_type := Explode(Split(Read(fname), "|"));
    E4, E6, j := Explode(Split(E4E6j[2..#E4E6j-1], "," : IncludeEmpty:=true));
    nvars := StringToInteger(nvars);
    P := PolynomialRing(Rationals(), nvars);
    AssignCanonicalNames(~P);
    X := [ReadPoly(P, f, nvars) : f in Split(X[2..#X-1], ",")];
    j := ReadPoly(P, j, nvars : Homogenize:=true); // note that ReadPoly can also deal with rational functions
    jnum := Numerator(j);
    jden := Denominator(j);
    model_type := StringToInteger(model_type);
    if #cusps gt 2 then // "{}"
        cusps := Split(cusps[2..#cusps-1], ",");
        QQ := Rationals();
        R<x> := PolynomialRing(QQ);
        fields := Split(fields[2..#fields-1], ",");
        by_i := AssociativeArray();
        for i in [0..#fields] do by_i[i] := []; end for;
        for cusp in cusps do
            if not ("a" in cusp) then
                Append(~by_i[0], cusp);
            else
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
    else
        cusps := [* *];
    end if;
    return X, g, model_type, jnum, jden, cusps;
end intrinsic;

intrinsic LMFDBWritePlaneModel(C::Any, proj::SeqEnum, label::MonStgElt)
{}
    System("mkdir -p plane_models");
    fname := Sprintf("plane_models/%o", label);
    if Type(proj[1]) eq RngMPolElt then
        R := Universe(proj);
        g := Rank(R);
        // Some of the plane model functions use x[1], x[2], etc in the function field
        // We need to replace these with X,Y,Z,W,...
        AssignCanonicalNames(~R);
    else
        g := #proj div 3;
        R := PolynomialRing(Rationals(), g);
        AssignCanonicalNames(~R);
        proj := [&+[proj[g*i + j] * R.j : j in [1..g]] : i in [0..2]];
    end if;
    if Type(C) ne RngMPolElt then
        C := DefiningEquation(C);
    end if;
    Write(fname, Sprintf("%o|%o|%o", C, Join([sprint(c) : c in proj], ","), g) : Overwrite);
end intrinsic;

intrinsic LMFDBReadPlaneModel(label::MonStgElt) -> SeqEnum
{}
    fname := Sprintf("plane_models/%o", label);
    if OpenTest(fname, "r") then
        f, proj, g := Explode(Split(Read(fname), "|"));
        g := StringToInteger(g);
        P3 := PolynomialRing(Rationals(), 3);
        AssignCanonicalNames(~P3);
        f := ReadPoly(P3, f, 3);
        Pg := PolynomialRing(Rationals(), g);
        AssignCanonicalNames(~Pg);
        proj := [ReadPoly(Pg, h, g) : h in Split(proj, ",")];
        return [<f, proj>];
    else
        return [];
    end if;
end intrinsic;

intrinsic LMFDBWriteGonalityBounds(gon_bounds::Tup, label::MonStgElt)
{}
    fname := Sprintf("gonality/%o", label);
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
        for line in lines do
            j, coeffs, isolated := Explode(Split(line, "|"));
            if coeffs eq "0,1" then
                K := Rationals();
            else
                K := NumberField(R![StringToInteger(c) : c in Split(coeffs, ",")]);
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
        if Type(j) ne MonStgElt then // not a cusp
            j := Join([Sprint(a) : a in Eltseq(j)], ",");
        end if;
        K := Sprint(DefiningPolynomial(Universe(Eltseq(coord))));
        coord := Join([Join([Sprint(a) : a in Eltseq(c)], ",") : c in Coordinates(coord)], ":");
        Append(~coord_strs, Sprintf("%o|%o|%o|%o", K, j, model_type, coord));
    end for;
    Write(fname, Join(coord_strs, "\n") * "\n" : Overwrite);
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
  uvars := Eltseq("XYZWTUVRSABCDEFGHIJKLMNOPQ");
  lvars := Eltseq("xyzwtuvrsabcdefghijklmnopq");
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

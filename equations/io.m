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

intrinsic AssignCanonicalNames(~R::Rng : upper:=true)
{Assign names in a standard order; R should be either a multivariate polynomial ring or a function field}
    uvars := Eltseq("XYZWTUVRSABCDEFGHIJKLMNOPQ");
    lvars := Eltseq("xyzwtuvrsabcdefghijklmnopq");
    if Type(R) eq FldFun then
        rank := 1;
    else
        rank := Rank(R);
    end if;
    if (#uvars lt rank) then
        uvars := [Sprintf("X%o", i) : i in [1..rank]];
        lvars := [Sprintf("x%o", i) : i in [1..rank]];
    end if;
    if upper then
        AssignNames(~R, uvars[1..rank]);
    else
        AssignNames(~R, lvars[1..rank]);
    end if;
end intrinsic;

intrinsic LMFDBWriteModel(X::Crv, j::JMapData,
		          cusps::SeqEnum[CspDat], fname::MonStgElt)
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
    max_deg := 4;
    cusps_to_write := [c : c in cusps | Degree(c`field) le max_deg];
    coords := Join([sprint(c`coords) : c in cusps_to_write] , ",");
    Qx<x> := PolynomialRing(Rationals());
    fields := Join([sprint(Qx!DefiningPolynomial(c`field)) : c in cusps] , ",");
    Write(fname, Sprintf("{%o}|{%o}|{%o,%o,%o}|{%o}|{%o}", Rank(R), 
			 Join([sprint(f) : f in DP], ","), E4_str, E6_str, j_str,
			 coords,fields) : Overwrite);
    return;
end intrinsic;

intrinsic LMFDBWritePlaneModel(C::Crv, proj::SeqEnum, fname::MonStgElt)
{}
    g := #proj div 3;
    R := PolynomialRing(Rationals(), g);
    AssignCanonicalNames(~R);
    coords := [&+[proj[g*i + j] * R.j : j in [1..g]] : i in [0..2]];
    Write(fname, Sprintf("%o|%o", DefiningEquation(C), Join([sprint(c) : c in coords], ",")) : Overwrite);
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

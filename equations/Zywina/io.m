declare type JMapData;
declare attributes JMapData: E4,E6,J;

function strip(X)
    // Strips spaces and carraige returns from string; much faster than StripWhiteSpace.
    return Join(Split(Join(Split(X," "),""),"\n"),"");
end function;

function sprint(X)
    // Sprints object X with spaces and carraige returns stripped.
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return strip(Sprintf("%o",X));
end function;

intrinsic LMFDBWriteModel(X::Rec, j::JMapData, fname::MonStgElt)
{Write the model, the q-expansions, and j-map to a file for input into the LMFDB database}
    Kq<q> := Parent(X`F0[1][1]);
    K := BaseRing(Kq);
    if Type(K) ne FldRat then
        AssignNames(~K, ["zeta"]);
	cyc_ord := CyclotomicOrder(K);
    else
	cyc_ord := 1;
    end if;
    // Need to figure out what to do about q-expansions
    uvars := Eltseq("XYZWTUVRSABCDEFGHIJKLMNOPQ");
    lvars := Eltseq("xyzwtuvrsabcdefghijklmnopq");
    DP := X`psi;
    R := Universe(DP);
    if (#uvars lt Rank(R)) then
	uvars := [Sprintf("X%o", i) : i in [1..Rank(R)]];
	lvars := [Sprintf("x%o", i) : i in [1..Rank(R)]];
    end if;
    AssignNames(~R, uvars[1..Rank(R)]);
    S := (assigned j`J) select Parent(j`J) else Parent(j`E4);
    AssignNames(~S, lvars[1..Rank(R)]);
    E4_str := (assigned j`E4) select sprint(j`E4) else "";
    E6_str := (assigned j`E6) select sprint(j`E6) else "";
    j_str := (assigned j`J) select sprint(j`J) else "";
    Write(fname, Sprintf("{%o}|{%o}|{%o,%o,%o}|{%o}", Join([sprint(f) : f in DP], ","), Join([Join([sprint(f) : f in fs],";") : fs in X`F0], ","), E4_str, E6_str, j_str, cyc_ord));
    return;
end intrinsic;

intrinsic LMFDBWriteModel(X::CrvCon, j::JMapData, fname::MonStgElt)
{Write the model and j-map to a file for input into the LMFDB}
    uvars := Eltseq("XYZWTUVRSABCDEFGHIJKLMNOPQ");
    lvars := Eltseq("xyzwtuvrsabcdefghijklmnopq");
    DP := DefiningPolynomials(X);
    R := Universe(DP);
    if (#uvars lt Rank(R)) then
	uvars := [Sprintf("X%o", i) : i in [1..Rank(R)]];
	lvars := [Sprintf("x%o", i) : i in [1..Rank(R)]];
    end if;
    AssignNames(~R, uvars[1..Rank(R)]);
    S := (assigned j`J) select Parent(j`J) else Parent(j`E4);
    AssignNames(~S, lvars[1..Rank(S)]);
    E4_str := (assigned j`E4) select sprint(j`E4) else "";
    E6_str := (assigned j`E6) select sprint(j`E6) else "";
    j_str := (assigned j`J) select sprint(j`J) else "";
    Write(fname, Sprintf("{%o}|{%o,%o,%o}", Join([sprint(f) : f in DP], ","), E4_str, E6_str, j_str));
    return;
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
	    Crv, SeqEnum[RngSerPowElt], JMapData, RngIntElt
{Read the model, the q-expansions, and JMapData from a file for input into the LMFDB database}
  input := Read(fname);
  input_lines := Split(input, "\n");
  r := input_lines[1];
  split_r := Split(r, "|");
  data := [Split(t[2..#t-1], ",") : t in split_r];
  rank := #data[2];
  cyc_ord := eval data[4][1];
  K := CyclotomicField(cyc_ord);
  if Type(K) ne FldRat then
      AssignNames(~K, ["zeta"]);
      zeta := K.1;
  end if;
  uvars := Eltseq("XYZWTUVRSABCDEFGHIJKLMNOPQ");
  lvars := Eltseq("xyzwtuvrsabcdefghijklmnopq");
  P<[x]> := ProjectiveSpace(Rationals(), rank-1);
  R := CoordinateRing(P);
  AssignNames(~R, uvars[1..rank]);
  polys := [R | eval StringToPoly(s, R, "x") : s in data[1]];
  C := Curve(P, polys);
  Kq<q> := PowerSeriesRing(K);
  qexps := [[eval f : f in Split(fs, ";")] : fs in data[2]];
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
  return C, qexps, j, cyc_ord;
end intrinsic;

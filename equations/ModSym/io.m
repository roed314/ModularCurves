
intrinsic WriteModel(X::Crv, fs::SeqEnum[RngSerPowElt],
		     E4::FldFunRatMElt, E6::FldFunRatMElt, name::MonStgElt)
{Write the model, the q-expansions, E4, E6 and j to a file, which can be loaded in magma,
    which is named name.m. They will be named X_name, fs_name, E4_name, etc.}

    preamble := Sprintf("
    /****************************************************
    Loading this file in magma loads the objects fs_%o,
    X_%o, E4_%o, E6_%o, j_%o. fs_%o is a list of power series which form 
    a basis for the space of cusp forms. X_%o is a 
    representation of the corresponding modular curve in 
    projective space, using the canonical embedding.
    E4_%o, E6_%o and j_%o are rational functions representing 
    E4, E6 and j in terms of the coordinates.
    *****************************************************/
    ",name, name, name, name, name,
		     name, name, name, name, name);

    fname := name cat ".m";
    Kq<q> := Parent(fs[1]);
    K := BaseRing(Kq);
    if Type(K) ne FldRat then
	AssignNames(~K, ["zeta"]);
    end if;
    zeta := K.1;
    poly<x> := DefiningPolynomial(K);
    // This should always be the rational field, but just in case
    F := BaseRing(K);
    suf := "";
    Proj<[x]> := AmbientSpace(X);
    if Type(K) ne FldRat then
	field_def_str := Sprintf("f<x> := Polynomial(F, %m);
	      K<zeta%o> := ext<F|f>;", Eltseq(poly), suf);
    else
	field_def_str := "K := F;";
    end if;
    write_str := Sprintf("
    	      F := %m;	
	      %o
	      Kq<q> := PowerSeriesRing(K);
	      fs_%o := [Kq | %m", F, field_def_str, name, fs[1]);
    if #fs gt 1 then
      write_str cat:= &cat[Sprintf(", %m", f) : f in fs[2..#fs]];
    end if;
    write_str cat:= "] ;";

    wts := Gradings(X)[1];
    is_weighted := Set(wts) ne {1};
    if is_weighted then
	proj_string := Sprintf("P_Q<[x]> := WeightedProjectiveSpace(Rationals(), %o);", wts);
    else
	proj_string := Sprintf("P_Q<[x]> := ProjectiveSpace(Rationals(), %o);", Dimension(Proj));
    end if;

    write_str cat:= Sprintf("
    	      %o
    	      X_%o := Curve(P_Q, %m);",
			    proj_string, name, DefiningPolynomials(X));

    write_str cat:= Sprintf("\nE4_num_%o := %m;\n", name, Numerator(E4));
    write_str cat:= Sprintf("E4_denom_%o := %m;\n", name, Denominator(E4));
    write_str cat:= Sprintf("E6_num_%o := %m;\n", name, Numerator(E6));
    write_str cat:= Sprintf("E6_denom_%o := %m;\n", name, Denominator(E6));
    write_str cat:= Sprintf("E4_%o := E4_num_%o / E4_denom_%o;\n", name, name, name);   
    write_str cat:= Sprintf("E6_%o := E6_num_%o / E6_denom_%o;\n", name, name, name); 
    write_str cat:= Sprintf("j_num_%o := 1728*E4_%o^3;\n", name, name);     
    write_str cat:= Sprintf("j_denom_%o := E4_%o^3-E6_%o^2;\n", name, name, name);
    write_str cat:= Sprintf("j_%o := j_num_%o / j_denom_%o;\n", name, name, name);
    fname := name cat ".m";
    Write(fname, write_str);
    return;
end intrinsic;

function strip(X)
    // Strips spaces and carraige returns from string; much faster than StripWhiteSpace.
    return Join(Split(Join(Split(X," "),""),"\n"),"");
end function;

function sprint(X)
    // Sprints object X with spaces and carraige returns stripped.
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return strip(Sprintf("%o",X));
end function;

intrinsic LMFDBWriteModel(X::Crv, fs::SeqEnum[RngSerPowElt],
		          E4::FldFunRatMElt, E6::FldFunRatMElt, fname::MonStgElt)
{Write the model, the q-expansions, E4, and E6 to a file for input into the LMFDB database}
    Kq<q> := Parent(fs[1]);
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
    DP := DefiningPolynomials(X);
    R := Parent(DP[1]);
    AssignNames(~R, uvars[1..Rank(R)]);
    S := Parent(E4);
    AssignNames(~S, lvars[1..Rank(R)]);
    weights := Gradings(X)[1];
    Write(fname, Sprintf("{%o}|{%o}|{%o,%o}|{%o}|{%o}", Join([sprint(f) : f in DefiningPolynomials(X)], ","), Join([sprint(f) : f in fs], ","), sprint(E4), sprint(E6), cyc_ord, Join([Sprintf("%o", w) : w in weights], ",")));
    return;
end intrinsic;

intrinsic LMFDBWriteModel(X::Crv, fs::SeqEnum[RngSerPowElt],
		          E4::RngMPolElt, E6::RngMPolElt, fname::MonStgElt)
{Write the model, the q-expansions, E4, and E6 to a file for input into the LMFDB database}
  FF := FieldOfFractions(Parent(E4));
  LMFDBWriteModel(X, fs, FF!E4, FF!E6, fname);
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
	    Crv, SeqEnum[RngSerPowElt], FldFunRatMElt, FldFunRatMElt
{Read the model, the q-expansions, E4, and E6 from a file for input into the LMFDB database}
  r := ReadLines(fname)[1];
  split_r := Split(r, "|");
  data := [Split(t[2..#t-1], ",") : t in split_r];
  rank := #data[2];
  cyc_ord := eval data[4][1];
  weights := [eval w : w in data[5]];
  assert rank eq #weights;
  K := CyclotomicField(cyc_ord);
  if Type(K) ne FldRat then
      AssignNames(~K, ["zeta"]);
      zeta := K.1;
  end if;
  uvars := Eltseq("XYZWTUVRSABCDEFGHIJKLMNOPQ");
  lvars := Eltseq("xyzwtuvrsabcdefghijklmnopq");
  if #Set(weights) eq 1 then
      R<[x]> := PolynomialRing(Rationals(), weights);
  else
      R<[x]> := PolynomialRing(Rationals(), rank);
  end if;
  AssignNames(~R, uvars[1..rank]);
  polys := [R | eval StringToPoly(s, R, "x") : s in data[1]];
  C := Curve(ProjectiveSpace(R), polys);
  Kq<q> := PowerSeriesRing(K);
  qexps := [eval f : f in data[2]];
  S<[X]> := FieldOfFractions(PolynomialRing(Rationals(), rank));
  AssignNames(~S, lvars[1..rank]);
  rats := [eval StringToPoly(s, S, "X") : s in data[3]];
  E4 := rats[1];
  E6 := rats[2];
  return C, qexps, E4, E6;
end intrinsic;

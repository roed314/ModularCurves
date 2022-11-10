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

import "OpenImage/main/ModularCurves.m" : FindModularForms, FindCuspForms;
intrinsic PlaneModelFromQExpansions(rec::Rec,prec::RngIntElt) -> Any
  {}

  if not assigned rec`F then
    rec := FindModularForms(2,rec,prec);
  end if;
  if not assigned rec`F0 then
    rec := FindCuspForms(rec);
  end if;

  found_bool := false;
  m := 5;
  while not found_bool do
    printf "trying m = %o\n", m;
    rels := FindRelations(fs[1..3],m);
    if #rels gt 0 then
      print "relation found!";
      found_bool := true;
    end if;
    m +:= 1;
  end while;

  f := rels[1];
  C := Curve(Proj(Parent(f)), f);
  assert Genus(C) eq rec`genus;
  return C;
end intrinsic;

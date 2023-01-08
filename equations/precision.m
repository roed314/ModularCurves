intrinsic RequiredPrecision(M::Rec, label::MonStgElt) -> RngIntElt, BoolElt, RngIntElt
{
Input:
    M - a modular curve record
Output:
    prec - the precision required to get a model from the OpenImage package
    hyp - whether the modular curve is hyperelliptic
    relation_degree - the maximum degree of an equation in the resulting model (only valid for canonical models, which is the case that's needed for relative j-maps)
}
  // We may have stored the result in ishyp/<label>
  if OpenTest("ishyp/" * label, "r") then
      s := Split(Read("ishyp/" * label), "\n")[1];
      hyp, prec, relation_degree := Explode(Split(s, "|"));
      return StringToInteger(prec), (hyp eq "t"), StringToInteger(relation_degree);
  end if;
  prec := Integers()!(M`N * Maximum([1/M`widths[i] : i in [1..#M`cusps]]));
  g := M`genus;
  if (g lt 3) then
      return prec, (g eq 2), 1;
  end if;
  k := 2;
  sturm := k/2*(2*M`genus-2)+M`v2*Floor(k/4)+M`v3*Floor(k/3)+ k/2*M`vinf;
  prec := Max(prec, Ceiling(M`N*(sturm)/M`degree));
  Pol<[x]>:=PolynomialRing(Rationals(),g);
  PP:=ProjectiveSpace(Rationals(),g-1);
  // For high levels, repeatedly computing FindModularForms becomes expensive and the required precision is larger anyway, so we step by a larger amount
  prec_step := Ceiling(M`N / 24);
  while true do
      repeat
	  prec +:= prec_step;
	  found := false;
	  // for now, doing that naively
	  while (not found) do
	      M:=FindModularForms(2,M,prec);
	      M:=FindCuspForms(M);
	      F:=M`F0;
	      assert #F eq g;
	      I2:=FindRelations(F,2);
	      I2:=[Pol!P: P in I2];
	      found := #I2 in {(g-1)*(g-2) div 2,((g-2)*(g-3)) div 2};
	      prec +:= prec_step;
	  end while;
	  prec -:= prec_step;
	  Q0:=Scheme(PP,I2);
	  dimQ0:=Dimension(Q0);
      until dimQ0 ge 1;
      if  #I2 eq (g-1)*(g-2) div 2 then
	  if dimQ0 gt 1 then
	      continue;
	  end if;
	  Q0:=Curve(PP,I2);
	  if not (IsIrreducible(Q0) and IsReduced(Q0)) then
	      continue;
	  elif Genus(Q0) ne 0 then
	      continue;
	  end if;
          return prec, true, 2;
      end if;
      if (dimQ0 eq 1) then
	  return prec, false, 2;
      end if;
      if g eq 3 then
          I4:=FindRelations(F,4);
          if #I4 eq 1 then
	      return prec, false, 4;
	  end if;
      else
	  mon3:=[m: m in MonomialsOfWeightedDegree(Pol,3)];
	  V:=VectorSpace(Rationals(),#mon3);

	  W:=sub<V| [V![MonomialCoefficient(x[i]*f,m): m in mon3] : i in [1..g], f in I2]>;
	  assert Dimension(W) eq ((g-3)*(g^2+6*g-10) div 6) - (g-3);

	  I3:=FindRelations(F,3);
	  I3:=[Pol!P: P in I3];

	  Q0:=Scheme(PP,I2 cat I3);
	  dimQ0:=Dimension(Q0);
	  if dimQ0 ge 1 then
              return prec, false, 3;
	  end if;
      end if;
  end while;
end intrinsic;

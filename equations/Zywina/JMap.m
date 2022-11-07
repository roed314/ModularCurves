import "ModularCurves.m" : FindModularForms, FindCuspForms, FindRelations;

// getting the JMap from the q-expansions
function FindFormAsRationalFunction(form, R, all_fs, wt_diff : min_k := 0)
    precs := [AbsolutePrecision(fs[1]) : fs in all_fs];
    _<q> := Universe(all_fs[1]);
    degmons := AssociativeArray();
    found := false;
    if min_k eq 0 then min_k := wt_diff; end if;
    k := min_k;
    printf "Trying to find form with weight %o\n", k;
    for d in {k-wt_diff, k} do
 	degmons[d] := MonomialsOfWeightedDegree(R, d div 2);
    end for;
    all_prods := [[Evaluate(m, all_fs[i]) + O(q^precs[i]) 
		   : m in degmons[k]] : i in [1..#all_fs]];
    // That's relevant when we compare differentials
    for i in [1..#all_fs] do
	all_prods[i] cat:= [form*Evaluate(m, all_fs[i]) 
			    + O(q^precs[i]) : m in degmons[k-wt_diff]];
    end for;
    // We should look for relations over QQ
    mats := [* Matrix([&cat[Eltseq(x) : x in AbsEltseq(f)] 
		       : f in prods]) : prods in all_prods *];
    mat := mats[1];
    for i in [2..#mats] do
	mat := HorizontalJoin(mat, mats[i]);
    end for;
    ker := Kernel(mat);
    found :=  exists(v){v : v in Basis(ker)
 			| not &and[v[i] eq 0 :
 				   i in [1..#degmons[k]]] and
 			      not &and[v[#degmons[k]+i] eq 0 :
 				       i in [1..#degmons[k-wt_diff]]]};
    assert found;
    v := ChangeRing(v*Denominator(v), Integers());
    num := &+[v[i]*degmons[k][i] : i in [1..#degmons[k]]];
    denom := -&+[v[#degmons[k]+i]*degmons[k-wt_diff][i]
 		 : i in [1..#degmons[k-wt_diff]]];
    return num / denom;
end function;

intrinsic JMap(X::Rec) -> FldFunRatMElt, FldFunRatMElt, FldFunRatMElt
{Computes E4, E6 and j as rational function, when the given qexpansions are the variables.}
    qexps := X`F0;
    g := X`genus;
    precs := [AbsolutePrecision(f) : f in qexps[1]]; 
    R<q> := Universe(qexps[1]);
    all_fs := [[f[i] + O(q^precs[i]) : f in qexps] : i in [1..#X`cusps]];
    // These bounds are from Rouse, DZB and Drew's paper
    E4_k := Ceiling((2*X`vinf + X`v2 + X`v3 + 5*g-4)/(g-1));  
    E6_k := Ceiling((3*X`vinf + X`v2 + 2*X`v3 + 7*g-6)/(g-1));
    if IsOdd(E4_k) then
	E4_k +:= 1;
    end if;
    if IsOdd(E6_k) then
	E6_k +:= 1;
    end if;    
    R<[x]> := Universe(X`psi);
    degmons := AssociativeArray();
    // we scan starting from the bounds in the paper
    prec := Maximum(precs);
    
    E4 := qExpansion(EisensteinSeries(ModularForms(1,4))[1],prec);
    E4 := Evaluate(E4, q^(X`N)) + O(q^prec);
    E4 := FindFormAsRationalFunction(E4, R, all_fs, 4 : min_k := E4_k);
    E6 := qExpansion(EisensteinSeries(ModularForms(1,6))[1],prec);
    E6 := Evaluate(E6, q^(X`N)) + O(q^prec);
    E6 := FindFormAsRationalFunction(E6, R, all_fs, 6 : min_k := E6_k);
    j := 1728*E4^3/(E4^3-E6^2);
    _<[x]> := Parent(E4);
    _<[x]> := Parent(j);
    return E4, E6, j;
end intrinsic;

intrinsic RequiredPrecision(M::Rec) -> RngIntElt
{.}
  M := FindModularForms(2,M,1);
  prec := Integers()!(M`N * Maximum([1/M`widths[i] : i in [1..#M`cusps]])) + 1;
  found := false;
  g := M`genus;
  // for now, doing that naively
  while (not found) do
      M:=FindModularForms(2,M,prec);
      M:=FindCuspForms(M);
      F:=M`F0; 
      assert #F eq g; 

      Pol<[x]>:=PolynomialRing(Rationals(),g);
      PP:=ProjectiveSpace(Rationals(),g-1);
      
      I2:=FindRelations(F,2);
      found := #I2 in {(g-1)*(g-2) div 2,((g-2)*(g-3)) div 2};
      prec +:= 1;
  end while;
  d :=  Ceiling((3*M`vinf + M`v2 + 2*M`v3 + 7*g-6)/(g-1));
  if IsOdd(d) then d+:= 1; end if; 
  prec_for_j := Floor(d/6) + 1 + M`N;
  prec := Maximum(prec, prec_for_j);
  return prec;
end intrinsic;	  
	  

freeze;

// exports intrinsic JMap

import "Box.m" : BoxMethod, qExpansions;

// function: FindCurveSimple
// input: qexps - a list of q-expansions
//        prec - precision
//        n_rel - maximal degree in which we expect to find a relation.
// output: X - a curve describing the image of the canonical embedding using these q-expansions 

function FindCurveSimple(qexps, prec, n_rel)
    R<q> := Universe(qexps);
    K := BaseRing(R);
    zeta := K.1;
    fs := [f + O(q^prec) : f in qexps];
    g := #fs;
    R<[x]> := PolynomialRing(K,g);
    degmons := [MonomialsOfDegree(R, d) : d in [1..n_rel]];
    prods := [[Evaluate(m, fs) + O(q^prec) : m in degmons[d]] :
	      d in [1..n_rel]];
    // kers := [Kernel(Matrix([AbsEltseq(f) : f in prod])) : prod in prods];
    kers := [Kernel(Matrix([&cat[Eltseq(x) : x in AbsEltseq(f)] : f in prod])) : prod in prods];
    rels := [[&+[Eltseq(kers[d].i)[j]*degmons[d][j] : j in [1..#degmons[d]]] :
	      i in [1..Dimension(kers[d])]] : d in [1..n_rel]];
    // We want to generate the ideal with the lowest possible degree
    is_all := false;
    d := 1;
    not_in_I := rels;
    I := ideal<R | 0>;
    while not is_all do
	I +:= ideal<R | &cat not_in_I[1..d]>;
	not_in_I := [[x : x in r | x notin I] : r in rels];
	is_all := &and[IsEmpty(x) : x in not_in_I];
	d +:= 1;
    end while;
    // This might throw an error in the hyperelliptic case. 
    X := Curve(ProjectiveSpace(R),I);
    return X;
end function;

function FindHyperellipticCurve(qexps, prec)
    R<q> := Universe(qexps);
    K := BaseRing(R);
    fs := [f + O(q^prec) : f in qexps];
    g := #fs;
    T, E := EchelonForm(Matrix([&cat[Eltseq(x)
				     : x in AbsEltseq(f)] : f in fs]));
    fs := [&+[E[j][i]*fs[i] : i in [1..g]] : j in [1..g]];
    x := fs[g-1] / fs[g];
    y := q * Derivative(x) / fs[g];
    mons := [x^i : i in [0..2*g+2]] cat [-y^2];
    denom := q^(-(2*g+2)*Valuation(x));
    f_mons := [denom*m + O(q^AbsolutePrecision(y)) : m in mons];
    ker := Kernel(Matrix([AbsEltseq(f : FixedLength) : f in f_mons]));
    assert Dimension(ker) eq 1;
    ker_b := Basis(ker)[1];
    ker_b /:= -ker_b[2*g+4];
    R<x> := PolynomialRing(K);
    poly := &+[ker_b[i+1]*x^i : i in [0..2*g+2]];
    X := HyperellipticCurve(-poly);
    return X, fs;
end function;

function FindFormAsRationalFunction(form, R, fs, wt_diff : min_k := 0)
     prec := AbsolutePrecision(form);
     _<q> := Universe(fs);
     degmons := AssociativeArray();
     found := false;
     if min_k eq 0 then min_k := wt_diff; end if;
     k := min_k;
     while (not found) do
 	vprintf ModularCurves, 1:
 	    "Trying to find form with weight %o\n", k;
 	for d in {k-wt_diff, k} do
 	    degmons[d] := MonomialsOfWeightedDegree(R, d div 2);
 	end for;
 	prods := [Evaluate(m, fs) + O(q^prec) : m in degmons[k]];
	// That's relevant when we compare differentials
// 	prods cat:= [form*Evaluate(m, fs)*q^wt_diff + O(q^prec)
	prods cat:= [form*Evaluate(m, fs) + O(q^prec)
		     : m in degmons[k-wt_diff]];
	// We should look for relations over QQ
	mat := Matrix([&cat[Eltseq(x)
			    :  x in AbsEltseq(f)] : f in prods]);
	ker := Kernel(mat);
 	found :=  exists(v){v : v in Basis(ker)
 			| not &and[v[i] eq 0 :
 				   i in [1..#degmons[k]]] and
 			not &and[v[#degmons[k]+i] eq 0 :
 				 i in [1..#degmons[k-wt_diff]]]};
 	k +:= 2;
     end while;
     k -:= 2;
     num := &+[v[i]*degmons[k][i] : i in [1..#degmons[k]]];
     denom := -&+[v[#degmons[k]+i]*degmons[k-wt_diff][i]
 		: i in [1..#degmons[k-wt_diff]]];
     return num / denom;
 end function;

intrinsic JMap(G::GrpPSL2, X::Crv[FldRat], qexps::SeqEnum[RngSerPowElt],
	       K::RngIntElt : LogCanonical := false) ->
  FldFunRatMElt, FldFunRatMElt, FldFunRatMElt
{Computes E4, E6 and j as rational function, when the given qexpansions are the variables.}
    g := #qexps;
    prec := AbsolutePrecision(qexps[1]);
    if LogCanonical then
	// This should work, but for some reason we don't always find them there!
	E4_k := 4;
	E6_k := 6;
    else
	assert g eq Genus(G);
	nu_infty := #Cusps(G);
	H := Universe(EllipticPoints(G)); 
	nu_2 := #[H | pt : pt in EllipticPoints(G) |
		      Order(Matrix(Stabilizer(pt, G))) eq 4];
	nu_3 := #[H | pt : pt in EllipticPoints(G) |
		      Order(Matrix(Stabilizer(pt, G))) eq 6];
	// These bounds are from Rouse, DZB and Drew's paper
	E4_k := Ceiling((2*nu_infty + nu_2 + nu_3 + 5*g-4)/(g-1));  
	E6_k := Ceiling((3*nu_infty + nu_2 + 2*nu_3 + 7*g-6)/(g-1));
	if IsOdd(E4_k) then
	    E4_k +:= 1;
	end if;
	if IsOdd(E6_k) then
	    E6_k +:= 1;
	end if;
    end if;
    R<q> := Universe(qexps);
    fs := [f + O(q^prec) : f in qexps];
    R<[x]> := CoordinateRing(AmbientSpace(X));
    // R<[x]> := PolynomialRing(Rationals(),g);
    degmons := AssociativeArray();
    // Because there is something wrong with the bounds,
    // we actually scan starting from the bounds in the paper
    E4 := qExpansion(EisensteinSeries(ModularForms(1,4))[1],prec);
    E4 := Evaluate(E4, q^K) + O(q^prec);
    E4 := FindFormAsRationalFunction(E4, R, fs, 4 : min_k := E4_k);
    E6 := qExpansion(EisensteinSeries(ModularForms(1,6))[1],prec);
    E6 := Evaluate(E6, q^K) + O(q^prec);
    E6 := FindFormAsRationalFunction(E6, R, fs, 6 : min_k := E6_k);
    j := 1728*E4^3/(E4^3-E6^2);
    _<[x]> := Parent(E4);
    return E4, E6, j;
end intrinsic;

intrinsic JMap(X::Crv[FldRat], fs::SeqEnum[RngSerPowElt], K::RngIntElt) ->
	     RngMPolElt, RngMPolElt, FldFunRatMElt
{Compute the JMap for the log canonical model.}
    R := CoordinateRing(AmbientSpace(X));
    _<q> := Universe(fs);
    prec := AbsolutePrecision(fs[1]);
    E4 := qExpansion(EisensteinSeries(ModularForms(1,4))[1],prec);
    E4 := Evaluate(E4, q^K) + O(q^prec);
    E4 := FindFormAsRationalFunction(E4, R, fs, 4 : min_k := 4);
    E6 := qExpansion(EisensteinSeries(ModularForms(1,6))[1],prec);
    E6 := Evaluate(E6, q^K) + O(q^prec);
    E6 := FindFormAsRationalFunction(E6, R, fs, 6 : min_k := 6);
    j := 1728*E4^3/(E4^3-E6^2);
    _<[x]> := Parent(j);
    return E4, E6, j;
end intrinsic;

// This only works when conjugating one eigenform
// gives you another eigenform
function FindRationalCurve(qexps, prec, n_rel)
    _<q> := PowerSeriesRing(Rationals());
    fs := [];
    for qexp in qexps do
      K := BaseRing(Parent(qexp));
      zeta := K.1;
      for j in [0..Degree(K)-1] do
        f := &+[Trace(zeta^j*Coefficient(qexp, n))*q^n : n in [1..prec-1]];
        f +:= O(q^prec);
        Append(~fs, f);
      end for;
    end for;
    T, E := EchelonForm(Matrix([AbsEltseq(f) : f in fs]));
    fs := [&+[E[j][i]*fs[i] : i in [1..#fs]] : j in [1..#fs]];
    n := #fs;
    R<[x]> := PolynomialRing(Rationals(),n);
    degmons := [MonomialsOfDegree(R, d) : d in [1..n_rel]];
    prods := [[Evaluate(m, fs) + O(q^prec) : m in degmons[d]] :
	      d in [1..n_rel]];
    kers := [Kernel(Matrix([AbsEltseq(f) : f in prod])) : prod in prods];
    rels := [[&+[Eltseq(kers[d].i)[j]*degmons[d][j] : j in [1..#degmons[d]]] :
	      i in [1..Dimension(kers[d])]] : d in [1..n_rel]];
    I := ideal<R | &cat rels>;
    X := Curve(ProjectiveSpace(R),I);
    return X;
end function;

intrinsic CanonicalRing(PG::GrpPSL2) -> Crv[FldRat],
                                      SeqEnum[RngSerPowElt],
                                      RngIntElt
{Return the curve, q-expansions and K (denominator of the power in q-expansions) for the model of the canonical ring.}
    s := Signature(PG);
    level := Level(PG);
    g := s[1];
    e := s[2];
    delta := s[3];
    assert delta ge 1;
    r := #e;
    if r eq 0 then
	if g ge 1 then
	    // This is Theorem 4.1.3 in DZB+Voight Stacky curve paper
	    // for log curves
	    gen_degs := [3,2,1,1];
	    rel_degs := [6,4,3,2];
	    idx := Minimum(delta, 4);
	    gen_deg := gen_degs[idx];
	    rel_deg := rel_degs[idx];
	else
	    // This follows from the discussion of the genus 0 case
	    gen_degs := [0,1,1,1];
	    rel_degs := [0,0,0,2];
	    idx := Minimum(delta, 4);
	    gen_deg := gen_degs[idx];
	    rel_deg := rel_degs[idx];
	end if;
    else
	e := Maximum(e);
	if g ge 1 then
	    // This is Theorem 8.4.1 in stacky curve
	    gen_deg := Maximum(3,e);
	    rel_deg := 2*gen_deg;
	else
	    if delta eq 0 then
		if r eq 3 then 
		    exceptional := [[2,3,7],[2,3,8],[2,3,9],[2,4,5],[2,5,5],[3,3,4],[3,3,5],
				    [3,3,6],[3,4,4],[3,4,5],[4,4,4]];
		    gen_degs := [21,15,9,10,6,12,9,6,8,5,4];
		    rel_degs := [42,30,24,20,16,24,18,15,16,16,5];
		elif r eq 4 then
		    exceptional := [[2,2,2,3], [2,2,2,4],[2,2,2,5],[2,2,3,3],
				    [2,2,3,4],[2,3,33]];
		    gen_degs := [9,7,5,6,4,3];
		    rel_degs := [18,14,12,12,13,9];
		elif r eq 5 then
		    exceptional := [[2,2,2,2,2],[2,2,2,2,3]];
		    gen_degs := [5,3];
		    rel_degs := [10,8];
		else
		    exceptional := [[2 : i in [1..r]]];
		    gen_degs := [3];
		    rel_degs := [6];
		end if;
		
		if s[2] in exceptional then
		    idx := Index(exceptional, s[2]);
		    gen_deg := gen_degs[idx];
		    rel_deg := rel_degs[idx];
		end if;
	    end if;
	    // Theorem 9.3.1
	    gen_deg := e;
	    rel_deg := 2*e;
	end if;
    end if;
    // TODO - fix the needed precision
    prec := 100;
    ring_gens := AssociativeArray();
    for d in [1..gen_deg] do
	G := ImageInLevelGL(PG);
	fs, K := BoxMethod(G, prec : wt := 2*d);
	// The Eisenstein series are returned with denominator N = level !!
	eis := EisensteinSeries(ModularForms(PG,2*d));
	eis := [qExpansion(f, prec) : f in eis];
	gap := level div K;
	eis_elt := [AbsEltseq(f) : f in eis];
	assert &and[ &and[f[x] eq 0 : x in [1..#f] | x mod gap ne 1] : f in eis_elt];
	eis_elt := [[f[gap*i+1] : i in [0..(#f-1) div gap]] : f in eis_elt];
	eis := [Universe(eis)!f_elt : f_elt in eis_elt];
	ring_gens[d] := fs cat eis;
    end for;
    fs := &cat [ring_gens[d] : d in [1..gen_deg]];
    grading := &cat[[d : x in ring_gens[d]] : d in [1..gen_deg]];
    R<[x]> := PolynomialRing(Rationals(),grading);
    degmons := [MonomialsOfWeightedDegree(R, d) : d in [1..rel_deg]];
    _<q> := Universe(fs);
    prods := [[Evaluate(m, fs) + O(q^prec) : m in degmons[d]] :
	      d in [1..rel_deg]];
    coeffs := [[&cat[Eltseq(x) : x in AbsEltseq(f)] : f in prod]
	       : prod in prods];
    kers := [IsEmpty(c) select VectorSpace(Rationals(),0) else Kernel(Matrix(c))
	     : c in coeffs];
    rels := [[&+[Eltseq(kers[d].i)[j]*degmons[d][j] : j in [1..#degmons[d]]] :
	      i in [1..Dimension(kers[d])]] : d in [1..rel_deg]];
    is_all := false;
    d := 1;
    not_in_I := rels;
    I := ideal<R | 0>;
    while not is_all do
	I +:= ideal<R | &cat not_in_I[1..d]>;
	not_in_I := [[x : x in r | x notin I] : r in rels];
	is_all := &and[IsEmpty(x) : x in not_in_I];
	d +:= 1;
    end while;
    X := Curve(ProjectiveSpace(R),I);
    return X, fs, K;
end intrinsic;

intrinsic CoveringMap(X::Crv, X_cov::Crv, fs::SeqEnum[RngSerPowElt],
		      fs_cov::SeqEnum[RngSerPowElt]) -> MapSch[Crv, Crv]
{Given modular curves X, X_cov with coordinates given by q-expansions fs, fs_cov,
 such that X_cov is a covering of X, compute the covering map. }
  prec_fs := Minimum([AbsolutePrecision(f) : f in fs]);
  prec_fs_cov := Minimum([AbsolutePrecision(f) : f in fs_cov]);
  prec := Minimum(prec_fs, prec_fs_cov);
  mat := Matrix([AbsEltseq(f)[1..prec] : f in fs_cov]);
  v := Matrix([AbsEltseq(f)[1..prec] : f in fs]);
  T := Solution(mat, v);
  x := GeneratorsSequence(CoordinateRing(X_cov));
  cov_map := Vector(x) * ChangeRing(Transpose(T), CoordinateRing(X_cov));
  return map<X_cov -> X | Eltseq(cov_map)>;
end intrinsic;

intrinsic JMap(cov::MapSch[Crv,Crv], E4::FldFunRatMElt, E6::FldFunRatMElt) ->
	  FldFunRatMElt, FldFunRatMElt, FldFunRatMElt
{Given a covering map of modular curves and the E4, E6 as rational functions on the
target curve, returns the E4, E6 and j-map on the top curve.}
  cov_sharp := AlgebraMap(cov);
  y := GeneratorsSequence(Domain(cov_sharp));
  polys := [cov_sharp(yy) : yy in y];
  E4_cov := Evaluate(E4, polys);
  E6_cov := Evaluate(E6, polys);
  j_cov := 1728*E4_cov^3/(E4_cov^3-E6_cov^2);
  return E4_cov, E6_cov, j_cov;
end intrinsic;

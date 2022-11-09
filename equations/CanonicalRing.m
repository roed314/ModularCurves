import "Zywina/ModularCurves.m" : FindModularForms;

intrinsic CanonicalRing(M::Rec : Precision := 0) -> SeqEnum, SeqEnum
{Return the curve, q-expansions (denominator of the power in q-expansions) for the model of the canonical ring.}
    if (Precision eq 0) then
	prec := 10;// !! TODO - figure out needed precision here
    else
	prec := Precision;
    end if;
    level := M`N;
    g := M`genus;
    e := [2 : i in [1..M`v2]] cat [3 : i in [1..M`v3]];
    delta := M`vinf;
    assert delta ge 1;
    r := #e;
    if r eq 0 then
	// for g >= 1
	// This is Theorem 4.1.3 in DZB+Voight Stacky curve paper
	// for log curves
	gen_degs := [3,2,1,1];
	rel_degs := [6,4,3,2];
	// this is using Table IIa
	if g ge 2 then
	    h := g + delta - 1;
	    gen_dims := [
		[ [g,g,1],  // hyperelliptic
		  [g,2,1],  // exceptional
		  [g,2,1] ], // non-exceptional
		[ [h, h-2],
		  [h, 1],
		  [h, 1] ],
		[[h]],
		[[h]]
		];
	    rel_dims := [
		[ [0, (g-1)*(g-2) div 2, (g-1)*(g-1), (g-1)*(g+2), 2*(g-1), 1],
		  [0, (g-2)*(g-3) div 2, 3*g-5, g+2, 1, 1], // exceptional
		  [0, (g-2)*(g-3) div 2, 2*g-2, g+2, 1, 1]], // non-exceptional
		[ [0, (h-2)*(h-3) div 2, (h-1)*(h-3), (h-2)*(h-3) div 2],
		  [0, (h-2)*(h-3) div 2, 2*(h-2)],
		  [0, (h-2)*(h-3) div 2]],
		[[0, (h-2)*(h-3) div 2 + delta - 3, g]],
		[[0, (h-2)*(h-3) div 2 + delta - 3]]
	    ];
	elif g eq 1 then
	    gen_dims := [
		[ [1,1,1] ],
		[ [2,1] ],
		[ [3] ],
		[ [delta] ]  
		];
	    rel_dims := [
		[ [0,0,0,0,0,1] ],
		[ [0,0,0,1] ],
		[ [0,0,1] ],
		[ [0, (delta-1)*(delta-4) div 2] ]
		];
	else
	    gen_dims := [[],
			[ [1] ],
			[ [2] ],
			[ [delta-1] ]];
	    rel_dims := [ [[]], [[]], [[]], [ [0, (delta-3)*(delta-4) div 2]]];
	    // This follows from the discussion of the genus 0 case
	    gen_degs := [0,1,1,1];
	    rel_degs := [0,0,0,2];
	end if;
	idx := Minimum(delta, 4);	
	rel_dims := rel_dims[idx];
	gen_dims := gen_dims[idx];
	gen_deg := gen_degs[idx];
	rel_deg := rel_degs[idx];
    else
	e := Maximum(e);
	if g ge 1 then
	    // This is Theorem 8.4.1 in stacky curve
	    gen_deg := Maximum(3,e);
	    rel_deg := 2*gen_deg;
	    if (r eq 1) then
		gen_dims := [ [1,0,0,1,0,1], [1,0,1,0,1] ];
		rel_dims := [[0 : i in [1..15-2*e]] cat [1]];
	    elif (r eq 2) then
		gen_dims := [ [1,1,0,1] ];
		rel_dims := [ [0 : i in [1..7]] cat [1] ];
	    else
		gen_dims := [ [1,2] ];
		rel_dims := [ [0 : i in [1..5]] cat [1] ];
	    end if;
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
		
		if e in exceptional then
		    idx := Index(exceptional, e);
		    gen_deg := gen_degs[idx];
		    rel_deg := rel_degs[idx];
		end if;
	    end if;
	    // Theorem 9.3.1
	    gen_deg := e;
	    rel_deg := 2*e;
	end if;
    end if;
    ring_gens := AssociativeArray();
    for d in [1..gen_deg] do
	ring_gens[d] := FindModularForms(2*d, M, prec)`F;
    end for;
    qexps := &cat [ring_gens[d] : d in [1..gen_deg]];
    precs := [AbsolutePrecision(fs[1]) : fs in qexps];
    _<q> := Universe(qexps[1]);
    all_fs := [[f[i] + O(q^precs[i]) : f in qexps] : i in [1..#M`cusps]];
    grading := &cat[[d : x in ring_gens[d]] : d in [1..gen_deg]];
    R<[x]> := PolynomialRing(Rationals(),grading);
    degmons := [MonomialsOfWeightedDegree(R, d) : d in [1..rel_deg]];
    all_prods := [[[Evaluate(m, all_fs[i]) + O(q^precs[i]) 
		   : m in degmons[d]] : i in [1..#all_fs]] : d in [1..rel_deg]];
    // We should look for relations over QQ
    all_mats := [[* Matrix([&cat[Eltseq(x) : x in AbsEltseq(f)] 
			    : f in prods]) : prods in all_prods_d *] 
		 : all_prods_d in all_prods];
    kers := [* *];
    for mats in all_mats do
	mat := mats[1];
	for i in [2..#mats] do
	    mat := HorizontalJoin(mat, mats[i]);
	end for;
	ker := Kernel(mat);
	Append(~kers, ker);
    end for; 
    // For the other cases we haven't implemented this sanity check
    if ((g ge 2) or ((g eq 1) and (r le 3))) then
	require [Dimension(k) : k in kers] in rel_dims : 
	  "Not sufficient precision!";
    end if;
    rels := [[&+[Eltseq(kers[d].i)[j]*degmons[d][j] : j in [1..#degmons[d]]] :
	      i in [1..Dimension(kers[d])]] : d in [1..rel_deg]];
    I := ideal<R | &cat rels>;
    rels := MinimalBasis(I);
    I := Ideal(rels);
    X := Curve(ProjectiveSpace(R),I);
    _<q> := Universe(qexps[1]);
    fs := [[f + O(q^precs[i]) : f in qexps[i]] : i in [1..#qexps]];
    M`F0 := fs;
    M`psi := DefiningPolynomials(X);
    return fs, M`psi;
end intrinsic;

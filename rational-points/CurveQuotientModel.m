// NOT A FINAL VERSION
// JUST TO HELP PEOPLE WITH TEST CURVES


// code to compute X_0(N) and the quotient map to X_0(N) / w_d for an Atkin-Lehner involution w_d.
// code should work when X_0(N) is not hyperelliptic or bielliptic (with elliptic quotient) (all such models for X_0(N) are known anyway)
// There are finitely many quotients of X_0(N) that are hyperelliptic and these are all known (work of Furemoto and Hasegawa). The code requires as input whether the quotient curve is hyperelliptic or not. (Could create a separate data file to easily check this, given n and d).
// code will sometimes not work when the quotient is hyperelliptic as the elimination ideal quotients too much out.
// if curve is bielliptic then small modifications of the code should work.


// N is the level, B is a set of cusp forms, prec is the precision, check is true or false and verifies computations up to the Sturm bound
Curve_X := function(N, B, prec, check);  
    dim:=#B;
    L<q>:=LaurentSeriesRing(Rationals(),prec);
    R<[x]>:=PolynomialRing(Rationals(),dim);
    Bexp:=[L!qExpansion(B[i],prec) : i in [1..dim]];
    eqns:=[R | ];
	d:=1;
	tf:=false;
	while tf eq false do
		d:=d+1;
		mons:=MonomialsOfDegree(R,d);
		monsq:=[Evaluate(mon,Bexp) : mon in mons];
		V:=VectorSpace(Rationals(),#mons);
		W:=VectorSpace(Rationals(),prec-10);
		h:=hom<V->W | [W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]]>;
		K:=Kernel(h);
		eqns:=eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
        	I:=Radical(ideal<R | eqns>);
		X:=Scheme(ProjectiveSpace(R),I);
		if Dimension(X) eq 1 then
			if IsIrreducible(X) then
				X:=Curve(ProjectiveSpace(R),eqns);
				if Genus(X) eq dim then
					tf:=true;
				end if;
			end if;
		end if;
	end while;

    assert Genus(X) eq dim;
    
    if check eq true then   // should be no need to check correctness like this for the quotient curve if genus is correct
       indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];	
	   indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)

	    for eqn in eqns do
		    eqnScaled:=LCM([Denominator(c) : c in Coefficients(eqn)])*eqn;
		    wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		    hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound.
						 // See Stein's book, Thm 9.18.
		    Bexp1:=[qExpansion(B[i],hecke+10) : i in [1..dim]]; // q-expansions
                        					    // of basis for S 
                        					    // up to precision hecke+10.
		    assert Valuation(Evaluate(eqnScaled,Bexp1)) gt hecke+1;
	    end for; // We have now checked the correctness of the equations for X.	
    end if;
 return(X);
end function;

// N is the level, d is the subscript of the Atkin-Lehner involution, h is true or false depending on whether the quotient curve is hyperelliptic or not.


Curve_and_Map := function(N,d,h);

    C := CuspForms(N);
    g := Dimension(C);
    ALd := AtkinLehnerOperator(C, d);
    NN := Nullspace(Matrix(ALd - 1));
    NNc := Nullspace(Matrix(ALd + 1));

    // might need to change the 6* to another integer to make sure we have integer coefficients.
    BN  := [&+[(Integers()!(6*Eltseq(Basis(NN )[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NN)]];
    g2 := #BN;
    BNc := [&+[(Integers()!(6*Eltseq(Basis(NNc)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NNc)]];

    prec := 5*N; // can change this

    XN := Curve_X(N, BN cat BNc,prec, true);  // The curve X_0(N)
    assert Genus(XN) eq Dimension(JZero(N));  // Sanity Check!
    A<[x]> := AmbientSpace(XN);
    row := [x[i] : i in [1..g2]] cat [-x[i] : i in [g2+1..g]];
    wd := iso<XN -> XN | row, row >;

    if h eq false then // quotient curve is not hyperelliptic and we use the canonical embedding
       XNwd := Curve_X(N, BN, prec, false);  // The curve X_0(N) / w_d
       assert Genus(XNwd) eq g2; 
       phi := map<XN -> XNwd | [x[i] : i in [1..g2]]>;  // The quotient map
    end if;

    if h eq true then 
       XNwd,phi := CurveQuotient(AutomorphismGroup(XN,[wd]));
    end if;

    return XN, XNwd, phi;
end function;


/* 

OLDER CODE / ALTERNATIVES, SAFE TO IGNORE

// Hyperelliptic Quotient:

// Example for X_0(67)

I := Ideal(XN);
assert #BN eq 2;
EI := EliminationIdeal(I,{x[3],x[4],x[5]});
RR<[w]>:=PolynomialRing(Rationals(),3);

neqn := Evaluate(Basis(EI)[1],[0,0,w[1],w[2],w[3]]);
Y := Curve(ProjectiveSpace(RR),neqn);

assert Genus(Y) eq 2;
_,H := IsHyperelliptic(Y);
SH := SimplifiedModel(H);
// Hyperelliptic Curve defined by y^2 = x^6 + 2*x^5 + x^4 - 2*x^3 + 2*x^2 - 4*x + 1 over Rational Field
// Matches Galbraith model.


    /* if h eq true then // quotient curve is hyperelliptic. We compute the quotient using an elimination ideal (this is much faster than Magma's inbuilt quotient function)
       I := Ideal(XN);
       if g2 lt g-g2 then  // we use the most variables in the elimination ideal to have a better chance of getting a model.
          len := g-g2;
          EI := EliminationIdeal(I,{x[i] : i in [g2+1..g]}); 
       else len := g2;
          EI := EliminationIdeal(I,{x[i] : i in [1..g2]}); 
       end if;
       
       RR<[w]>:=PolynomialRing(Rationals(),len);
       eqns := Basis(EI);
       if g2 lt g-g2 then
           neqns := [ Evaluate(eqq,ZeroSequence(Integers(), g-len) cat [w[i] : i in [1..len]]) : eqq in eqns];
       else neqns := [ Evaluate(eqq, [w[i] : i in [1..len]] cat ZeroSequence(Integers(), g-len)) : eqq in eqns];
       end if;
       Y := Curve(ProjectiveSpace(RR),neqns); // this will be usually be a singular model in projective space
       assert Genus(Y) eq g2;
       
       if g2 lt g-g2 then
           psi := map<XN -> Y | [x[i] : i in [g2+1..g]]>;  // quotient map to simplified model
       else psi := map<XN -> Y | [x[i] : i in [1..g2]]>;
       end if;
       tf,H,mu := IsHyperelliptic(Y);   // H is the curve in weighted projective space
       assert tf;
       XNwd,nu := SimplifiedModel(H);   // Simplified model for the curve
       phi := Expand(psi*mu*nu);        // Quotient map.
    end if;       
    */
 

*/


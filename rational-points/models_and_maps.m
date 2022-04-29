// (WORK IN PROGRESS)

// Main purpose of this code is to compute X_0(N) and the quotient map to X_0(N) / w_d for an Atkin-Lehner involution w_d.
// Code should work when X_0(N) is not genus 0, elliptic, hyperelliptic or bielliptic (when working with an elliptic quotient) (all such models for X_0(N) are known anyway)
// There are finitely many quotients of X_0(N) that are hyperelliptic and these are all known (work of Furemoto and Hasegawa). The code requires as input whether the quotient curve is hyperelliptic or not, but will work even if this is not known. (It would be good to create a separate data file to easily check this, given N and d).

// The main function also outputs additional information (such as other AL involutions and cusp forms used)
// The code also includes a function to diagonalise an involution and output a new model.

// TODO 
// relatively easy things to do :
// - Some small adaptations will deal with the case when the curve X_0(N) is bielliptic
// - A few lines should also cover the elliptic and hyperelliptic curves X_0(N) (just for completeness)

// harder things to do (which should not be urgent!) :
// - Compute maps to quotients by multiple AL involutions (e.g. to star quotients).
// - Obtain a function that can compute the j-invariant of a given point (either by working with the point or by producing equations for the j-map)
// - Output the cusps on the model. When the cusps are rational there are not may non-cupsidal Q-rational points on the curves X_0(N), so this should be okay to do. When the cusps are not rational (non-square free level) then this probably requires extra work. Since the curves are coming from a canonical embedding via cusp forms there should be a straightforward way of doing this (?)

///////////////
/// Curve_X ///  (auxiliary function)
///////////////

// N is the level, B is a set of cusp forms, prec is the precision, check is true or false and accordingly verifies computations up to the Sturm bound
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

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

/////////////////////
/// Curve_and_Map /// 
/////////////////////

// N is the level, d is AL index, h is true or false depending on whether the quotient curve is hyperelliptic or not.
// If unsure whether the quotient curve is hyperelliptic and you don't want to look it up, then just set h to be true
// alternatively, try running it with h false, and if it doesn't terminate after a minute or two then the quotient is most likely hyperelliptic.

// Ouput :
// Model for X_0(N), Model for X_0(N) / w_d, Quotient map, w_d, sequence of the remaining Atkin-Lehner involutions, Basis of cuspforms for the plus-eigenspace, Basis of cuspforms for the minus-eigenspace

Curve_and_Map := function(N,d,h);

    C := CuspForms(N);
    g := Dimension(C);

    other_al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1 and m ne d];
    

    ALd := AtkinLehnerOperator(C, d);
    NN := Nullspace(Matrix(ALd - 1));
    NNc := Nullspace(Matrix(ALd + 1));

    // might need to change the 6* to another integer to make sure we have integer coefficients.
    BN  := [&+[(Integers()!(6*Eltseq(Basis(NN)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NN)]];
    g2 := #BN;
    BNc := [&+[(Integers()!(6*Eltseq(Basis(NNc)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NNc)]];

    M := Matrix(Basis(NN) cat Basis(NNc)); // change of basis matrix
    other_als := [ M*AtkinLehnerOperator(C,m)*(M^(-1)) : m in other_al_inds];

    prec := 5*N; // can change this

    XN := Curve_X(N, BN cat BNc,prec, true);  // The curve X_0(N)
    assert Genus(XN) eq Dimension(JZero(N));  // Sanity Check!
    A<[x]> := AmbientSpace(XN);
    row := [x[i] : i in [1..g2]] cat [-x[i] : i in [g2+1..g]];
    wd := iso<XN -> XN | row, row >;

    other_al_eqs := [ [&+[W[i,j]*x[j] : j in [1..g]] : i in [1..g]]   : W in other_als];
    other_als := [ iso<XN->XN | eqq,eqq> : eqq in other_al_eqs ];

    if h eq false then // quotient curve is not hyperelliptic and we use the canonical embedding
       XNwd := Curve_X(N, BN, prec, false);  // The curve X_0(N) / w_d
       assert Genus(XNwd) eq g2; 
       phi := map<XN -> XNwd | [x[i] : i in [1..g2]]>;  // The quotient map
    end if;

    if h eq true then 
       XNwd,phi := CurveQuotient(AutomorphismGroup(XN,[wd]));
    end if;

    return XN, XNwd, phi, wd, other_als, BN, BNc;
end function;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

/////////////////
/// Curve_X0N /// 
/////////////////

// A separate function to compute a model for X0N only. Will compute a model with w_N diagonalised.

Curve_X0N := function(N);
    C := CuspForms(N);
    ALN := AtkinLehnerOperator(C, N);
    NN := Nullspace(Matrix(ALN - 1));
    NNc := Nullspace(Matrix(ALN + 1));
    // might need to change the 6* to another integer to make sure we have integer coefficients.
    BN  := [&+[(Integers()!(6*Eltseq(Basis(NN)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NN)]];
    g2 := #BN;
    BNc := [&+[(Integers()!(6*Eltseq(Basis(NNc)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NNc)]];
    prec := 5*N; // can change this
    XN := Curve_X(N, BN cat BNc,prec, true);
    return XN;
end function;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

////////////////////////////////////////////////////////

//////////////////
/// diag_model /// 
//////////////////

// Input: A curve X and an involution w (given as an isomorphism or a map)
// Output: NX (a new model for X), map from X to NX, its inverse from NX to X, the new diagonalised involution Nw

// (it is faster to output two separate maps like this rather than an isomorphism, as otherwise Magma checks the maps are inverse to each other (I think), and this can take some time)


diag_model := function(X,w);

    A<[x]> := AmbientSpace(X);
    var := Dimension(A)+1;
    R<[x]> := PolynomialRing(Rationals(), var);
    eqX := DefiningEquations(X);
    eqw := DefiningEquations(w);
    Mw := Transpose(Matrix(w));
    Diag,T:=PrimaryRationalForm(Mw); 
    assert T*Mw*(T^-1) eq Diag;
    
    Coord_change_eqs := [&+[(T^(-1))[i,j]*x[j] : j in [1..var]] : i in [1..var]];
    Coord_change_eqs_inv := [&+[T[i,j]*x[j] : j in [1..var]] : i in [1..var]];
    Coord_change := hom<R->R | Coord_change_eqs >;

    New_eqX := [Coord_change(ee) : ee in eqX];

    NX := Curve(ProjectiveSpace(R),New_eqX); 
     
    New_eqw := [Diag[i,i]*x[i] : i in [1..var]];
    Nw := iso<NX->NX | New_eqw, New_eqw >;
     
    XtoNX := map<X->NX | Coord_change_eqs_inv  >;
    NXtoX := map<NX->X | Coord_change_eqs  >;
     
    return NX, XtoNX, NXtoX, Nw;
end function;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

////////////////////////
/// Extended Example ///
////////////////////////

N := 74;
d := 2;

// We compute a model for X_0(74) and the map to the quotient by the Atkin-Lehner involution w_2
// The quotient curve is non-hyperelliptic (although code will still work if you put 'true' below (in case you thought it was hyperelliptic or if you didn't know and didn't want to look it up!).

time X74, X74_w2, phi, w2, ws, BN, BNc := Curve_and_Map(74,2,false); // 1 second (if you use true it is 4 seconds and the quotient map is ugly)

assert Genus(X74) eq 8;
assert Genus(X74_w2) eq 4;

// The map to the quotient is just given by forgetting the final 4 coordinates

/*
Mapping from: Crv: X74 to Crv: X74_w2
with equations : 
x[1]
x[2]
x[3]
x[4]
*/

// w2 has matrix : Matrix(w2); 
/*
[ 1  0  0  0  0  0  0  0]                                       
[ 0  1  0  0  0  0  0  0]
[ 0  0  1  0  0  0  0  0]
[ 0  0  0  1  0  0  0  0]
[ 0  0  0  0 -1  0  0  0]
[ 0  0  0  0  0 -1  0  0]
[ 0  0  0  0  0  0 -1  0]
[ 0  0  0  0  0  0  0 -1]
*/

// The other Atkin-Lehner involutions are 

w37 := ws[1];
w74 := ws[2];

// Let's find a new model with w74 diagonalised, and the map to this new model

NX74, map1, map2, Nw74 := diag_model(X74,w74);

// Nw74 is now diagonalised, its matrix is : Matrix(Nw74);
/*
[ 1  0  0  0  0  0  0  0]
[ 0  1  0  0  0  0  0  0]
[ 0  0 -1  0  0  0  0  0]
[ 0  0  0 -1  0  0  0  0]
[ 0  0  0  0 -1  0  0  0]
[ 0  0  0  0  0 -1  0  0]
[ 0  0  0  0  0  0 -1  0]
[ 0  0  0  0  0  0  0 -1]
*/

// Let's compute the quotient curve X_0(74) / w_74 in three ways.
// The quotient is hyperelliptic

// 1.
// We'll use the original code
time _,Y1 := Curve_and_Map(74,74,true); // Under 1 second
// Hyperelliptic Curve defined by y^2 + (x^3 + x^2 + x + 1)*y = -x^5 - x^4 - x^3 - x^2 - x over Rational Field
 
// 2.
// We'll use our diagonalised model 

time Y2 := CurveQuotient(AutomorphismGroup(NX74,[Nw74])); // Under 1 second
// Hyperelliptic Curve defined by y^2 + (x^3 + x^2 + x + 1)*y = -x^4 - x^3 - x^2 over Rational Field

// 3.
// We'll use our old model with the non-diagonalised involutions

time Y3 := CurveQuotient(AutomorphismGroup(X74,[w74]));  // 33 seconds, this is very slow!
// Hyperelliptic Curve defined by y^2 + (x^3 + x^2 + x + 1)*y = -x^5 - x^4 - x^3 - x^2 - x over Rational Field


assert IsIsomorphic(Y1,Y2); // good!
assert IsIsomorphic(Y1,Y3); // good!

// Do we have the right curve?

// Galbraith gives the following simplified model on Page 43 of their thesis: y^2 = x^6 − 2*x^5 − x^4 − x^2 − 2*x + 1

simp_Y1 := SimplifiedModel(Y1);

// Hyperelliptic Curve defined by y^2 = x^6 - 2*x^5 - x^4 - x^2 - 2*x + 1 over Rational Field
// This matches Galbraith's model!

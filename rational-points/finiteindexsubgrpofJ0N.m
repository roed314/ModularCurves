// The main function in this file is finiteindexsubgrpofJ0N() which takes as input
// a positive number N
// and attempts to compute
// a list of linearly independent degree 0 divisors on X_0(N) generating a finite index subgroup of J_0(N)(Q).
//
// The function works by finding a number of small rational points on X_0(N)^+,
// using them to find a finite index subgroup of J_0(N)^+(Q), and then pulling them back.
//
// So, one hopes this function to work as desired when
// 1. there are sufficiently many small rational points on X_0(N)^+, and
// 2. rank J_0(N)(Q) = rank J_0(N)^+(Q)


load "new_models.m";
load "rank_calcs.m";

//This function computes the discriminant of the field a place is defined over.
discQuadPlace := function(P);
    assert Degree(P) eq 2;
    
	K := ResidueClassField(P);
    D := Discriminant(MaximalOrder(K));
    
	if IsDivisibleBy(D, 4) then
       D := D div 4;
    end if;
    
	return D;
end function;

// This code assumes that X/\Q is a non-hyperelliptic
// curve (genus \ge 3) with Mordell-Weil rank 0.
// X is a projective curve over rationals,
// p prime of good reduction,
// D divisor on X,
// This reduces to a divisor on X/F_p.
NewReduce := function(X, Xp, D);

	if Type(D) eq DivCrvElt then
		decomp := Decomposition(D);
		return &+[pr[2]*$$(X, Xp, pr[1]) : pr in decomp]; // Reduce the problem to reducing places.
	end if;

	Fp := BaseRing(Xp);
	p := Characteristic(Fp);

	Qa := Coordinates(RepresentativePoint(D));
	K := Parent(Qa[1]);
	
	if IsIsomorphic(K, Rationals()) then
		K := RationalsAsNumberField();
	end if;

	OK := RingOfIntegers(K);
	dec := Factorization(p * OK);
	ret := Zero(DivisorGroup(Xp));

	for factor in dec do
		pp := factor[1];                   // A prime above the rational prime p
		assert factor[2] eq 1;

		f := InertiaDegree(pp);            
		Fpp<t> := ResidueClassField(pp); 
		Xpp := ChangeRing(X,Fpp);

		unif := UniformizingElement(pp);   // Use to reduce point modulo p
		m := Minimum([Valuation(K!a, pp) : a in Qa | not a eq 0]);  
		Qared := [unif^(-m)*(K!a) : a in Qa]; 
		Qtaa := Xpp![Evaluate(a,Place(pp)) : a in Qared]; // Reduction of point to Xpp
		Qta := Xp(Fpp) ! Eltseq(Qtaa);      

		ret := ret + 1*Place(Qta);
  	end for;

	return ret;
end function;

//This function computes J_X(F_p) for curve X
JacobianFp := function(X);
	CC, phi, psi := ClassGroup(X); //Algorithm of Hess
	/*Z := FreeAbelianGroup(1);
	degr := hom<CC->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CC)]>;
	JFp := Kernel(degr); // This is isomorphic to J_X(\F_p).*/
	JFp := TorsionSubgroup(CC);
	return JFp, phi, psi;
end function;

// This code assumes that X/\Q is a non-hyperelliptic
// curve (genus \ge 3) with Mordell-Weil rank 0.
// X is a projective curve over rationals,
// p prime of good reduction,
// D divisor on X,
// This reduces to a divisor on X/F_p.
reduce := function(X,Xp,D);
	if Type(D) eq DivCrvElt then
		decomp:=Decomposition(D);
		return &+[ pr[2]*$$(X,Xp,pr[1]) : pr in decomp]; // Reduce the problem to reducing places.
	end if;
	assert Type(D) eq PlcCrvElt;
	if  Degree(D) eq 1 then
		P:=D;
		R<[x]>:=CoordinateRing(AmbientSpace(X));
		n:=Rank(R);
		KX:=FunctionField(X);
		inds:=[i : i in [1..n] | &and[Valuation(KX!(x[j]/x[i]),P) ge 0 : j in [1..n]]];	
		assert #inds ne 0;
		i:=inds[1];
		PP:=[Evaluate(KX!(x[j]/x[i]),P) : j in [1..n]];
		denom:=LCM([Denominator(d) : d in PP]);
		PP:=[Integers()!(denom*d) : d in PP];
		g:=GCD(PP);
		PP:=[d div g : d in PP];
		Fp:=BaseRing(Xp);
		PP:=Xp![Fp!d : d in PP];
		return Place(PP);	
	end if;
	I:=Ideal(D);
	Fp:=BaseRing(Xp);
	p:=Characteristic(Fp);
	B:=Basis(I) cat DefiningEquations(X);
	n:=Rank(CoordinateRing(X));
	assert Rank(CoordinateRing(Xp)) eq n;
	R:=PolynomialRing(Integers(),n);
	BR:=[];
	for f in B do
		g:=f*p^-(Minimum([Valuation(c,p) : c in Coefficients(f)]));
		g:=g*LCM([Denominator(c) : c in Coefficients(g)]);
		Append(~BR,g);
	end for;
	J:=ideal<R | BR>;
	J:=Saturation(J,R!p);
	BR:=Basis(J);
	Rp:=CoordinateRing(AmbientSpace(Xp));
	assert Rank(Rp) eq n;
	BRp:=[Evaluate(f,[Rp.i : i in [1..n]]) : f in BR];
	Jp:=ideal<Rp| BRp>;
	Dp:=Divisor(Xp,Jp);
	return Dp;
end function;

// This function returns the space of relations between a given sequence xs of
// elements in an abelian group A
relations := function(A,xs);
    R := FreeAbelianGroup(#xs);
    f := hom<R -> A | xs>;
    return Kernel(f);
end function;

// This function returns a space containing the space of relations between a
// given sequence of divisors on a curve X defined over Q.
// This is done by reducing the divisors modulo a bunch of primes p,
// finding the relations between the reduced divisors in the Jacobian of X mod p,
// and intersecting the space of relations found for the various primes.
relations_divs := function(X, divs, bp : primes := PrimesUpTo(15), bd := 25);
    fullrelsspace := FreeAbelianGroup(#divs);
	relsspace := fullrelsspace;
    for p in primes do
        try
            Xp := ChangeRing(X,GF(p));
//			bpp := ChangeRing(bp,GF(p));
			bpp := reduce(X,Xp,bp);
			printf "Computing Jacobian of the curve over F_%o\n", p;
            Jfp, phi, psi := JacobianFp(Xp);
			printf "Done computing Jacobian\n";
            divsp := [];
			printf "Trying to reduce divisors modulo %o\n", p;
            for D in divs do
                Append(~divsp,reduce(X,Xp,D));
				printf ".";
            end for;
			printf "Reduced divisors\nCalculating relations between the reduced divisors\n";
			psibpp := psi(bpp);
			divspzero := [psi(D) - Degree(D)*psibpp : D in divsp];
            relsp := relations(Jfp,divspzero);
			printf "Done calculating relations.\n";
        catch e
            Exclude(~primes,p);
            continue;
        end try;
        relsspace := relsspace meet relsp;
		printf "Reducing mod %o has cut down the relation space\n", p;
    end for;
    L := Lattice(#divs,&cat[Eltseq(fullrelsspace ! relsspace.i) : i in [1..#divs]]);
	Lprime, T := LLL(L);
	small_rels := [Eltseq(Lprime.i) : i in [1..#divs] | Norm(Lprime.i) lt bd*#divs];
	return small_rels;
end function;

/*
modformeqns_X0N_X0Nplus := function(Bminus, Bplus, N, prec, jMapProof);
// We first find the equation of X_0(N)plus
    B := Bplus;
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
		Xplus:=Scheme(ProjectiveSpace(R),I);
		if Dimension(Xplus) eq 1 then
			if IsIrreducible(Xplus) then
				Xplus:=Curve(ProjectiveSpace(R),eqns);
				if Genus(Xplus) eq dim then
					tf:=true;
				end if;
			end if;
		end if;
	end while;

// TODO: how does the Hecke-Sturm bound change for X_0(N)plus?
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


    B := Bminus cat Bplus;
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
*/
	//We commented out this part because it is slow and only potentially simplifies the equations
	/*eqns:=GroebnerBasis(ideal<R | eqns>); // Simplifying the equations.
	tf:=true;
	repeat
		t:=#eqns;
		tf:=(eqns[t] in ideal<R | eqns[1..(t-1)]>);
		if tf then 
			Exclude(~eqns,eqns[t]);
		end if;
	until tf eq false;
	t:=0;
	repeat
		t:=t+1;
		tf:=(eqns[t] in ideal<R | Exclude(eqns,eqns[t])>);	
		if tf then
			Exclude(~eqns,eqns[t]);
			t:=0;
		end if;
	until tf eq false and t eq #eqns;*/
/*
	X:=Curve(ProjectiveSpace(R),eqns); // Our model for X_0(N) discovered via the canonical embedding.
	assert Genus(X) eq dim;

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

	if(not IsPrime(N)) then
		DivisorsN := Reverse(Divisors(N));
		
		for i in [2..#DivisorsN] do
			if IsInSmallModularCurveDatabase(DivisorsN[i]) then
				divN := DivisorsN[i];
				break;
			end if;
		end for;
		
		"Using divN: ", divN;
		
		Z:=SmallModularCurve(divN); 
		KZ:=FunctionField(Z);
		qEZ:=qExpansionsOfGenerators(divN,L,prec); // This gives gives qExpansions of the generators
							// of the function field of Z=X_0(n) as Laurent series in q. 
		KX:=FunctionField(X);
		KXgens:=[KX!(R.i/R.dim) : i in [1..(dim-1)]] cat [KX!1]; // The functions x_i/x_dim as elements of the function field of X.
		coords:=[]; // This will contain the generators of the function field of Z as element of the function of X.

		for u in qEZ do
			//We want to express u as an element of the function field of X=X_0(N).
			Su:={};
			d:=0;
			while #Su eq 0 do
				d:=d+1;
				mons:=MonomialsOfDegree(R,d);
				monsq:=[Evaluate(mon,Bexp) : mon in mons];
				V:=VectorSpace(Rationals(),2*#mons);
				W:=VectorSpace(Rationals(),prec-10);
				h:=hom<V->W | 
					[W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]] 
					cat  [ W![Coefficient(-u*monsq[i],j) : j in [1..(prec-10)]  ]  : i in [1..#mons] ]>;
				K:=Kernel(h);
				for a in [1..Dimension(K)] do
					num:=&+[Eltseq(V!K.a)[j]*mons[j] : j in [1..#mons] ];
					denom:=&+[Eltseq(V!K.a)[j+#mons]*mons[j] : j in [1..#mons] ];
					numK:=Evaluate(num,KXgens); 
					denomK:=Evaluate(denom,KXgens);
					if numK ne KX!0 and denomK ne KX!0 then
						Su:=Su join {numK/denomK};
					end if;
				end for;
			end while;
			assert #Su eq 1;
			coords:=coords cat SetToSequence(Su);
		end for;
		phi:=map<X -> Z | coords cat [1]>;
		jd:=Pullback(phi, jFunction(Z, divN));

		CuspPlaces := Poles(jd);
		Cusps := [RepresentativePoint(place) : place in CuspPlaces];
		if(jMapProof) then
			P:=AmbientSpace(X);
			R:=CoordinateRing(P);
			assert Rank(R) eq dim;
			num:=Numerator(FunctionField(P)!jd);
			denom:=Denominator(FunctionField(P)!jd);
			num:=Evaluate(num,[R.i : i in [1..(dim-1)]]);
			denom:=Evaluate(denom,[R.i : i in [1..(dim-1)]]);
			deg:=Max([Degree(num),Degree(denom)]);
			num:=Homogenization(num,R.dim,deg);
			denom:=Homogenization(denom,R.dim,deg);
			assert Evaluate(num,KXgens)/Evaluate(denom,KXgens) eq jd;	
			// We compute the degree of j : X_0(N) --> X(1) using the formula
			// in Diamond and Shurman, pages 106--107.
			assert N gt 2;
			dN:=(1/2)*N^3*&*[Rationals() | 1-1/p^2 : p in PrimeDivisors(N)];
			dN:=Integers()!dN;
			degj:=(2*dN)/(N*EulerPhi(N));
			degj:=Integers()!degj; // Degree j : X_0(N)-->X(1)
			degjd:=&+[-Valuation(jd,P)*Degree(P) : P in CuspPlaces];
			assert degj eq degjd;
			// Now if j \ne jd then the the difference j-jd is a rational
			// function of degree at most 2*degj (think about the poles).
			// Hence to prove that j=jd all we have to check is that their
			// q-Expansions agree up to 2*degj+1.
			jdExpansion:=Evaluate(num,Bexp)/Evaluate(denom,Bexp);
			jdiff:=jdExpansion-jInvariant(q);
			assert Valuation(jdiff) ge 2*degj+1; // We have proven the correctness of the j-map jd on X_0(N)
		end if;
        P:=AmbientSpace(X);
        R:=CoordinateRing(P);
        quotbywN := map<X -> Xplus | [R.i : i in [#Bminus+1..#B]]>;
		return X, Xplus, quotbywN, Cusps;
	end if;
	P:=AmbientSpace(X);
	R:=CoordinateRing(P);
    quotbywN := map<X -> Xplus | [R.i : i in [#Bminus+1..#B]]>;
	P1 := X!([+1] cat [0 : i in [2..#Bminus]] cat [+1] cat [0 : i in [2..#Bplus]]);
	P2 := X!([-1] cat [0 : i in [2..#Bminus]] cat [+1] cat [0 : i in [2..#Bplus]]);
	Cusps := [P1, P2];
	return X, Xplus, quotbywN, Cusps;
end function;
*/

function atkinlehnersubgrp(N,seq);
	boo := true;
	subgrp := seq;
	while boo do
		for a in subgrp do
			for b in subgrp do
				c := ExactQuotient(a*b,GCD(a,b)^2);
				if c ne 1 and not c in subgrp then
					Append(~subgrp,c);
					boo := true;
					break a;
				end if;
			end for;
			boo := false;
		end for;
	end while;
	return Sort(subgrp);
end function;

// This function constructs the following
// X = the curve X_0(N)
// Xplus = the curve X_0(N)^+
// pi = the quotient map
/*
// cusps = Cusps of X_0(N)
*/
// bp = a rational cusp chosen as basepoint of X
// Xplus_pts = a list of small rational points on X_0(N)^+
// divs_sub = a list of linearly independent degree 0 divisors on X generating a finite index subgroup of J_0(N)(Q)
finiteindexsubgrpofJ0N := function(N);
/*
	C := CuspForms(N);
	printf "Dimension of CuspForms(%o) is: %o\n", N, Dimension(C);
	AL := AtkinLehnerOperator(C, N);
	NN := Nullspace(Matrix(AL - 1));
	printf "Dimension of eigenspace lambda = 1 for w_%o is: %o\n", N, Dimension(NN);
	NNc := Nullspace(Matrix(AL + 1));
	printf "Dimension of eigenspace lambda = -1 for w_%o is: %o\n", N, Dimension(NNc);
	BN := [&+[(Integers()!(1*Eltseq(Basis(NN)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NN)]];
	BNc := [&+[(Integers()!(1*Eltseq(Basis(NNc)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NNc)]];
*/

/*
	X, Xplus, pi, cusps := modformeqns_X0N_X0Nplus(BNc, BN, N, 500, true);
	printf "There are %o cusps on X_0(%o)\n", #cusps, N;
	printf "They are:\n%o\n", cusps;
*/
/*
	hypell_X0Nplus := [ 42, 46, 52, 57, 60, 62, 66, 67, 68, 69, 72, 73, 74, 77, 80, 85, 87, 91, 92, 94, 98, 103, 104, 107, 111, 121, 125, 143, 167, 191 ];
	genus1_X0Nplus := [ 22, 28, 30, 33, 34, 37, 38, 40, 43, 44, 45, 48, 51, 53, 54, 55, 56, 61, 63, 64, 65, 75, 79, 81, 83, 89, 95, 101, 119, 131 ];
	genus0_X0Nplus := [ 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 29, 31, 32, 35, 36, 39, 41, 47, 49, 50, 59, 71 ];
// This list is complete for N upto 200
	hypell_X0Nplus := Sort(hypell_X0Nplus cat genus1_X0Nplus);
	if N in genus0_X0Nplus then
		printf "X_0(%o)^+ has genus 0\n", N;
		printf "The curve is in the small modular curve database\n";
		error Error();
	end if;
	if equal_rank(N,N) then
		h := N in hypell_X0Nplus;
		printf "Working with X_0(%o)/w_%o", N, N;
		X, Xplus, pi, wN, ws, BN, BNc := Curve_and_Map(N,N,h);
//		g := Genus(X0NQuotient(N,[N]));
	else
		Halldivs := [d : d in Divisors(N) | GCD(d,ExactQuotient(N,d)) eq 1 and d ne 1];
		good_wds := [d : d in Halldivs | equal_rank(N,d)];
		if #good_wds eq 0 then
			printf "No Atkin-Lehner quotient has Mordell-Weil rank equal to that of X_0(%o)", N;
			error Error();
		else
			d := good_wds[1];
			h := IsHyperelliptic(X0NQuotient(N,[d]));
			printf "Working with X_0(%o)/w_%o", N, d;
			X, Xplus, pi, wN, ws, BN, BNc := Curve_and_Map(N,d,h);
//			g := Genus(X0NQuotient(N,[d]));
		end if;
	end if;

	if h then
		Xplus_pts := Points(Xplus,10000);
	else
		Xplus_pts := PointSearch(Xplus,100);
	end if;
*/
/*
	a, r := LeadingCoefficient(LSeries(JZero(N)),1,100);
*/
	r, boo := rank_J0N_wd(N,1);
	if r ne 0 then
		Halldivs := {d : d in Divisors(N) | GCD(d,ExactQuotient(N,d)) eq 1 and d ne 1};
		seq_als := SetToSequence({atkinlehnersubgrp(N,Sort(SetToSequence(x))) : x in Subsets(Halldivs) | #x gt 0});
		printf "%o\n", seq_als;
		seq_als := [x : x in seq_als | &and[equal_rank(N,y) : y in x]];
		printf "%o\n", seq_als;
		comp := func<a,b|(#a eq #b) select &+b-&+a else #a-#b>;
		seq_als := Sort(seq_als,comp);
		seq_als := [x : x in seq_als | not <N,x> in hyper_data] cat [x : x in seq_als | <N,x> in hyper_data];
		printf "%o\n", seq_als;
	else
		seq_als := [[N]];
	end if;
	for seq in seq_als do
		X, ws, pairs, NB, cusp := eqs_quos(N,[seq]);
		Xquo := pairs[1,1];
		pi := pairs[1,2];
		curvhyp := false;
		if Type(Xquo) eq CrvHyp then
			Xquo_pts := Points(Xquo : Bound := 1000);
			curvhyp := true;
		elif DefiningEquations(Xquo) eq [] then
			Xquo_pts := {@@};
			for a := -10 to 10 do
				for b := -10 to 10 do
					if not (a eq 0 and b eq 0) then
						if GCD(a,b) eq 1 then
							pt := Xquo ! [a,b];
							Include(~Xquo_pts,pt);
						end if;
					end if;
				end for;
			end for;
		else
			Xquo_pts := PointSearch(Xquo,1000);
		end if;
/*
		if #Xquo_pts eq 0 then
			continue;
		end if;
*/
		printf "Found %o small rational points on X_0(%o) quotiented by the Atkin-Lehner involutions corresponding to %o\n", #Xquo_pts, N, seq;
		printf "They are:\n%o\n", Xquo_pts;

		bp_quo := Divisor(pi(cusp));
		bp := Divisor(cusp);
		if r eq 0 then
			return X, seq, Xquo, pi, bp, Xquo_pts, bp_quo, [];
		end if;

		bpquo_pullback := Pullback(pi,bp_quo);
		divsplus := [Divisor(pt) : pt in Xquo_pts];
		divs := [Pullback(pi,D) : D in divsplus];

	/*
		assert exists(bp){c : c in cusps | Type(c) eq Pt};
		bp := Divisor(bp);
		bp_quo := Pushforward(pi,bp);
	*/
		if curvhyp then
			rels := relations_divs(X,divs,bp : primes := PrimesUpTo(20), bd := 100);
		else
			rels := relations_divs(Xquo,divsplus,bp_quo : primes := PrimesUpTo(50), bd := 100);
		end if;
		for r in rels do
			D := &+[r[i]*divsplus[i] : i in [1..#divsplus]] - &+[r[i] : i in [1..#divsplus]]*bp_quo;
			assert IsPrincipal(D);
		end for;
		L := StandardLattice(#divs);
		Lsub := sub<L | rels>;
		Lquot, quot := L / Lsub;

	/*
	TODO: need to change JZero to JZero^+ in this block
		b, tors := TorsionSubgroup(JZero(N));
		assert b;
		n := #AbelianInvariants(tors);
		// a, r := LeadingCoefficient(LSeries(JZero(N)),1,100);
		r, boo := rank_J0N_wd(N,1);
		assert AbelianInvariants(Lquot) eq AbelianInvariants(tors) cat [0 : i in [1..r]];
	*/
		abinvsLquot := AbelianInvariants(Lquot);
		n := Maximum([0] cat [i : i in [1..#abinvsLquot] | abinvsLquot[i] ne 0]);
		Lquot_basis := [Lquot.i @@ quot : i in [n+1..#Generators(Lquot)]];
		divsplus_sub := [&+[v[i]*divsplus[i] : i in [1..#divsplus]] - sumv*bp_quo where sumv is &+[v[i] : i in [1..#divsplus]]: v in Lquot_basis];
		divs_sub := [&+[v[i]*divs[i] : i in [1..#divs]] - sumv*bpquo_pullback where sumv is &+[v[i] : i in [1..#divsplus]] : v in Lquot_basis];
	/*
		return X, Xquo, pi, cusps, bp, Xquo_pts, bp_quo, divs_sub;
	*/
		if #divs_sub eq r then
			return X, seq, Xquo, pi, bp, Xquo_pts, bp_quo, divs_sub;
		end if;
	end for;
/*
	return Sprintf("Not enough rational divisors found which can generate J_0(%o). Found %o, but rank is %o.", N, #divs_sub, r);
*/
	return Sprintf("Not enough rational divisors found which can generate J_0(%o).", N);
end function;

/*
N := 137;
X, Xplus, pi, cusps, bp, Xplus_pts, bp_quo, divsX := finiteindexsubgrpofJ0N(N);
*/
/*
X, Xplus, pi, bp, Xplus_pts, bp_quo, divsX := finiteindexsubgrpofJ0N(N);
*/

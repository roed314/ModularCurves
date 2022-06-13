// The main function in this file is finiteindexsubgrpofJ0N() which takes as input
// a positive number N
// and attempts to compute
// a list of linearly independent degree 0 divisors on X_0(N) generating a finite index subgroup of J_0(N)(Q).
//
// The function works by finding small rational points on some Atkin-Lehner quotient of X_0(N),
// and then pulling them back to get divisors on X_0(N).
//
// So, one hopes this function to work as desired when
// 1. there are sufficiently many small rational points on an Atkin-Lehner quotient, and
// 2. the induced map from the Mordell-Weil group of the Jacobian of the quotient curve to J_0(N)(Q), has finite kernel.


load "new_models.m";
load "rank_calcs.m";

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////
/// JacobianFp /// 
//////////////////

// This function computes Jac(X)(F_q) for a curve X defined over a finite field F_q
// Input: X - a curve defined over F_q
// Output:
// - A finite abelian group A isomorphic to Jac(X)(F_q)
// - a map from A to the group of divisors of X
// - a map from the group of divisors of X to A, which sends a divisor to its divisor class.
JacobianFp := function(X);
	CC, phi, psi := ClassGroup(X); //Algorithm of Hess
	/*Z := FreeAbelianGroup(1);
	degr := hom<CC->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CC)]>;
	JFp := Kernel(degr); // This is isomorphic to J_X(\F_p).*/
	JFp := TorsionSubgroup(CC);
	return JFp, phi, psi;
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////
/// NewReduce /// 
/////////////////

// Input:
// - A projective curve X over Q
// - Basechange of X to F_p for a prime p of good reduction
// - a divisor on X
// Output:
// - The given divisor reduced to X/F_p.
// Note: This code assumes that X/\Q is a non-hyperelliptic curve (genus \ge 3) with Mordell-Weil rank 0.

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

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////
/// reduce /// 
//////////////

// This is an old version of the function NewReduce above.
// Input:
// - A projective curve X over Q
// - Basechange of X to F_p for a prime p of good reduction
// - a divisor on X
// Output:
// - The given divisor reduced to X/F_p.
// Note: This code assumes that X/\Q is a non-hyperelliptic curve (genus \ge 3) with Mordell-Weil rank 0.

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

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////
/// relations /// 
/////////////////

// This function returns the space of relations between a given sequence xs of
// elements in an abelian group A
// Input: An abelian group A, a list xs of elements of A
// Output: The space of relations between the given elements in A, as a subspace of Z^(#xs).

relations := function(A,xs);
    R := FreeAbelianGroup(#xs);
    f := hom<R -> A | xs>;
    return Kernel(f);
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////////
/// relations_divs /// 
//////////////////////

// This function returns a space containing the space of relations between a
// given sequence of divisors on a curve X defined over Q.
// This is done by reducing the divisors modulo a bunch of primes p,
// finding the relations between the reduced divisors in Jac(X_p)(F_p),
// and intersecting the space of relations found for the various primes.

// Input:
// - A curve X defined over Q
// - A list of divisors of X, (not necessarily of degree 0)
// - A rational base point of X
// - (optional) list of primes to work with
// - (optional) a bound for deciding between small height relations (which most likely come from Q),
// and large height relations (which exist only over the various finite fields F_p for the primes tried).
// Output:
// - a list consisting of the relations found between the degree zero divisors D-deg(D)*bp
// Note: The relations outputted are checked to be correct using IsPrincipal().
// Note: But, the space spanned by the output could be strictly smaller than the actual space of relations.

relations_divs := function(X, divs, bp : primes := PrimesUpTo(30), bd := 1000);
    fullrelsspace := FreeAbelianGroup(#divs);
	relsspace := fullrelsspace;
    for p in primes do
        try
            Xp := ChangeRing(X,GF(p));
//			bpp := ChangeRing(bp,GF(p));
			bpp := NewReduce(X,Xp,bp);
			printf "Computing Jacobian of the curve over F_%o\n", p;
            Jfp, phi, psi := JacobianFp(Xp);
			printf "Done computing Jacobian\n";
            divsp := [];
			printf "Trying to reduce divisors modulo %o\n", p;
            for D in divs do
                Append(~divsp,NewReduce(X,Xp,D));
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
	for r in small_rels do
		D := &+[r[i]*divs[i] : i in [1..#divs]] - &+[r[i] : i in [1..#divs]]*bp;
		if not IsPrincipal(D) then
			Exclude(~small_rels,r);
		end if;
	end for;
	return small_rels;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////////////
/// atkinlehnersubgrp /// 
/////////////////////////

// Input: The level N, and a list of Hall divisors of N representing the corresponding Atkin-Lehner involutions.
// Output: The list of all (non-trivial) Hall divisors of N corresponding to all the Atkin-Lehner involutions in the subgroup generated.

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


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////////////////
/// finiteindexsubgrpofJ0N /// 
//////////////////////////////

// This function attempts to compute a list of linearly independent degree 0 divisors on X_0(N)
// generating a finite index subgroup of J_0(N)(Q).

// Input: The level N
// Output:
// - the curve X_0(N)
// - a list of Hall divisors of N corresponding to a subgroup of Atkin-Lehner involutions, so that
// the Mordell-Weil rank of the Jacobian of the quotient curve is equal to that of J_0(N)
// - the quotient curve
// - the quotient map
// - the divisor of a rational cusp chosen as basepoint of X_0(N)
// - a list of small rational points on the quotient curve
// - the divisor of the image of the rational cusp on the quotient curve
// - a list of (potentially linearly independent) degree 0 divisors on X_0(N) generating a finite index subgroup of J_0(N)(Q)
//
// If the algorithm fails to find such a list of degree 0 divisors on X_0(N), it returns a string with the message
// "Not enough rational divisors found which can generate J_0(N)."

finiteindexsubgrpofJ0N := function(N);
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
			Xquo_pts := PointSearch(Xquo,100);
		end if;
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

		if curvhyp then
			rels := relations_divs(X,divs,bp : primes := PrimesUpTo(40), bd := 1000);
		else
			rels := relations_divs(Xquo,divsplus,bp_quo : primes := PrimesUpTo(40), bd := 1000);
		end if;
		L := StandardLattice(#divs);
		Lsub := sub<L | rels>;
		Lquot, quot := L / Lsub;

		abinvsLquot := AbelianInvariants(Lquot);
		n := Maximum([0] cat [i : i in [1..#abinvsLquot] | abinvsLquot[i] ne 0]);
		Lquot_basis := [Lquot.i @@ quot : i in [n+1..#Generators(Lquot)]];
		divsplus_sub := [&+[v[i]*divsplus[i] : i in [1..#divsplus]] - sumv*bp_quo where sumv is &+[v[i] : i in [1..#divsplus]]: v in Lquot_basis];
		divs_sub := [&+[v[i]*divs[i] : i in [1..#divs]] - sumv*bpquo_pullback where sumv is &+[v[i] : i in [1..#divsplus]] : v in Lquot_basis];
		if #divs_sub eq r then
			return X, seq, Xquo, pi, bp, Xquo_pts, bp_quo, divs_sub;
		end if;
	end for;
	return Sprintf("Not enough rational divisors found which can generate J_0(%o).", N);
end function;

/*
N := 137;
X, seq, Xquo, pi, bp, Xquo_pts, bp_quo, divsX := finiteindexsubgrpofJ0N(N);
*/

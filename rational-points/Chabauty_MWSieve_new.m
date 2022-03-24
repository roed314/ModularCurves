load "ChabautyHelp.m";

//D is an element of an abstract group iso. to JFp which we want to map to divisor class
//JFpGenerators are generators of JFp - Jacobian modulo p
//PhiActionTable is the value of phi() on generators

//example how I checked that this works as intended:
//table := [Decomposition(phi(g)) : g in OrderedGenerators(JFp)];
//assert BetterPhi(z + k, OrderedGenerators(JFp), table, JFp) eq phi(z + k);

//not used in code yet because we might want to discuss it first
//testing showed significant speed gains for X0(137)

BetterPhi := function(D, JFpGenerators, PhiActionTable, JFp)
	rep := Representation(JFpGenerators, D);
		
	for j in [1..#JFpGenerators] do
		for i in [1..#PhiActionTable[j]] do
			PhiActionTable[j][i][2] := PhiActionTable[j][i][2] * (rep[j] mod Order(JFp.j));
		end for;
	end for;

	divNew := &+[Divisor(PhiActionTable[j]) : j in [1..#JFpGenerators]];

	return divNew;
end function;

// Called by MWSieve, performs step for p_i described in the article

ChabautyInfo := function(X, AtkinLehner, genusC, p, A, divs, Dpull, B, iA, W, deg2)
	//first get J(X_p)
	Fp := GF(p);
	Xp := ChangeRing(X,Fp);

	//We reduce the divisors and the basepoint
	JFp, phi, psi := JacobianFp(Xp);
	divsp := [reduce(X, Xp, divi) : divi in divs];
	Dpull_p := reduce(X, Xp, Dpull); 

	//The map A -> J_X(\F_p).
	h := hom<A -> JFp | [(JFp!psi(divp)) : divp in divsp]>;

	//reduce known degree 2 divisors
	deg2p := [1*reduce(X, Xp, DDD) : DDD in deg2];
	deg2p2 := [psi(DD - Dpull_p) : DD in deg2p];

	//We now split our cosets represented by elements of W
	//into smaller cosets on which h takes a single value.
	Bp, iAp := sub<A | Kernel(h)>;
	newB, newiA := sub<A | iA(B) meet iAp(Bp)>; 
	AmodnewB, pi1 := quo< A | newiA(newB)>;
	AmodB, pi2 := quo<AmodnewB | pi1(iA(B))>;
	W := [(x + w)@@pi1 : x in Kernel(pi2), w in pi1(W)]; 
	B := newB;
	iA := newiA;

	//we use that h(W) must be subset of Image(mI)
	mI:=hom<JFp -> JFp | [JFp!psi(OneMinusWmodp(Xp, phi(g), AtkinLehner, p)) : g in OrderedGenerators(JFp)]>;
	imW := {@ h(x) : x in W | h(x) in Image(mI) @}; 
	K := Kernel(mI);
	jposP := [];

	//For each z such that (1 - w)*z = x, we check whether z can come from a rational point on X^(2).
	//We try to eliminate z as described in the article.
	//If we can't eliminate at least one z such that (1 - w)*z = x, we keep x.
	printf "out of %o: ", #imW;
	gensJFp := OrderedGenerators(JFp);
	table := [Decomposition(phi(g)) : g in gensJFp];
	for x in imW do
		printf ".";
    		z := x@@mI;
    		if &or[Dimension(phi(z + k) + Dpull_p) gt 0 and (not z + k in deg2p2 or not IsLonely(deg2[Index(deg2p2, z + k)], p, X, AtkinLehner, genusC)) : k in K] then
			//if &or[Dimension(BetterPhi(z + k, gensJFp, table, JFp) + Dpull_p) gt 0
					 //and (not z + k in deg2p2 or not IsLonely(deg2[Index(deg2p2, z + k)], p, X, AtkinLehner, genusC)) : k in K] then
				Append(~jposP, x);
    		end if;
	end for;

	//We keep those x in W which we were unable to eliminate
	W := [x : x in W | h(x) in jposP]; 
	return W, B, iA; 
end function;


// INPUT:
// model 'X' for projective curve X/\Q;
// set 'deg2' of degree 2 divisors on X (known points on X^(2)(\Q));
// matrix 'AtkinLehner' defining Atkin-Lehner operator on X such that C = X/<AtkinLehner>, rk(J(C)(\Q))=rk(J(X)(\Q));
// set 'divs' of degree 0 divisors that generate a subgroup G \subset J(X)(\Q), such that (1-w)(J(X)(\Q)) <= G;
// abstract abelian group 'A' isomorphic to G such that A.i corresponds to divs[i];
// number 'genusC' that is the genus of C;
// a degree 2 divisor 'Dpull' on X that is the pullback of a rational point on C, to be used to embed X^{(2)} in J;
// subgroup 'B0' <= A, inclusion 'iA0': A -> B0, set 'W0' of B0-coset representatives such that B0 + W0 = A.

MWSieve := function(X, AtkinLehner, genusC, primes, A, divs, Dpull, B0, iA0, W0, deg2)
	B := B0;
	iA := iA0;
	W := W0;
	
	// Together, B+W \subset A consists of the possible images of unknown (rational)
	// points in A. The map X^(2)(\Q) \to A is composition of X^(2)(\Q) \to J(X)(\Q) and
	// multiplication by (1-Atkinlehner) such that (1-Atkinlehner)*J(X)(\Q) \subset A.
	
	for i -> p in primes do
		printf "p = %o (%o/%o): ", p, i, #primes;
		W, B, iA := ChabautyInfo(X, AtkinLehner, genusC, p, A, divs, Dpull, B, iA, W, deg2);

		// We get B<=A and W a set of B-coset representatives such that
		// hypothetical unknown points map to one of those cosets

		printf "The number of possible cosets unknown points can land in is %o.\n", #W;

		if W eq [] then
			return true;
		end if;
		
		//this is actually our goal
		if #W eq 1 and IsIdentity(W[1]) then
			return B, iA, W;
		end if;


	end for;
	return B, iA, W;
end function;

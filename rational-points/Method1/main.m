SetLogFile("main.log");
load "X0p_NiceModel.m";
load "new_models.m";
load "auxiliary.m";
load "Chabauty_MWSieve_new.m";
load "rank_calcs.m";

ProvablyComputeQuadPts_X0N := function(N : d:=N)
	printf "Genus of X_0(%o) is: %o\n", N, Dimension(CuspForms(N));
	printf "d is %o\n", d;
	//  Check rk J_0(N)(Q) = rk J_0(N)^+(Q)
	if d eq N then
		if not IsRankOfALQuotEqual(N) then
			error "One needs rk J_0(N)(Q) = rk J_0(N)^+(Q) for our algorithm to work.";
		else
			printf "rk J_0(N)(Q) = rk J_0(N)^+(Q).\n";
		end if;
	else
		if rank_quo(N, [d]) ne rank_quo(N, []) then
			error "One needs rk J_0(N)(Q) = rk J_0(N)(Q)/w_d for our algorithm to work.";
		else
			printf "rk J_0(%o)(Q) = rk J_0(%o)(Q)/w_%o \n", N, N, d;
		end if;
	end if;

	XN, ws, _, _, cuspInf := eqs_quos(N, []);

	if IsSquarefree(N) then
		XN_Cusps := compute_cusps(XN, N, ws, cuspInf, []);
	else
		jMap, numDenom := jmap(XN, N);
		XN_Cusps := compute_cusps(XN, N, ws, cuspInf, numDenom);
	end if;

	printf "Nice model for X_0(%o) is: %o\n\n", N, XN;

	//wN := ws[#ws]; //this is because ALs are returned in ascending index
	ListOfDivs := Divisors(N);
	for i:=1 to #ListOfDivs do
		if ListOfDivs[i] eq d then wN := ws[i-1]; break;
		end if;
	end for;
	printf "w_%o on X_0(%o) is given by: %o\n", N, N, wN;

	printf "Genus of X_0(%o) is %o\n", N, Genus(XN);
	printf "We have found these points on X_0(%o):\n%o\n", N, XN_Cusps;

	gens := [Divisor(c1) - Divisor(c2) : c1,c2 in XN_Cusps | c1 ne c2];

	//known degree 1 places
	pls1 := [XN_Cusps[i] : i in [1..#XN_Cusps] | Degree(XN_Cusps[i]) eq 1];

	//known degree 2 rational effective divisors
	deg2 := [1*XN_Cusps[i] : i in [1..#XN_Cusps] | Degree(XN_Cusps[i]) eq 2];
	deg2pb := [];

	for i in [1..#pls1] do
		for j in [i..#pls1] do
			Append(~deg2, 1*pls1[i] + 1*pls1[j]);
			
			if wN(RepresentativePoint(pls1[i])) eq RepresentativePoint(pls1[j]) then
				Append(~deg2pb, 1*pls1[i] + 1*pls1[j]);
			end if;

		end for;
	end for;

	printf "We have found %o points on X_0(%o)^2(Q).\n", #deg2, N;

	//Finally, we do the sieve.

	A, divs := GetTorsion(N, XN, XN_Cusps);
	genusC := genus_quo(N, [d]);
	bp := deg2pb[1];
	wNMatrix := Matrix(wN);

	primes := []; // TODO: find suitable primes

	for p in PrimesInInterval(3, 10) do
		if N mod p ne 0 then
			Append(~primes, p);
		end if;
	end for;


	B0, iA0 := sub<A | Generators(A)>;
	W0 := {0*A.1};

	B, iA, W := MWSieve(XN, wNMatrix, genusC, primes, A, divs, bp, B0, iA0, W0, deg2);

	printf "\nFor unknown Q in X_0(%o)^2(\Q) we have (1 - w_%o)[Q - bp] is in a coset of %o represented by an element of %o.\n", N, N, B, W;

	if #W eq 1 and IsIdentity(W[1]) then
		printf "It follows that if there is an unknown Q in X_0(%o)^2(\Q), then (1 - w_%o)[Q - bp] == 0.\n", N, N;
		printf "This implies that [Q - bp] is fixed by w_%o\n", N;
		printf "Then Q ~ w_%o(Q), which implies that Q = w_%o(Q) because X_0(%o) is not hyperelliptic.\n", N, N, N;
		printf "Then either Q is a pullback, or it is fixed by w_%o pointwise.\n", N;
		printf "If P = (X_i) is fixed by w_%o,\n", N;
		printf "either the first %o coordinates are 0 or the last %o coordinates are 0\n\n", genusC, Dimension(CuspForms(N)) - genusC;

		I := IdentityMatrix(Rationals(), Genus(XN));
		CR<[x]> := CoordinateRing(AmbientSpace(XN));

		// all coordinates where there is a -1 in w_N must be 0 for a point fixed by w_N
		J1 := &+[ideal<CR | &+[v[i]*x[i] : i in [1..Genus(XN)]]> : v in Basis(Kernel(wNMatrix + I))];
		J2 := &+[ideal<CR | &+[v[i]*x[i] : i in [1..Genus(XN)]]> : v in Basis(Kernel(wNMatrix - I))];

		Z1 := Scheme(XN, J1);
		Z2 := Scheme(XN, J2);
		Z := Union(Z1, Z2);
		printf "We find all such P by imposing these conditions and finding points on the scheme:\n%o\n\n", Z;

		pts := PointsOverSplittingField(Z);
		printf "All such P are:\n%o\n", pts;

		pts_of_deg_le_2 := [P : P in pts | forall{i : i in [1..Dimension(AmbientSpace(Z))] | Degree(MinimalPolynomial(P[i])) le 2}];
		ptsclstr := [Cluster(Z, P) : P in pts_of_deg_le_2];
		degrees := [Degree(P) : P in ptsclstr];
		printf "The degrees of these points are %o (or > 2).\n", degrees;

		if forall{deg: deg in degrees | deg ne 2} then
			printf "Hence there are no quadratic points on X_0(%o) not coming from pullbacks of rationals.\n", N;
		else
			error "TODO: Sieve worked, but we still need to analyze quadratic points (there are some).";
		end if;

		else 
			error "TODO: Sieve did not prove what we wanted.";
	end if;

	return "done";
end function;

//ProvablyComputeQuadPts_X0N(101);
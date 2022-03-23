SetLogFile("main.log");
load "Progs/quadPts.m";
load "X0p_NiceModel.m";
load "Chabauty_MWSieve_new.m";
SetDebugOnError(true);

//we find models for X_0(N) and X_0(N)/w_N

N := 91;

C := CuspForms(N);
printf "Dimension of CuspForms(%o) is: %o\n", N, Dimension(C);

// TODO: Check rk(J(Q)) = rk(J^{w_N}(Q))

ALN := AtkinLehnerOperator(C, N);
NN := Nullspace(Matrix(ALN - 1));

printf "Dimension of eigenspace lambda = +1 for w_%o is: %o\n", N, Dimension(NN);

NNc := Nullspace(Matrix(ALN + 1));

printf "Dimension of eigenspace lambda = -1 for w_%o is: %o\n", N, Dimension(NNc);

BN  := [&+[(Integers()!(2*Eltseq(Basis(NN )[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NN)]];
BNc := [&+[(Integers()!(2*Eltseq(Basis(NNc)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NNc)]];

XN, XN_Cusps := modformeqns(BNc cat BN, N, 500, false);
printf "Nice model for X_0(%o) is: %o\n\n", N, XN;
RR<[u]> := CoordinateRing(AmbientSpace(XN));
n := Dimension(AmbientSpace(XN));

H := DiagonalMatrix(RationalField(), Dimension(C), [+1 : i in [1..Dimension(NNc)]] cat [-1 : i in [1..Dimension(NN)]]);
rows := [[&+[RowSequence(H)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]]];
wN := iso<XN -> XN | rows, rows>;
printf "w_%o on X%o is given by: %o\n", N, N, wN;

printf "Genus of X_0(%o) is %o\n", N, Genus(XN);
printf "Genus of X_0(%o)/w_%o is %o\n", N, N, Dimension(NN);

printf "We have found these points on X_0(%o):\n%o\n", N, XN_Cusps;
 
//Dtor := Divisor(XN_Cusps[1]) - Divisor(XN_Cusps[2]);

//not needed for prime values of N, torsion is then known
//for non-prime N, we will need different method of getting torsion
p := 3;
while IsDivisibleBy(N, p) do
	p := NextPrime(p);
end while;
// compute the cuspidal torsion subgroup (= J(Q)_tors assuming the generalized Ogg conjecture)
h, Ksub, bas, divsNew := findGenerators(XN, [Place(cusp) : cusp in XN_Cusps], Place(XN_Cusps[1]), p);
// Ksub == abstract group isomorphic to cuspidal
// "It also returns a subset divsNew such that [[D-deg(D) P_0] : D in divsNew] generates the same subgroup."

/*order := 1;
nDtor := Dtor;
repeat
    nDtor +:= Dtor;
    b, ff := IsPrincipal(nDtor);
    order +:= 1;
until b;
printf "order of P1 - P2: %o\n", order;
//printf "equals the order of J_0(%o)_tors: %o\n", N, nDtor eq TorsionBound(Jacobian(XN), 200);
//printf "Is Dtor := XN_Cusps[1] - XN_Cusps[2] a generator for J_0(%o)(Q)_tors?\n", N; //, b and not(IsPrincipal(5*Dtor)) and not(IsPrincipal(13*Dtor));
*/

//known degree 1 places
pls1 := [Place(XN_Cusps[i]) : i in [1..#XN_Cusps]];

//known degree 2 places, we conjecture all are pullbacks
pls2:=[];

deg2:=[];
deg2pb:=[];

for i in [1..#pls1] do
	for j in [i..#pls1] do
		deg2 := Append(deg2, 1*pls1[i] + 1*pls1[j]);
		if wN(RepresentativePoint(pls1[i])) eq RepresentativePoint(pls1[j]) then
			deg2pb := Append(deg2pb, 1*pls1[i] + 1*pls1[j]);
		end if;
	end for;
end for;

printf "We have found %o points on X_0(%o)^2(Q).\n", #deg2, N;
printf "%o of them are pullbacks of rationals from X_0(%o)/w_%o.\n", #deg2pb, N, N;

//Finally, we do the sieve.
//A := AbelianGroup([order]);
A := Ksub;
//divs := [Dtor];
D := [Divisor(divsNew[i]) - Divisor(XN_Cusps[1]) : i in [1..#divsNew]];
divs := [&+[coeffs[i] * D[i] : i in [1..#coeffs]] : coeffs in bas];
genusC := Dimension(NN);
bp := deg2pb[1];
wNMatrix := Matrix(wN);

primes := [3, 5, 7, 11]; // TODO: find suitable primes
B0, iA0 := sub<A | Generators(A)>;
W0 := {0*A.1};

B, iA, W := MWSieve(XN, wNMatrix, genusC, primes, A, divs, bp, B0, iA0, W0, deg2); // 
//MWSieve(XN, wNMatrix, genusC, primes, A, divs, I, bp, B0, iA0, W0, deg2); // I is a number

printf "\nFor unknown Q in X_0(%o)^2(\Q) we have (1 - w_%o)[Q - bp] is in a coset of %o represented by an element of %o.\n", N, N, B, W;
if #W eq 1 and IsIdentity(W[1]) then
	printf "It follows that if there is an unknown Q in X_0(%o)^2(\Q), then (1 - w_%o)[Q - bp] == 0.\n", N, N;
	printf "This implies that [Q - bp] is fixed by w_%o\n", N;
	printf "Then Q ~ w_%o(Q), which implies that Q = w_%o(Q) because X_0(%o) is not hyperelliptic.\n", N, N, N;
	printf "Then either Q is a pullback, or it is fixed by w_%o pointwise.\n", N;
	printf "If P = (X_i) is fixed by w_%o,\n", N;
	printf "either the first %o coordinates are 0 or the last %o coordinates are 0\n\n", Dimension(NN), Dimension(NNc);

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
		error "TODO";
	end if;
else 
	error "TODO";
end if;

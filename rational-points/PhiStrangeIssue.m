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


JacobianFp := function(X)
	CC, phi, psi := ClassGroup(X); //Algorithm of Hess
	Z := FreeAbelianGroup(1);
	degr := hom<CC->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CC)]>;
	JFp := Kernel(degr); // This is isomorphic to J_X(\F_p).
	return JFp, phi, psi;
end function;

//B is a basis for Cuspforms(N)
//N is N for which we want the model for X0(N)
//divN is a divisor of N, used only for jMap, divN = 1 is allowed

modformeqns := function(B, N, prec)
dim := #B;
L<q> := LaurentSeriesRing(Rationals(),prec);
R<[x]> := PolynomialRing(Rationals(),dim);
Bexp := [L!qExpansion(B[i],prec) : i in [1..dim]];
eqns := [R | ];
	d := 1;
	tf := false;
	while tf eq false do
		d := d + 1;
		mons := MonomialsOfDegree(R, d);
		monsq := [Evaluate(mon, Bexp) : mon in mons];
		V := VectorSpace(Rationals(), #mons);
		W := VectorSpace(Rationals(), prec - 10);
		h := hom<V->W | [W![Coefficient(monsq[i], j) : j in [1..(prec - 10)]] : i in [1..#mons]]>;
		K := Kernel(h);
		eqns := eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
        	I := Radical(ideal<R | eqns>);
		X := Scheme(ProjectiveSpace(R), I);
		if Dimension(X) eq 1 then
			if IsIrreducible(X) then
				X := Curve(ProjectiveSpace(R), eqns);
				if Genus(X) eq dim then
					tf := true;
				end if;
			end if;
		end if;
	end while;

	X := Curve(ProjectiveSpace(R),eqns); // Our model for X_0(N) discovered via the canonical embedding.
	assert Genus(X) eq dim;
    	indexGam := N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];	
	indexGam := Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)

	for eqn in eqns do
		eqnScaled := LCM([Denominator(c) : c in Coefficients(eqn)])*eqn;
		wt := 2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke := Ceiling(indexGam*wt/12);  // Hecke=Sturm bound.
						 // See Stein's book, Thm 9.18.
		Bexp1 := [qExpansion(B[i], hecke + 10) : i in [1..dim]]; // q-expansions
                        					    // of basis for S 
                        					    // up to precision hecke+10.
		assert Valuation(Evaluate(eqnScaled,Bexp1)) gt hecke + 1;
	end for; // We have now checked the correctness of the equations for X.

	return X;
end function;

//we find models for X137 and X137/w137

C := CuspForms(137);
"Dimension of CuspForms(137) is: ", Dimension(C);

AL137 := AtkinLehnerOperator(C, 137);
N137 := Nullspace(Matrix(AL137 - 1));

"Dimesion of eigenspace lambda = 1 for w137 is: ", Dimension(N137);

N137c := Nullspace(Matrix(AL137 + 1));

"Dimesion of eigenspace lambda = -1 for w137 is: ", Dimension(N137c);
"";

B137 := [&+[(Integers()!(1*Eltseq(Basis(N137)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(N137)]];
B137c := [&+[(Integers()!(1*Eltseq(Basis(N137c)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(N137c)]];

X137 := modformeqns(B137c cat B137, 137, 500);
"Nice model for X0(137) is:";
X137;
"";


X := X137;
p := 3;
Fp := GF(p);
Xp := ChangeRing(X,Fp);

JFp, phi, psi := JacobianFp(Xp);
table := [Decomposition(phi(g)) : g in OrderedGenerators(JFp)];
gens := OrderedGenerators(JFp);

iters := 0;
ordinary := [];
fast := [];

for elem in JFp do
	ordinary := Append(ordinary, phi(elem));
	iters := iters + 1;
	"Slow phi element ", iters;
	if iters eq 100 then
		break;
	end if;
end for;

iters := 0;
for elem in JFp do
	fast := Append(fast, BetterPhi(elem, gens, table, JFp));
	iters := iters + 1;
	"Fast phi element ", iters;
	if iters eq 100 then
		break;
	end if;
end for;

for i in [1..10] do
	"Are slow and fast results on index ", i, " equal? ", ordinary[i] eq fast[i];
end for;

for i in [1..100] do
	"Dimension of RR space with ordinary phi, index ", i, ": ", Dimension(ordinary[i]);
end for;

for i in [1..100] do
	"Dimension of RR space with fast BetterPhi, index ", i, ": ", Dimension(fast[i]);
end for;

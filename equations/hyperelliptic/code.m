function GetModularCurveGenerators(label)
	N, gens := GetLevelAndGensFromLabel(label);
	Mat := MatrixRing(Integers(N),2);
	return [Mat!elt : elt in gens];

	/* for elt in getrecs("~/projects/ModularCurves/equations/modular_curves_data.txt":Delimiter:="|") do
		if elt[2] eq label then
			N := StringToInteger(elt[3]);
			gen_str := elt[4];
			gen_str := ReplaceCharacter(gen_str, "{", "[");
			gen_str := ReplaceCharacter(gen_str, "}", "]");
			gen_list := eval gen_str;
			Mat := MatrixRing(Integers(N),2);
			return [Mat!elt : elt in gen_list];
		end if;
	end for;
	return false; */
end function;


function toConic(X)
	// Testing function to convert a rational normal curve to a conic.
	// It is far too slow to run in projective spaces of dimension > 6.
	// Input: A rational normal curve.
	// Output: An isomorphic plane conic.

	assert IsCurve(X);
	D := CanonicalDivisor(X);
	phi := DivisorMap(-D);
	con := Conic(Image(phi));
	return con;
end function;

function PadList(L, n)
	return L cat [0 : i in [#L+1..n]];
end function;

function AbsEltseqPad(elt , prec)
	if Type(AbsolutePrecision(elt)) eq Infty then
		_<t> := Parent(elt);
		print elt;
		elt +:= O(t^prec);
		assert Type(AbsolutePrecision(elt)) ne Infty;
	end if;
	coeffs := AbsEltseq(elt);
	if #coeffs gt prec then
		return coeffs[1..prec];
	else
		return coeffs cat [0 : _ in [#coeffs + 1 .. prec]];
	end if;
end function;


function MatrixAbsEltseq(list)
	prec := Min([AbsolutePrecision(elt) : elt in list]);
	return Matrix([AbsEltseqPad(f, prec) : f in list]);
end function;

function tCheck(BT, t)
	// this checks the Poonen property
	i := #BT;
	b := BT[i];
	while i gt 1 do
		i -:= 1;
		b /:= t;
		assert IsWeaklyZero(BT[i] - b);
	end while;
	return true;
end function;

function Poonenate(BT, t)
	// Create a Poonen basis
	K := BaseRing(Parent(t));
	newBT := BT;
	i := #BT;
	b := BT[i];
	M := IdentityMatrix(K, i);
	while i gt 1 do
		i -:= 1;
		b /:= t;
		N := MatrixAbsEltseq(Append(BT, b));
		K := Kernel(N);
		assert Dimension(K) eq 1;
		v := Basis(K)[1];
		for j in [1..#BT] do
			M[i][j] := v[j];
		end for;
		newBT[i] := b;
	end while;
	assert tCheck(newBT, t);
	return newBT, M;
end function;


function FindPolynomial(Mons, qExps)
	// Given a list of monomials M in #qExps variables, find the unique linear combination that vanishes.
	_<qN> := Parent(qExps[1]);
	Vals := [Evaluate(f, qExps) : f in Mons];
	d := Min([AbsolutePrecision(f) : f in Vals]);
	v := Min([Degree(LeadingTerm(f)) : f in Vals] cat [0]);
	M := Matrix([PadList(AbsEltseq(qN^(-v)*f + O(qN^(d-v))), d-v)[[1..d-v]] : f in Vals]);
	K := Kernel(M);
	assert Dimension(K) eq 1;
	B := Basis(K)[1];
	R := BaseRing(Parent(Mons[1]));
	return &+[(R!B[i])*Mons[i] : i in [1..#Mons]];
end function;


//intrinsic HyperellipticModel(SeqEnum[RngSerPowElt]) -> Crv
function HyperellipticModel(B)
	prec := Min([AbsolutePrecision(elt) : elt in B ]);
	g := #B;
	_<qN> := Parent(B[1]);
	K := BaseRing(Parent(B[1]));

	// Compute a triangular basis and check that it satisfies the Poonen property.
	_, T := EchelonForm(MatrixAbsEltseq(B));
	BT := [&+[T[j][i]*B[i] : i in [1..g]] : j in [1..g]];
	t := BT[g] / BT[g-1];
	BT, T2 := Poonenate(BT, t);
	T := T2*T;
	T_inv := T^(-1);

	// Construct the pull back of the canonical divisor on the conic to the P1 over K.
	P1 := Curve(ProjectiveSpace(K, 1));
	FF<t1> := FunctionField(P1);
	f0 := &+[T_inv[1][i]*t1^(i-1) : i in [1..g]];
	f1 := &+[T_inv[2][i]*t1^(i-1) : i in [1..g]];
	f := f0 / f1;
	CanDiv := Divisor(Differential(f));
	RR := Basis(-CanDiv);
	//den := FF!&*[Denominator(elt) : elt in RR];
	//RR := [den*elt : elt in RR];
	PreImagR := PreimageRing(Parent(Numerator(RR[1])));
	RK<y> := PolynomialRing(K);
	nu := hom< PreImagR -> RK | [y] >;

	function ApplyGalois(f, rho)
		f := nu(f);
		return RK![rho(c) : c in Coefficients(f)];
	end function;

	// Compute a rational basis for the Riemann-Roch space
	Coeffs := [ [K.1^a, 0, 0] : a in [0..Degree(K)-1]] cat [ [0, K.1^a, 0] : a in [0..Degree(K)-1]] cat [ [0, 0, K.1^a] : a in [0..Degree(K)-1]];
	A := [ Parent(1/qN) | 0 : i in [1..#Coeffs]];
	for foobar->rho in Automorphisms(K) do
		g0 := &+[rho(T[g-1][i])*B[i] : i in [1..g]];
		g1 := &+[rho(T[g][i])*B[i] : i in [1..g]];
		rhot := g1 / g0;
		//print foobar, [Evaluate(ApplyGalois(Numerator(rj), rho), rhot) / Evaluate(ApplyGalois(Denominator(rj), rho), rhot) : j->rj in RR];
		for i in [1..#Coeffs] do
			A[i] +:= &+[ rho(Coeffs[i][j]) * Evaluate(ApplyGalois(Numerator(rj), rho), rhot) / Evaluate(ApplyGalois(Denominator(rj), rho), rhot) : j->rj in RR ];
		end for;
	end for;
	//print [Degree(LeadingTerm(elt)) : elt in A | not IsWeaklyZero(elt)];
	order := Min([0] cat [Degree(LeadingTerm(elt)) : elt in A | not IsWeaklyZero(elt)]);
	Aorig := A;
	A := [Parent(B[1]) ! Parent(B[1])!(qN^-order * elt) : elt in Aorig];
	MA := MatrixAbsEltseq(A);
	//print [PivotColumn(E, j) : j->_ in Rows(E)] where E :=EchelonForm(MA);
	assert Rank(MA) eq 3;
	A := [A[PivotColumn(otherT, i)] : i in [1..3]] where otherT := EchelonForm(Transpose(MA)); // extracting pivot rows
	assert Rank(MatrixAbsEltseq(A)) eq 3;


	// Use linear algebra to find the conic defined by these traces.
	P2 := ProjectivePlane(Rationals());
	R3<a,b,c> := CoordinateRing(P2);
	M3 := MonomialsOfDegree(R3, 2);
	q := FindPolynomial(M3, A);

	// Simplify the conic and keep track of the q-expansions used to define this conic.
	C := Curve(P2, q);
	_, D := IsConic(C);
	MC, phi_min := MinimalModel(D);
	eq_phi_min := DefiningEquations(Inverse(phi_min));
	foo := [0,0]; // hacky way to pad the output of coefficients
	Amin := [ A[1]*K!(Coefficients(E, a) cat foo)[2] + A[2]*K!(Coefficients(E, b) cat foo)[2] + A[3]*K!(Coefficients(E, c) cat foo)[2] : E in eq_phi_min ];
	assert IsWeaklyZero(Evaluate(Equation(MC), Amin));
	//print "Conic over Q:", Equation(MC);

	// Find rational function expressing b/a in terms of t
	R3<x3, y3, z3> := PolynomialRing(K, 3);
	R2<xK, yK> := PolynomialRing(K, 2);
	Rf<zK> := PolynomialRing(K);
	Pols := [1, yK, yK^2, xK, xK*yK, xK*yK^2];
	Pol_bt := FindPolynomial(Pols, [Amin[2]/Amin[1], t]);
	Pol_ct := FindPolynomial(Pols, [Amin[3]/Amin[1], t]);
	aa_t := LCM(Evaluate(Coefficients(Pol_bt, xK)[2], [0, zK]), Evaluate(Coefficients(Pol_ct, xK)[2], [0, zK]));
	ba_t := - aa_t*Evaluate(Coefficients(Pol_bt, xK)[1], [0, zK]) / Evaluate(Coefficients(Pol_bt, xK)[2], [0, zK]);
	ca_t := - aa_t*Evaluate(Coefficients(Pol_ct, xK)[1], [0, zK]) / Evaluate(Coefficients(Pol_ct, xK)[2], [0, zK]);
	// Constructing a polynomial h vanishing on the zeros of g.
	// FIXME: we are assuming that the conic has a c^2 term
	assert #Coefficients(DefiningEquation(MC), 3) eq 3;

	// If MC has rational point, find a new_t to be a P1 parameter for that curve.
	if HasRationalPoint(MC) then
		Pt := RationalPoint(MC);
		if (Pt[3]*ba_t - Pt[2]*ca_t ne 0) and (Pt[3]*aa_t - Pt[1]*ca_t ne 0) then
			pt := (Pt[3]*aa_t - Pt[1]*ca_t) / (Pt[3]*ba_t - Pt[2]*ca_t);
		elif (Pt[2]*aa_t - Pt[1]*ba_t ne 0) and (Pt[2]*ca_t - Pt[3]*ba_t ne 0) then
			pt := (Pt[2]*ca_t - Pt[3]*ba_t) / (Pt[2]*aa_t - Pt[1]*ba_t);
		elif (Pt[1]*ca_t - Pt[3]*aa_t ne 0) and (Pt[1]*ba_t - Pt[2]*aa_t ne 0) then
			pt := (Pt[1]*ba_t - Pt[2]*aa_t) / (Pt[1]*ca_t - Pt[3]*aa_t);
		else
			assert(false);
		end if;
		assert(Degree(Denominator(pt)) le 1);
		assert(Degree(Numerator(pt)) le 1);
		d,c := Explode(Eltseq(Denominator(pt)) cat [0]);
		b,a := Explode(Eltseq(Numerator(pt)) cat [0]);
		pt_inv := (d*zK - b) / (-c*zK + a);
		print "Warning: conic has rational point, implementation not verified!";
	end if;

	// Compute a hyperelliptic equation for the curve over P1 over K.
	dt := Derivative(t);
	v := qN * dt / BT[1];
	Pols := [yK^2] cat [xK^i : i in [0..2*g+2]];
	H_eq := FindPolynomial(Pols, [t, v]);
	H_eq /:=Coefficients(H_eq, yK)[1+2];
	assert Coefficients(H_eq, yK)[1+2] eq 1;
	f := -Evaluate(H_eq, [xK, 0]);
	if HasRationalPoint(D) then
		f2 := Evaluate(f, [pt_inv, 0]);
		if Denominator(f2) eq 1 then
			f2 := Numerator(f2);
		else
			factf2 := Factorisation(Denominator(f2));
			assert(#factf2 eq 1 and Degree(factf2[1][1]) eq 1);
			f2 := Numerator(f2) * factf2[1][1]^(factf2[1][2] mod 2);
		end if;
		f2 /:= LeadingCoefficient(f2);
		// Find the right constant c to scale h with
		q_t := Evaluate(pt, t);
		dq_t := Derivative(q_t);
		q_f2 := Evaluate(f2, q_t);
		elt := LeadingCoefficient(q_f2);
		// First scale f2 such that the leading q-expansion coefficient is 1, so we can take square roots.
		f2prime := f2/elt;
		q_f2prime := q_f2/elt;
		sqrt_q_f2prime := Sqrt(q_f2prime);
		M3_elts := [a : a in B] cat [qN*dq_t*1/sqrt_q_f2prime];
		M3_minprec := Min([AbsolutePrecision(x) : x in M3_elts]);
		M3 := Matrix([PadList(AbsEltseq(x), M3_minprec)[[1..M3_minprec]] : x in M3_elts]);
		kernel_basis := Basis(Kernel(M3));
		//print #kernel_basis;
		assert #kernel_basis eq 1;
		v := kernel_basis[1];
		assert v[g + 1] ne 0;
		// After having found a K-multiple that lies in the regular rational differentials, scale h back to correct.
		f2_correct := f2prime / v[g + 1]^2;
		assert(not(false in {c in Rationals() : c in Coefficients(f2_correct)}));
		f2_correct := ChangeRing(f2_correct, Rationals());
		//print "f2-polynomial:", f2_correct;
		
		// Construct the curve
		P2<y0, y1, z0> := WeightedProjectiveSpace(Rationals(), [1,1,g+1]);
		doubleCover := Homogenization(Evaluate(f2_correct, y1), y0, 2*g+2) - z0^2;
		doubleCover *:= LCM([Denominator(elt) : elt in Coefficients(doubleCover)]);
		XQQ := Curve(P2, [doubleCover]);
		return XQQ;
	else
	
		//print "Hyperelliptic polynomial over K:", f;

		// Find a hyperelliptic relation for the geometric curve over the conic.
		Qf := quo< Rf | Evaluate(f, [zK, 0]) >;
		Mons2 := [x3^i*y3^j*z3^(g+1-i-j) : i in [0..g+1], j in [0..1] | i+j le g + 1];
		//print ba_t, ca_t;
		if Degree(f) eq 2*g + 2 then
			Matrix2 := Matrix([ PadList(Eltseq(Evaluate(m, [Qf!aa_t, Qf!ba_t, Qf!ca_t])), 2*g+2) : m in Mons2]);
		else
			assert Degree(f) eq 2*g + 1;
			aa_LC := Coefficient(aa_t, 2);
			ba_LC := Coefficient(Numerator(ba_t), 2);
			ca_LC := Coefficient(Numerator(ca_t), 2);
			//Matrix2 := Matrix([ PadList(Eltseq(Evaluate(m, [Qf!aa_t, Qf!ba_t, Qf!ca_t])), 2*g + 2) cat [Evaluate(m, [ba_LC*ca_LC, aa_LC*ca_LC, aa_LC*ba_LC])] : m in Mons2]);
			Matrix2 := Matrix([ PadList(Eltseq(Evaluate(m, [Qf!aa_t, Qf!ba_t, Qf!ca_t])), 2*g + 2) cat [Evaluate(m, [aa_LC, ba_LC, ca_LC])] : m in Mons2]);
		end if;
		K2 := Kernel(Matrix2);
		assert(Dimension(K2) eq 1);
		B2 := Basis(K2)[1];
		h := &+[ B2[i]*Mons2[i] : i in [1..#Mons2]];
		h := Evaluate(h, [1, xK, yK]);
		assert {c in Rationals() : c in Coefficients(h)} eq {true};

		// Find the right constant c to scale h with
		q_b_over_a := Amin[2] / Amin[1];
		dq_b_over_a := Derivative(q_b_over_a);
		q_h := Evaluate(h, [Amin[2]/Amin[1], Amin[3]/Amin[1]]);
		elt := LeadingCoefficient(q_h);
		// First scale h such that the leading q-expansion coefficient is 1, so we can take square roots.
		hprime := h/elt;
		q_hprime := q_h/elt;
		sqrt_q_hprime := Sqrt(q_hprime);
		M3_elts := [a : a in B] cat [qN*dq_b_over_a*1/sqrt_q_hprime];
		M3_minprec := Min([AbsolutePrecision(x) : x in M3_elts]);
		M3 := Matrix([PadList(AbsEltseq(x), M3_minprec)[[1..M3_minprec]] : x in M3_elts]);
		kernel_basis := Basis(Kernel(M3));
		//print #kernel_basis;
		assert #kernel_basis eq 1;
		v := kernel_basis[1];
		assert v[g + 1] ne 0;
		// After having found a K-multiple that lies in the regular rational differentials, scale h back to correct.
		h_correct := hprime / v[g + 1]^2;
		//print "h-polynomial:", h_correct;
		
		// Construct the curve
		P3<y0, y1, y2, z0> := WeightedProjectiveSpace(Rationals(), [2,2,2,g+1]);
		conicEq := Evaluate(DefiningEquation(MC), [y0, y1, y2]);
		conicEq *:= LCM([Denominator(elt) : elt in Coefficients(conicEq)]);
		doubleCover := Homogenization(Evaluate(h_correct, [y1, y2]), y0, g+1) - z0^2;
		doubleCover *:= LCM([Denominator(elt) : elt in Coefficients(doubleCover)]);
		XQQ := Curve(P3, [conicEq, doubleCover]);
		return XQQ;
	end if;	
end function;

function SimplifyGeometricHyperellipticCurve(foo)
	//_<X, Y, Z, W> := Parent(DefiningEquations(foo)[2]);
	a := [1..#Coefficients(DefiningEquations(foo)[2]) - 1];
	N := GCD([Numerator(c) : c in Coefficients(DefiningEquations(foo)[2])[a]]);
	D := LCM([Denominator(c) : c in Coefficients(DefiningEquations(foo)[2])[a]]);
	_, sqrtN := SquarefreeFactorisation(N);
	sqfrD, sqrtD := SquareFreeFactorisation(D);
	P3<X, Y, Z, W> := WeightedProjectiveSpace(Rationals(), [2, 2, 2, Degree(DefiningEquations(foo)[2])]);
	eq1 := Evaluate(DefiningEquations(foo)[1], [X, Y, Z, W]);
	eq2 := sqrtD^2*sqfrD^2/sqrtN^2*Evaluate(DefiningEquations(foo)[2], [X, Y, Z, W*sqrtN/sqrtD/sqfrD]);
	bar := Curve(P3, [eq1, eq2]);
	return bar;
end function;

function HyperellipticModelFromLabel(label : i:=1, prec0:=0)
	gens := GetModularCurveGenerators(label);
	N := Characteristic(BaseRing(Parent(gens[1])));
	rec := CreateModularCurveRec(N,gens);
	bool, polys, fs := FindCanonicalModel(rec: prec0:=prec0);
	if not bool then
		B := [elt[i] : elt in fs];
		C := HyperellipticModel(B);
	else
		return false;
	end if;
	if Dimension(Ambient(C)) eq 3 then
		C := SimplifyGeometricHyperellipticCurve(C);
	end if;
	isH, H := IsHyperelliptic(C);
	if isH then
		H := ReducedMinimalWeierstrassModel(H);
		P2<X,Y,Z> := CoordinateRing(Ambient(H));
		return H;
	end if;
	return C;
end function;

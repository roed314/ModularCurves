N := 100;
//n := Integers() ! (N/2);

load "quadPts.m";

SetDebugOnError(true);

load "new_models.m";
time X, ws, pairs, NB, cusp := eqs_quos(N, [[N]]);
	// make defining equations of X integral by multiplying by the common denominator
	denominator := 1;
  	for f in DefiningEquations(X) do
      denominator := LCM([Denominator(c) : c in Coefficients(f)] cat [denominator]);
  	end for;
  	definingEquations := [denominator * f : f in DefiningEquations(X)];
  //X2 := X;
  X := Curve(AmbientSpace(X), definingEquations);
  /*printf "X = %o\n", X;
  time phi, Xnew, Xl, coord, proj := level_quo(X, N, n);
  print "1";
  Z := SmallModularCurve(n);
  assert Domain(phi) eq X;
  time flag, isom := IsIsomorphic(Codomain(phi), Z);
  assert flag;
  print "2";
  jinvN := Pullback(phi * isom, jFunction(Z, n));
  print "3";*/
  time jinvN := jmap(X, N);
  /*if additionalBadPrimes eq [] then
    for f in DefiningEquations(X) do
      additionalBadPrimes cat:= &cat[PrimeDivisors(Denominator(c)) : c in Coefficients(f)];
    end for;
  end if;*/
    
	// X=X_0(N)
 	// Z=X_0(n)
	// and phi : X --> Z is the degeneracy map
	// jinvN is the j-function as an element of the function field of X. 
	//
	//
	// We construct the cusps on X_0(N)
	//cusps := Poles(jinvN);
	preimage_of_infty := Pullback(jinvN, Codomain(jinvN)![1,0]);
	time cusp_pts := PointsOverSplittingField(Difference(preimage_of_infty, BaseScheme(jinvN)));
	function defining_ideal(c)
		R<[x]> := CoordinateRing(AmbientSpace(X));
		ind := Index(Eltseq(c), 1); // find a coordinate 1
		assert ind ne 0;
		return ideal< R | [Homogenization(Evaluate(MinimalPolynomial(c[i]), x[i]), x[ind]) : i in [1..#x]] >;
	end function;
	cusps := {Place(X, defining_ideal(c)) : c in cusp_pts};

// Sanity check!
cuspDegrees := [EulerPhi(GCD(m, N div m)) : m in Divisors(N)]; // The cusp degrees as predicted by theory.
assert Sort(cuspDegrees) eq Sort([Degree(c) : c in cusps]); // The degrees of the cusps we have found agree with theory.
cusps1 := [P : P in cusps | Degree(P) eq 1];
assert #cusps1 ge 2; 
            // There are always at least two cusps 
            // of degree 1 corresponding to the
            // factors 1 and N of N.
P0 := cusps1[1]; // This will our base point for the Abel-Jacobi map.

//time quadPts(N, 7 : additionalBadPrimes := [3]);
//time quadPts(N, n, 20 : additionalBadPrimes := [2,3,5]);

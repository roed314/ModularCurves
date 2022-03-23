load "Progs/quadPts.m";

//the following function checks if rank J0(N)(Q) = rank J0(N)+(Q) as suggested by Philippe
IsRankOfALQuotEqual := function(N)
  J := JZero(N);
  w := AtkinLehnerOperator(J,N);
  if(Nrows(Matrix(w)) eq 0) then
    printf "non-existent Atkin-Lehner operator";
    return false;
  end if;
  Jmin := ConnectedKernel(1+w);
  return not IsZeroAt(LSeries(Jmin),1);
end function;



// Compute the rank of J0(N)+ using Kolyvagin-Logachev. Will
// throw an error if the analytic rank for any newform appears 
// to be >1.
// I believe this is Steffen's code.
function rank_J0Nplus(N : Lprec := 30, printlevel := 0)
  NF := Newforms(CuspForms(Gamma0(N),2));
  errors := [];
  pl := printlevel;

  for f in [t[1] : t  in NF | AtkinLehnerEigenvalue(t[1], N) eq 1] do
    if pl gt 1 then printf "The newform is %o, \n", qExpansion(f, 20); end if;
    if pl gt 1 then printf "defined over %o. \n\b", NumberField(BaseRing(f)); end if;
    L := LSeries(ModularAbelianVariety(f));
    d := Degree(NumberField(BaseRing(f)));
    if not IsZeroAt(L, 1) then return 0, [0: i in [1..d]]; end if;
    Lseries := [LSeries(f : Embedding := func<x | Conjugates(x)[i] >) : i in [1..d]];
    rank := 0;
    i := 0;

    for L in Lseries do 
      LSetPrecision(L, Lprec);
      if pl gt 1 then "checking the functional equation for conjugate",i; end if;
      assert IsZero(CFENew(L));
      taylor := LTaylor(L, 1, 1);  
      if pl gt 0 then 
        printf "The Taylor expansion of the L-function of %o at s=1 is \n%o\n", f, taylor;
      end if;
      if IsZero(Coefficient(taylor, 0)) then 
        coeff := Coefficient(taylor, 1);
        if Abs(coeff) lt 10^-3 then // might be 0
          error "rank seems to be larger than g -- this is not implemented";
        else 
          rank +:= 1;
        end if;
      end if;
      Append(~errors, coeff);
      i +:= 1;
    end for; // L in Lseries
  end for; // f in ...
  return rank, errors;
end function;

function TorsionBound(X, BadPrimes : LowerBound := 0, PrimesBound := 20)
  torsionBound := 0;
  for p in PrimesUpTo(PrimesBound) do
    if p in BadPrimes then
      continue;
    end if;
    Fp := GF(p);
    try
	    Xp := ChangeRing(X, Fp);
    catch e
      continue; 
    end try;
    torsionBound := Gcd(torsionBound, #TorsionSubgroup(ClassGroup(Xp)));
    if torsionBound eq LowerBound then
      return torsionBound;
    end if;
  end for;
  return torsionBound;
end function;

//...
function GetTorsion(N, XN, XN_Cusps)

	if IsPrime(N) then
		// sanity check
		assert #XN_Cusps eq 2;

		Dtor := Divisor(XN_Cusps[1]) - Divisor(XN_Cusps[2]);
		order := Integers()!((N - 1) / GCD(N - 1, 12));
		
		A := AbelianGroup([order]);
		divs := [Dtor];

	else
		p := 3;
		while IsDivisibleBy(N, p) do
			p := NextPrime(p);
		end while;

		// compute the cuspidal torsion subgroup (= J(Q)_tors assuming the generalized Ogg conjecture)
		h, Ksub, bas, divsNew := findGenerators(XN, [Place(cusp) : cusp in XN_Cusps], Place(XN_Cusps[1]), p);

		// Ksub == abstract group isomorphic to cuspidal
		// "It also returns a subset divsNew such that [[D-deg(D) P_0] : D in divsNew] generates the same subgroup."

		A := Ksub;

		D := [Divisor(divsNew[i]) - Divisor(XN_Cusps[1]) : i in [1..#divsNew]];
		divs := [&+[coeffs[i] * D[i] : i in [1..#coeffs]] : coeffs in bas];
	end if;

	return A, divs;

end function;

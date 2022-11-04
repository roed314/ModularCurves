AttachSpec("ModCrv.spec");

function testGenus0Gamma0(N)
    // When N eq 1, magma has problems with points on the curve, not clear why, probably since there are no degree 1 generators
    assert N ne 1;
    PG := Gamma0(N);
    assert Genus(PG) eq 0;
    X<[x]>, fs, K := CanonicalRing(PG);
    E4, E6, j := JMap(Gamma0(N), X, fs, K : LogCanonical);
    P := X![Evaluate(f, 0) : f in fs];
    assert (not IsSingular(P));
    rr, rr_map := RiemannRochSpace(Divisor(P));
    P1_map_rat := ProjectiveFunction(rr_map(rr.1)/rr_map(rr.2));
    P1_map := [Numerator(P1_map_rat), Denominator(P1_map_rat)];
    P1<s,t> := ProjectiveSpace(Rationals(),1);
    pi := map<X->P1 | P1_map>;
    assert IsInvertible(pi);
    E4_P1 := Evaluate(E4, [pi(xx) : xx in x]);
    E6_P1 := Evaluate(E6, [pi(xx) : xx in x]);
    return E4_P1, E6_P1;
end function;

// Warning - this test takes a long time
function testAllGenus0Gamma0()
    genus_0 := [2..10] cat [12,13,16,18,25];
    E4s := [];
    E6s := [];
    for N in genus_0 do
	E4, E6 := testGenus0Gamma0(N);
	Append(~E4s, E4);
	Append(~E6s, E6);
    end for;
    return E4s, E6s;
end function;

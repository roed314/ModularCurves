function find_common_evec_mod_p(H, p)
    assert IsPrime(p);
    Hp := sub<GL(2, Integers(p)) | Generators(H)>;
    gens := Generators(Hp);
    gens_t := [Transpose(Matrix(h)) : h in gens];
    espaces := [{Eigenspace(h, ev[1]) : ev in Eigenvalues(h)} : 
		h in gens_t];
    if IsEmpty(espaces) then
	return false, _;
    end if;
    common := &meet espaces;
    if IsEmpty(common) then
	return false, _;
    end if;
    common := [V : V in common];
    v_p := Basis(common[1])[1];
    return true, v_p;
end function;

function borel_recognize_mod_N(H)
    ZN := BaseRing(H);
    assert Type(ZN) eq RngIntRes;
    N := Modulus(ZN);
    // Magma does not have a root algorithm over Z_N
    assert IsPrime(N);
    gens := Generators(H);
    gens_t := [Transpose(Matrix(h)) : h in gens];
    espaces := [{Eigenspace(h, ev[1]) : ev in Eigenvalues(h)} : 
		h in gens_t];
    common := &meet espaces;
    if IsEmpty(common) then
	return false;
    end if;
    common := [V : V in common];
    v1 := Basis(common[1])[1];
    // could take any linearly independent vector
    v2 := Basis(Kernel(Transpose(Matrix(v1))))[1];
    t := GL(2,Integers(N))!Transpose(Matrix([v1,v2]));
    return t, v1; // H^t is now a Borel subgroup
end function;

function poly_roots_mod_prime_power(f)
    ZN := BaseRing(f);
    N := Modulus(ZN);
    is_pp, p, e := IsPrimePower(N);
    Fp := Integers(p);
    for j in [1..e] do
	Zpj := Integers(p^j);
	Zpjx<x> := PolynomialRing(Zpj);
	if (j eq 1) then
	    roots := [r[1] : r in Roots(Zpjx!f)];
	else
	    root_lifts := [Zpj!r : r in roots];
	    roots := [Zpj | ];
	    for r in root_lifts do
		fprime := Fp!Evaluate(Derivative(Zpjx!f), r);
		fval := Evaluate(Zpjx!f, r);
		if (fprime eq 0) then
		    if fval eq 0 then
			// All lifts work
			roots cat:= [r + p^(j-1) * i : i in [0..p-1]];
		    end if;
		else
		    r1 := Zpj!(fprime^(-1)) * fval;
		    Append(~roots, r - r1);
		end if;
	    end for;
	end if;
	assert &and[Evaluate(Zpjx!f, r) eq 0 : r in roots];
    end for;
    assert &and[Evaluate(f, r) eq 0 : r in roots];
    return roots;
end function;

// v_p is an eigenvector modulo p, lam is the eigenvalue
function lift_eigenvector(h, v_p, lam)
    ZN := BaseRing(h);
    N := Modulus(ZN);
    is_pp, p, e := IsPrimePower(N);
    assert e eq 2; // have not implemented the general case yet
    Fp := Integers(p);
    M2p := MatrixAlgebra(Fp,2);
    v0 := Vector(ZN, Eltseq(v_p));
    h0 := MatrixAlgebra(ZN, 2)!(M2p!h);
    h1 := (h - h0) div (ZN!p);
    lam0 := ZN!(Fp!lam);
    lam1 := (lam - lam0) div p;
    tmp := -(v0*h0 - lam0*v0) div (ZN!p);
    tmp -:= v0*h1 - lam1*v0;
    t := MatrixAlgebra(Integers(p),2)!(h0-lam0);
    vv := Vector(Fp, tmp);
    v1 := Solution(t, vv);
    v := v0 + p*Vector(ZN,Eltseq(v1));
    assert IsZero(v*h-lam*v);
    return v;
end function;

function find_common_evec(H)
    ZN := BaseRing(H);
    N := Modulus(ZN);
    is_pp, p, e := IsPrimePower(N);
    Fp := Integers(p);
    gens_t := [Transpose(Matrix(h)) : h in Generators(H)];
    V := RSpace(ZN,2);
    espaces := [PowerSet(V) | ];
    for h in gens_t do
	f<x> := CharacteristicPolynomial(h);
	lams := poly_roots_mod_prime_power(f);
	evecs := &cat[Basis(Kernel(h - ScalarMatrix(2, ZN!lam))) : lam in lams];
	Append(~espaces, {V!v : v in evecs});
    end for;
    // Could find the lift but this is faster
    // assert exists(ev){ev : ev in evecs | Vector(Fp, ev) eq v_p};
    if IsEmpty(espaces) then
	return false, _;
    end if;
    common := &meet espaces;
    if IsEmpty(common) then
	return false, _;
    end if;
    common := [V : V in common];
    assert exists(ev){v : v in common | 
		      GCD([Integers()!x : x in Eltseq(v) cat [N]]) eq 1};
    v2 := Basis(Kernel(Transpose(Matrix(ev))))[1];
    t := GL(2,Integers(N))!Transpose(Matrix([ev,v2]));
    return true, t; // H^t is now a Borel subgroup
end function;

function get_maximal_borel_intersection(H)
    ZN := BaseRing(H);
    N := Modulus(ZN);
    P1, rescale := ProjectiveLine(ZN);
    rev_lookup := AssociativeArray(P1);
    for i->pt in P1 do
	rev_lookup[pt] := i;
    end for;

    // Set up the appropriate data structure so we can apply union-find.
    
    Node := recformat<pt : ModTupRngElt, 
		      rank : RngIntElt,
		      parent : RngIntElt>;
    
    nodes := [];
    
    for i->pt in P1 do
	node := rec< Node| >;
	node`pt := pt;
	node`rank := 0;
	node`parent := i;
	Append(~nodes, node);
    end for;
    
    // Retrieve the generators of the group.
    // We transpose because H acts on the left
    gs := {Transpose(g) : g in Generators(H)};
    
    // Do we need this?
    gs := gs join {g^(-1) : g in gs};
    
    // This function establishes the parent node of all elements in the
    //  partition to an element of least rank.
    function find(nodes, i)
	x := nodes[i];
	if x`parent ne i then
	    x`parent := find(nodes, x`parent);
	end if;
	return x`parent;
    end function;
    
    // Merge sets which are in the same equivalance class. We do this by
    //  establishing the parent (found with `find' above) for all elements
    //  in the partition.
    // TODO : This union-find is not very efficient...
    // Implement an efficient version
    procedure union(~nodes, i, j)
	// x := nodes[i];
	// y := nodes[j];
	xRoot := find(nodes, i);
	yRoot := find(nodes, j);
	if xRoot eq yRoot then return; end if;

	if nodes[xRoot]`rank lt nodes[yRoot]`rank then
	    nodes[xRoot]`parent := yRoot;
	elif nodes[xRoot]`rank gt nodes[yRoot]`rank then
	    nodes[yRoot]`parent := xRoot;
	else
	    nodes[yRoot]`parent := xRoot;
	    nodes[xRoot]`rank := nodes[xRoot]`rank + 1;
	end if;
    end procedure;
    
    // Apply the generators of the automorphism group to each subspace.
    for i->x in nodes do
	for g in gs do
            _, new_pt, _ := rescale(x`pt * g, false, true);
	    idx := rev_lookup[new_pt];
	    union(~nodes, i, idx);
	end for;
    end for;
    
    O := AssociativeArray();

    // Populate the associative array, keeping track of how many orbits are
    //  in each partition.
    for x in nodes do
	if not IsDefined(O, x`parent) then
	    O[x`parent] := 1;
	else
	    O[x`parent] +:= 1;
	end if;
    end for;
    
    min_elt := Minimum([<O[x], nodes[x]`pt> : x in Keys(O)]);
    ts := [];
    min_vs := [nodes[x]`pt : x in Keys(O) | O[x] eq min_elt[1]];
    for v1 in min_vs do
	// could take any linearly independent vector
	v2 := Basis(Kernel(Transpose(Matrix(v1))))[1];
	mat := Transpose(Matrix([v1,v2]));
	while not IsInvertible(mat) do
	    v2[2] +:= 1;
	    mat := Transpose(Matrix([v1,v2]));
	end while;
	t := GL(2,Integers(N))!mat;
	Append(~ts, t);
    end for;
    
    return ts; // H^t now has maximal Borel intersection for every such t
end function;

// feed a Borel and see if we can find it after conjugation
// at the moment only works for prime powers
procedure test_find_common_evec(B : num_tests := 10)
    ZN := BaseRing(B);
    for i in [1..num_tests] do
	a := Random(GL(2, ZN));
	H := B^a;
	has_common, t := find_common_evec(H);
	assert (has_common) and (H^t eq B);
    end for;
end procedure;

function get_borel_level(H)
    ZN := BaseRing(H);
    N := Modulus(ZN);
    fac := Factorization(N);
    borel_level := 1;
    conjs := [* *];
    for pe in fac do
	p, e := Explode(pe);
	has_ev := false;
	j := 1;
	t := H!1;
	repeat
	    Zpj := Integers(p^j);
	    Hpj := sub<GL(2, Zpj) | Generators(H)>;
	    prev_t := t;
	    has_ev, t := find_common_evec(Hpj);
	    j +:= 1;
	until (not has_ev) or (j gt e);
	borel_level *:= p^(j-1);
	Append(~conjs, has_ev select t else prev_t);
    end for;
    return borel_level, conjs;
end function;

function TestFindConjugates(line)
    data := Split(line, ":");
    label := data[1];
    level := StringToInteger(Split(label, ".")[1]);
    if (level eq 1) then
	return 0;
    end if;
    gens := eval(data[3]);
    conjugators := eval(data[7]);
    ZN := Integers(level);
    G := GL(2, ZN);
    H := sub< G | gens>;
    H_conjs := {H^(G!a) : a in conjugators};
    start_time := Cputime();
    ts := get_maximal_borel_intersection(H);
    timing := Cputime(start_time);
    assert {H^t : t in ts} eq H_conjs;
    return timing;
end function;

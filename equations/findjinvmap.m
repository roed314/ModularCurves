// This function computes the map to the j-line for a non-hyperelliptic 

function GetDegrees(M, is_hyp)
    if is_hyp then
	return 6,6;
    end if;
    maxd := Floor((M`index)/(2*M`genus-2) + 3/2);
    if ((maxd-1) ge (M`index)/(2*M`genus-2)) and
       ((maxd-1) le ((M`index)/(2*M`genus-2) + 1/2)) then
	mind := maxd-1;
	printf "The smallest degree that might work is %o.\n",mind;
	printf "Degree %o definitly works.\n",maxd;  
    else
	mind := maxd;
	printf "The smallest degree that might work is %o and it definitely works.\n",maxd;
    end if;
    return mind, maxd;
end function;

function GetPrecision(M, maxd, is_hyp)
    numcusps := M`vinf;
    N := M`N;
    // oldprec := Ceiling(maxd*(N/3-2) + 2);
    maxprec := Floor(N*(1 + maxd/6)+1);
    // For 7.168.3.1, minimal prec = 16. 
    if is_hyp then
	maxprec +:= N;
    end if;
    printf "Precision chosen = %o.\n",maxprec;
    return maxprec;
end function;

function dimension(M,d, is_can)
    if (is_can) then
	return (2*d-1)*(M`genus-1);
    else
	return (2*d-1)*(M`genus-1) + d*M`vinf + M`v2*Floor(d/4) + M`v3*Floor((2*d)/3);
    end if;
end function;

function get_row_qexp(qexp, prec)
    return &cat[Eltseq(x) : x in AbsEltseq(qexp)[1..prec]];
end function;

function get_row_f(f, precs)
    numcusps := #f;
    assert #f eq #precs;
    return &cat[get_row_qexp(f[i], precs[i]) : i in [1..numcusps]];
end function;

function FindJMapInv(M, maxprec, mind, maxd)
    // Build canonical ring
    //assert M`k eq 2;
    //assert #M`F0 eq M`genus;
    is_can := (#M`F0 eq M`genus) and (M`k eq 2);
    assert #M`F0 eq Rank(Universe(M`psi));

    tttt := Cputime();
    numcusps := M`vinf;
    N := M`N;
    modforms := M`F0;
    //polyring := ChangeRing(Parent(M`psi[1]),Rationals());
    // polyring := PolynomialRing(Rationals(),#modforms,"grevlex");
    // polyring := ChangeRing(Universe(M`psi), Rationals());
    polyring := PolynomialRing(Rationals(), 
			       Grading(Universe(M`psi)), "grevlex");
    vars := [ polyring.i : i in [1..#modforms]];
    gens := [ Evaluate(M`psi[j],vars) : j in [1..#M`psi]];

    ttemp := Cputime();
    printf "Computing Grobner basis for canonical ideal.\n";
    I := ideal<polyring | gens>;
    G := GroebnerBasis(I);
    gbtime := Cputime(ttemp);
    printf "Grobner basis time was %o.\n",gbtime;
    LMs := [ LeadingMonomial(G[i]) : i in [1..#G]];
    initideal := ideal<polyring | LMs>;
    
    // canring is a list of pairs.
    // The first thing in a pair is list of lists of Fourier expansions
    // of the degree d generators of the canonical ring.
    // The second thing in a pair is list of degree d monomials representing the
    // elements.
    
    gen_deg := Maximum(Grading(polyring));
    canring := [<[M`F0[v] : v in [1..#vars] | Degree(vars[v]) eq d],
		 [vars[v] : v in [1..#vars] | Degree(vars[v]) eq d]> 
		: d in [1..gen_deg]];
    K := BaseRing(Parent(M`F0[1][1]));
    qN := Parent(M`F0[1][1]).1;
    LL := LaurentSeriesRing(K);
    fielddeg := Degree(K);

    // Let's choose monomials that will *always* work!

    printf "Generating canonical ring.\n";
    ttime := Cputime();
    multcount := 0;
    doneper := -1;
    total := &+[ dimension(M, d, is_can) : d in [gen_deg+1..maxd]];    
    
    for d in [gen_deg+1..maxd] do
	// this is for log canonical
	dimen := dimension(M, d, is_can);
	fouriermat := ZeroMatrix(Rationals(),0,(maxprec-1)*fielddeg*numcusps);
	mons := MonomialsOfWeightedDegree(polyring,d);
	bas := [ mons[i] : i in [1..#mons] | not (mons[i] in initideal)];
	newfourier := [];
	newvars := [];
	for j in [1..#bas] do
	    curmon := bas[j];
	    // We have to be able to write curmon as a product of a 
	    // degree (d-d0)
	    // monomial not in initideal, and a degree d0 element,
	    // where d0 is in [1..gen_deg]
	    // If we couldn't, then curmon would be in initideal
	    divs := [[IsDivisibleBy(curmon, m) : m in canring[d-d0][2]] 
		     : d0 in [1..gen_deg]];
	    d0 := Index([&or is_div : is_div in divs], true);
	    ind := Index(divs[d0],true);
	    chk, q := IsDivisibleBy(curmon,canring[d-d0][2][ind]);
	    ind2 := Index(vars,q);
	    multcount := multcount + 1;
	    if Floor(100*multcount/total) gt doneper then
		doneper := Floor(100*multcount/total);
		printf "Doing multiplication %o of %o. %o\%% complete.\n",multcount,total,doneper;
	    end if;  
	    newprd := [ modforms[ind2][i]*canring[d-d0][1][ind][i] : i in [1..numcusps]];
	    Append(~newfourier,newprd);
	    Append(~newvars,curmon);
	end for;
	Append(~canring,<newfourier,newvars>);
    end for;
    canringtime := Cputime(ttemp);
    printf "Canonical ring time was %o.\n",canringtime;

    // Simplify a Q-vector space. This script takes a matrix M
    // and finds the lattice of elements L where all the coordinates are integers.
    // Then it finds an LLL-reduced basis for that lattice. It returns
    // a square matrix that indicates which linear combinations of the rows of M
    // are the LLL-reduced basis

    function nicefy(M)
	M0, T := EchelonForm(M);
	// Rows of T give current basis.
	ee := Eltseq(M0);
	denom := LCM([ Denominator(ee[i]) : i in [1..#ee]]);
	printf "Nicefying %ox%o matrix with denominator %o.\n",NumberOfRows(M),NumberOfColumns(M),denom;
	M2 := Matrix(Integers(),NumberOfRows(M),NumberOfColumns(M),[ denom*ee[i] : i in [1..#ee]]);
	printf "Computing saturation.\n";
	//SetVerbose("Saturation",2);
	AA := Saturation(M2);
	printf "Done.\n";
	chk, mult := IsConsistent(ChangeRing(M2,Rationals()),ChangeRing(AA,Rationals()));
	curbat := denom*mult*T;
	printf "Calling LLL.\n";
	newlatbasismat, change := LLL(AA : Proof := false);
	printf "Done.\n";
	finalbat := ChangeRing(change,Rationals())*curbat;
	return finalbat;
    end function;

    ttemp := Cputime();
    if (is_can) then
	j_prec := Ceiling((maxprec+2*N) / N);
    else
	j_prec := Ceiling((maxprec+3*N) / N);
    end if;
    j := (1728*Eisenstein(4,qN : Precision := j_prec)^3)/(Eisenstein(4,qN : Precision := j_prec)^3 - Eisenstein(6,qN : Precision := j_prec)^2);
    j := Evaluate(j,qN^N);

    func := j;
    done := false;

    curd := mind;
    jmat := ZeroMatrix(Rationals(),0,(maxprec-1)*fielddeg*numcusps);
    for i in [1..#canring[curd][1]] do
	vecseq := [];
	for jj in [1..numcusps] do
	    pp := LL!(func*canring[curd][1][i][jj]);
	    vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [curd-N..curd-N+maxprec-2]]);
	end for;
	jmat := VerticalJoin(jmat,Matrix(Rationals(),1,(maxprec-1)*fielddeg*numcusps,vecseq));
    end for;
    
    for i in [1..#canring[curd][1]] do
	vecseq := [];
	for jj in [1..numcusps] do
	    pp := LL!(-canring[curd][1][i][jj]);
	    vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [curd-N..curd-N+maxprec-2]]);
	end for;
	jmat := VerticalJoin(jmat,Matrix(Rationals(),1,(maxprec-1)*fielddeg*numcusps,vecseq));
    end for;
    NN := NullSpace(jmat);
    dimdim := Dimension(NN);
    printf "For d = %o, dimension of null space is %o.\n",curd,dimdim;
    if dimdim ge 1 then
	done := true;
    end if;

    if (done eq false) then
	curd := maxd;
	jmat := ZeroMatrix(Rationals(),0,(maxprec-1)*fielddeg*numcusps);
	for i in [1..#canring[curd][1]] do
	    vecseq := [];
	    for jj in [1..numcusps] do
		pp := LL!(func*canring[curd][1][i][jj]);
		vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [curd-N..curd-N+maxprec-2]]);
	    end for;
	    jmat := VerticalJoin(jmat,Matrix(Rationals(),1,(maxprec-1)*fielddeg*numcusps,vecseq));
	end for;
	
	for i in [1..#canring[curd][1]] do
	    vecseq := [];
	    for jj in [1..numcusps] do
		pp := LL!(-canring[curd][1][i][jj]);
		vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [curd-N..curd-N+maxprec-2]]);
	    end for;
	    jmat := VerticalJoin(jmat,Matrix(Rationals(),1,(maxprec-1)*fielddeg*numcusps,vecseq));
	end for;
	NN := NullSpace(jmat);
	printf "For d = %o, dimension of null space is %o.\n",curd,Dimension(NN);
    end if;

    // Now actually write down the map to the j-line

    canringdim := #canring[curd][1];
    nullmat := Matrix(Basis(NN));
    changemat := nicefy(nullmat);
    v := (changemat*nullmat)[1];
    denom := &+[ (polyring!v[i])*canring[curd][2][i] : i in [1..canringdim]];
    num := &+[ (polyring!v[i+canringdim])*canring[curd][2][i] : i in [1..canringdim]];
    weakzero := [ &+[ v[i]*canring[curd][1][i][j] : i in [1..canringdim]]*func - &+[ v[i+canringdim]*canring[curd][1][i][j] : i in [1..canringdim]] : j in [1..numcusps]];
    assert &and [ IsWeaklyZero(weakzero[i]) : i in [1..numcusps]];
    val := &+[ AbsolutePrecision(weakzero[i])*M`widths[i] : i in [1..numcusps]]/N;
    normwt := (M`index)*curd*2;
    printf "Valuation of norm = %o.\n",val;
    printf "This should be greater than %o.\n",normwt/12;
    assert (val gt (normwt/12));
    
    lintime := Cputime(ttemp);
    printf "Linear algebra time was %o.\n",lintime;

    C := Curve(ProjectiveSpace(polyring), M`psi : Nonsingular := true);
    Cvars := [ C.i : i in [1..#modforms]];
    jmap := map<C -> ProjectiveSpace(Rationals(),1) | [num,denom]>;

    printf "Skipping point search.\n";
/*	       
    ttime := Cputime();
    pts := PointSearch(C,1000);
    pttime := Cputime(ttime);
    printf "Point search time was %o.\n",pttime;
    ttime := Cputime();
    for i in [1..#pts] do
	printf "Point %o has image %o.\n",pts[i],jmap(pts[i]);
    end for;
    jtime := Cputime(ttime);
    printf "Done.\n";
*/
   
    // If started with a log canonical model,
    // map to a curve in regular projective space
    if (not is_can) then
	printf "Constructing a model embedded in projective space...\n";
	invtime :=  Cputime();
	X := FindModelOfXG(M);
	X_emb := Curve(ProjectiveSpace(Universe(X`psi)), X`psi);
	// Here we use the fact that David is embedding X 
	// using forms of weight X`k
	precs_orig := [AbsolutePrecision(f) : f in canring[X`k div 2][1][1]];
	precs_new := [AbsolutePrecision(f) : f in X`F0[1]];
	precs := [Minimum(precs_orig[i], precs_new[i]) : i in [1..#precs_new]];
	orig_basis := Matrix([get_row_f(f, precs) : f in canring[X`k div 2][1]]);
	f_rows := Matrix([get_row_f(f, precs) : f in X`F0]);
	lin_comb := Solution(orig_basis, f_rows);
	vec := Vector(canring[X`k div 2][2]);
	vec := vec * Transpose(ChangeRing(lin_comb, BaseRing(vec)));
	iota := map<C->X_emb | Eltseq(vec)>;
	is_inv, iota_inv := IsInvertible(iota);
	assert is_inv;
	jmap_emb := iota_inv * jmap;
	jmap_alg := AlgebraMap(jmap_emb);
	num := jmap_alg(Domain(jmap_alg).1);
	denom := jmap_alg(Domain(jmap_alg).2);
	jmap := map<X_emb -> ProjectiveSpace(Rationals(),1) | [num,denom]>;
	printf "Done.\n";
	invtime := Cputime(invtime);
    else
	X := M;
    end if;
    
    printf "GB time = %o.\n",gbtime;
    printf "Canonical ring time = %o.\n",canringtime;
    printf "Linear algebra time = %o.\n",lintime;
    if (not is_can) then
	printf "Inverting map time = %o.\n", invtime; 
    end if;
//    printf "Point search time = %o.\n",pttime;
//    printf "j-map time = %o.\n",jtime;
    printf "Total time was %o sec.\n",Cputime(tttt);
    return X, jmap, num, denom;
end function;


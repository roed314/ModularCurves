//////////////
// Philippe // (get in touch with me if (when) you find problems with the code!)
//////////////

// Code to compute models for X_0(N), its AL quotients, and maps to the quotients.
// Code computes models for which all AL involutions are diagonalised.
// Main function is eqs_quos

// There are many examples included after the function eqs_quos

// After this there are some extra functions 
// The main useful one is probably level_quo
// this gives you a map to a quotient curve X_0(M) of a lower level (under certain conditions)


///////////////
/// canonic ///  
///////////////

// B is a sequence of cusp forms.
// Computes the canonical embedding.
canonic := function(B); 
    N := Level(B[1]);
    prec := 5*N; 
    dim:=#B;
    L<q>:=LaurentSeriesRing(Rationals(),prec);
    R<[x]>:=PolynomialRing(Rationals(),dim);
    Bexp:=[L!qExpansion(B[i],prec) : i in [1..dim]];
    eqns:=[R | ];
	d:=1;
	tf:=false;
	while tf eq false do
		d:=d+1; 
		mons:=MonomialsOfDegree(R,d);
		monsq:=[Evaluate(mon,Bexp) : mon in mons];
		V:=VectorSpace(Rationals(),#mons);
		W:=VectorSpace(Rationals(),prec-10);
		h:=hom<V->W | [W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]]>;
		K:=Kernel(h);
		eqns:=eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
        	I:=Radical(ideal<R | eqns>);
		X:=Scheme(ProjectiveSpace(R),I);
		if Dimension(X) eq 1 then
			if IsIrreducible(X) then
				X:=Curve(ProjectiveSpace(R),eqns);
				if Genus(X) eq dim then
					tf:=true;
				end if;
			end if;
		end if;
	end while;
    
    indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];	
	indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)

	for eqn in eqns do
		eqnScaled:=LCM([Denominator(c) : c in Coefficients(eqn)])*eqn;
		wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound for Gamma_0(N)						 
	    Bexp1:=[qExpansion(B[i],hecke+10) : i in [1..dim]]; // q-expansions
		assert Valuation(Evaluate(eqnScaled,Bexp1)) gt hecke+1;
	end for; // We have now checked the correctness of the equations for X.	
  
 return(X);
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////
/// simul_diag /// (auxiliary function)
//////////////////

// This is an auxiliary function for later code.

// Input: A sequence of matrices that are involutions
// Output: The matrix T that simultaneuosly diagonalised them and the diagonalised matrices.

simul_diag := function(seqw);
    n := NumberOfRows(seqw[1]);
    Vs := [VectorSpace(Rationals(),n)];

    for w in seqw do
        NVs := [];
        for U in Vs do
            BU := Basis(U);
            N1 := Nullspace(w-1) meet U;
            N2 := Nullspace(w+1) meet U;
            NVs := NVs cat [N1,N2];
            Vs := NVs;
        end for;
     end for;

     new_basis := &cat[Basis(V) : V in NVs | Dimension(V) gt 0];
     T := Matrix(new_basis);
     new_als := [T*w*T^(-1) : w in seqw];
     return T, new_als;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////////
/// all_diag_basis /// 
//////////////////////

// Input: N
// Output: - A basis for the cusp forms of level N for which all AL involutions act as diagonal matrices
// - the matrices of the AL involutions (listed in ascending order by AL index)

all_diag_basis := function(N);
    C := CuspForms(N);
    g := Dimension(C);

    al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
    al_invols := [AtkinLehnerOperator(C,d) : d in al_inds];

    T, new_als := simul_diag(al_invols);
    B := Basis(C);
    NB := [&+[(T)[i,j]*1*B[j] : j in [1..g]] : i in [1..g]];  // can change 1   
    return NB, new_als;
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////
/// all_diag_X /// 
//////////////////

// Input: N
// Output: 
// - A model for X_0(N) with all the Atkin-Lehner involutions diagonalised
// - the Atkin-Lehner involutions (listed in ascending order by index)
// - basis of cuspforms used
// - The infinity cusp (as a rational point)

// X_0(N) should be of genus > 1 and non-hyperelliptic.

all_diag_X := function(N);
    NB, new_als := all_diag_basis(N);
    X:=canonic(NB);        
    A<[x]> := AmbientSpace(X); 
    g := Dimension(A)+1;
               
    als_X := [ iso<X->X | [w[i,i]*x[i] : i in [1..g]], [w[i,i]*x[i] : i in [1..g]]>  : w in new_als];

    cusp_seq := [];
    for f in NB do
        if Coefficient(f,1) ne 0 then 
            cusp_seq := cusp_seq cat [1];
        else cusp_seq := cusp_seq cat [0];
        end if;
    end for;
    cusp := X ! cusp_seq;
    return X, als_X, NB, cusp;
end function;   


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

///////////////////////////////////
/// Hyperelliptic quotient data /// 
///////////////////////////////////

// Star quotients
// If N is in this list, the star quotient of X_0(N) is hyperelliptic curve of genus > 2.
// Taken from Theorem 2 of Furemoto--Hasegawa 1999
hyper_stars := [136, 171, 176, 207, 252, 279, 315];

// Non-star quotients (genus >2)
// First entry of the tuple is N
// Second entry is the indices of the Atkin-Lehner involutions that we quotient out by (listed in ascending order)
// Includes all data for different ways of writing the same group
// e.g. <78, [2,3,6]> and <78, [2,3]> correspond to the same curve and are both included.
// Taken from Theorems 3 and 4 of Furemoto--Hasegawa 1999
hyper_data :=  [
<46, [2]>, 
<51, [3]>, 
<55, [5]>, 
<56, [8]>, 
<60, [4]>, <60, [12]>, <60, [60]>, 
<62, [2]>, 
<66, [6]>, <66, [66]>, 
<69, [3]>, 
<70, [10]>, <70, [14]>, 
<78, [6]>, <78, [26]>, <78, [2,3,6]>, <78, [2,3]>, <78, [2,6]>, <78, [3,6]>, <78, [6,13,39]>, <78, [6,13]>, <78, [6,39]>, <78, [13,39]>,
<87, [3]>, 
<92, [4]>, <92, [92]>, 
<94, [2]>, <94, [94]>, 
<95, [5]>, <95, [19]>, 
<105, [3,5,15]>, <105, [3,5]>, <105, [3,15]>, <105, [5,15]>, <105, [3,7,21]>, <105, [3,7]>, <105, [3,21]>, <105, [7,21]>, <105, [7,15,105]>, <105, [7,15]>, <105, [7, 105]>, <105, [15, 105]>,
<110, [2,5,10]>, <110, [2,5]>, <110, [2,10]>, <110, [5,10]>, <110, [2,11,22]>, <110, [2,11]>, <110, [2,22]>, <110, [11,22]>, <110, [5,22,110]>, <110, [5,22]>, <110, [5, 110]>, <110, [22, 110]>,
<119, [7]>, <119, [17]>,
<63, [9]>,
<72, [9]>,
<104, [104]>,
<120, [5,24,120]>, <120, [5,24]>, <120, [5,120]>, <120, [24,120]>,
<126, [7,9,63]>, <126, [7,9]>, <126, [7,63]>, <126, [9,63]>, <126, [9,14,126]>, <126, [9,14]>, <126, [9,126]>, <126, [14,126]>,
<168, [21, 24, 56]>, <168, [21,24]>, <168, [21,56]>, <168, [24,56]>
];

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////
/// genus_quo /// 
/////////////////

// Input: N and a sequence of AL indices (in ascending order)
// Output: The genus of the corresponding quotient of X_0(N)

// X_0(N) should be of genus > 0.

genus_quo := function(N, seq_al);
    C := CuspForms(N);
    g := Dimension(C);
    // start by simply diagonalising all AL involutions
    al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
    al_invols := [AtkinLehnerOperator(C,d) : d in al_inds];
    T, new_als := simul_diag(al_invols);
    // pick out those corresponding to seq_al
    seqw_M := [new_als[i] : i in [1..#new_als] | al_inds[i] in seq_al];
    Ss := [Diagonal(Mw) : Mw in seqw_M];
    n := #Ss[1];
    gen_seq := [1 : i in [1..n] | &+[s[i] : s in Ss] eq #Ss];
    if IsNull(gen_seq) then 
        g_quo := 0;
    else g_quo := &+gen_seq;
    end if;
    return g_quo;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////////
/// is_hyper_quo /// 
////////////////////

// Input: N and a sequence of AL indices
// Output: true or false according to whether the quotient is hyperelliptic or not.

// X_0(N) should be of genus > 0 and non-hyperelliptic.

is_hyper_quo := function(N, seq_al);
    g_quo := genus_quo(N,seq_al);
        if g_quo eq 2 then 
           is_hyp := true;
        elif g_quo gt 2 and N in hyper_stars then // we check by computation if AL involutions generate the whole group.
            C := CuspForms(N);
            n := Dimension(C);
            // start by simply diagonalising all AL involutions
            al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
            al_invols := [AtkinLehnerOperator(C,d) : d in al_inds];
            T, new_als := simul_diag(al_invols);
            // pick out those corresponding to seq_al
            seqw_M := [new_als[i] : i in [1..#new_als] | al_inds[i] in seq_al];
            GL_n := GeneralLinearGroup(n, Rationals());
            al_group := sub<GL_n | seqw_M >;
            if #al_group eq 2^(#PrimeFactors(N)) then 
                is_hyp := true;
            elif <N, seq_al> in hyper_data then 
                is_hyp := true;
            else is_hyp := false;
            end if;
        elif g_quo gt 2 and <N, seq_al> in hyper_data then 
            is_hyp := true;
        else is_hyp := false;
        end if;
    return is_hyp;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////
/// eqs_quos /// 
////////////////

// Input: N and a sequence of sequences of Atkin-Lehner indices 
// (each sequence of indices should be given in ascending order by index)
// Output: 
// - A model for X_0(N) with all the Atkin-Lehner involutions diagonalised
// - The diagonalised Atkin-Lehner involutions on X_0(N) (listed in ascending order by index)
// - A list: for each sequence of AL-indices, a tuple consisting of the corresponding quotient curve and the map to the quotient curve
// - The basis of cuspforms used for the canonical embedding of X
// - the infinity cusp on X (as a rational point)

// X_0(N) should be of genus > 1 and non-hyperelliptic
// There are no restrictions on the quotient.

eqs_quos := function(N, list_als);
    X, ws,NB,cusp := all_diag_X(N);
    A<[x]> := AmbientSpace(X);
    al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
    pairs := [* *];
    for seq_al in list_als do
        seqw := [ws[i] : i in [1..#ws] | al_inds[i] in seq_al];
        seqw_M := [Matrix(w) : w in seqw];
        Ss := [Diagonal(Mw) : Mw in seqw_M];
        n := #Ss[1];
        g_quo := genus_quo(N, seq_al);
        is_hyp := is_hyper_quo(N, seq_al);
        
        PS0 := SetToSequence(Subsets({1..n}));
       
        if g_quo gt 1 and is_hyp eq false then // can use canonical embeding for quotient curve.
             pos_coords := &meet[{P : P in PS0 | #P gt 0 and &+[s[i] : i in P] eq #P} : s in Ss];  
             pos_seq := SetToSequence(pos_coords);
             sizes := [#c : c in pos_seq];
             _,position := Maximum(sizes);
             coords := Sort(SetToSequence(pos_seq[position]));
             Bpl := [NB[i] : i in coords];
             Y := canonic(Bpl);
             rho := map< X ->Y | [x[i] : i in coords] >;
             pairs := pairs cat [* <Y, rho> *];
             
        else                           // cannot use canonical embedding for quotient curve
                                       // we use a projection map instead (if possible)
                                       // quotient is either elliptic or hyperelliptic
            PS := [P : P in PS0 | #P gt 1];
            consts := &meet[{P : P in PS | &+[s[i] : i in P] eq #P or &+[s[i] : i in P] eq -#P} : s in Ss];
            con := SetToSequence(consts);
            sizes := [#c : c in con];
            _,pos := Maximum(sizes);
            coords := Sort(SetToSequence(con[pos]));
            P := ProjectiveSpace(Rationals(),#coords-1);
            proj := map<A->P|[x[i] : i in coords]>;
            Y1 := Curve(proj(X));
            genY1 := Genus(Y1);
            if genY1 eq g_quo then 
                assert Dimension(Y1) eq 1 and IsIrreducible(Y1);
                Y := Y1;
                genY := genY1;
                rho1 := map<X->Y | [x[i] : i in coords]>;
            else Y, rho1 := CurveQuotient(AutomorphismGroup(X,seqw));  // longer, only used if projection map does not work.
                assert Dimension(Y) eq 1 and IsIrreducible(Y); 
                genY := Genus(Y);
            end if;
    

             if  genY gt 1 then // curve is hyperelliptic
                 htf, Z, rho2 := IsHyperelliptic(Y);
                 assert htf;           
                 H, rho3 := SimplifiedModel(Z);
                 rho := rho1*rho2*rho3;
                 pairs := pairs cat [* <H,rho>*];
             elif genY eq 0 then 
                 pairs := pairs cat [* <Y, rho>*];
             else assert Genus(Y) eq 1 and g_quo eq 1;
                 assert Degree(rho1) eq #AutomorphismGroup(X,seqw); // make sure we haven't quotiented out by an extra isogeny
                 Z, rho2 := EllipticCurve(Y,rho1(cusp));
                 E, rho3 := SimplifiedModel(Z);
                 rho := rho1*rho2*rho3;
                 assert IsZero(N mod Conductor(E));
                 pairs := pairs cat [*< E, rho >*];
             end if;
        end if;
    end for;

    return X, ws, pairs, NB, cusp;
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////
/// Examples /// 
////////////////
/*
// Example 1 //

// 1a) 
// Let's start by computing a model for X074.
// There are 3 AL involutions. 
// We compute them, but we do not compute any quotient information.

time X, ws, pairs, NB, cusp := eqs_quos(74,[]);  // 0.6 seconds

// pairs is an empty list. 
// NB is the basis of cusp forms we have used for the canonical embedding.
// cusp is the infinty cusp.


// 1b) This time we compute the quotients by each involution

time X, ws, pairs, NB, cusp := eqs_quos(74,[[2],[37],[74]]);  // 0.8 seconds

// pairs consist of three tuples of a curve and a map
// the first curve is X_0(74) / w_2

Y := pairs[1][1]; 
assert Genus(Y) eq 4;
rho := pairs[1][2];
PointSearch(Y,1000); // we find 3 rational points

// the third curve is X_0(74) / w_74.
// it is hyperelliptic.

Y := pairs[3][1]; // Hyperelliptic Curve defined by y^2 = x^6 - 2*x^5 - x^4 - x^2 - 2*x + 1
assert Genus(Y) eq 2;
Pts := Points(Y : Bound := 1000); // we find 6 rational points.
// the curve has rank 1 and genus 2
// we should be able to check that this gives all the rational points.
// let's do this.
J := Jacobian(Y);
G := J ! [Pts[1],Pts[6]];
Order(G); // this is 3, so the point has finite order...
// let's pick another point in the Jacobian
G := J ! [Pts[1],Pts[5]];
assert Order(G) eq 0;
assert #Chabauty(G) eq 6;  // we have found all the rational points.

// 1c)  This time we quotient by the full group of Atkin-Lehner involutions.

time X, ws, pairs, NB, cusp := eqs_quos(74,[[2,37]]);  // 1 second

// this time the quotient curve is an elliptic curve

assert Conductor(pairs[1][1]) eq 37;

rho := pairs[1][2]; // this is the quotient map
// the quotient map is given by a composition of 3 different maps in this case
// if we would like a single map, then we can define
phi := Expand(rho);


// replacing [2,37] by [2,74] or [37,74] or [2,37,74] will give the same output
// (since the group generated by the AL involutions is a C2 x C2.

/////////////////////////////////////////////////////////////////////////////////

// Example 2 //

// We'll try X_0(136) now
// 136 = 8*17

time X, ws, pairs, NB, cusp := eqs_quos(136,[[ 8,17,136 ]]);  // 10 seconds

assert Genus(X) eq 15; // this is quite high, so it took a little longer.
Y := pairs[1][1]; // Hyperelliptic Curve defined by y^2 = x^8 - 6*x^6 - 4*x^5 + x^4 + 4*x^3 + 20*x^2 + 16*x
// this is a genus 3 hyperelliptic curve as expected.

// We can look at an intermediate curve too

time X, ws, pairs, NB, cusp := eqs_quos(136,[[ 8 ]]);  // 9 seconds
Y := pairs[1][1];
assert Genus(Y) eq 7;

// Example 3 //

// Here is an example with X_0(p). 
// We'll do p = 163

time X, ws, pairs, NB, cusp := eqs_quos(163,[[ 163 ]]);  // 53 seconds, quite long
assert Genus(X) eq 13;
Y := pairs[1][1];
assert Genus(Y) eq 6;
// The part that takes a long time is computing the model for X_0(163) in this case
// Once this is done the rest is fast.
time X := all_diag_X(163); // 53 seconds
// although if you run this code a second time it is much faster (4 seconds) due to some stored computations

// Example 4 //

// An example with a larger group of automorphisms.

time X, ws, pairs, NB, cusp := eqs_quos(60,[[3],[4],[5],[3,4],[4,5],[3,5],[3,4,5]]); // 1 second

Y := pairs[7][1];
assert Genus(Y) eq 0;  // we have a genus 0 quotient here

for pair in pairs do
    Y := pair[1];
    Genus(Y);
    if Genus(Y) eq 1 then
       Conductor(Y);
    end if;
end for;
// We get 4,3,4,2,1,1,0 for the genera
// The two elliptic curves have conductors 30 and 20 (which is as expected).

// Example 5 // 

// We do a prime power level

time X, ws, pairs, NB, cusp := eqs_quos(125,[[125]]); // 0.8 seconds

Y := pairs[1][1]; // Hyperelliptic Curve defined by y^2 = x^6 + 2*x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 8*x+ 1
assert Genus(Y) eq 2;

// Example 6 //

// Let's check a model against Galbraith's calculations for a non-hyperelliptic quotient
// (It is easier to check with hyperelliptic quotients)

time X, ws, pairs, NB, cusp := eqs_quos(169,[[169]]);  // 1 second
Y := pairs[1][1];
// this matches Galbraith's model exactly in this case.

*/

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++


///////////////////////////////////////////////////////
////////////////// FURTHER FUNCTIONS //////////////////
///////////////////////////////////////////////////////


// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////////////
/// change_basis_mat /// 
////////////////////////

// Input: bases B and NB for the same space of cusp forms
// Output: Change of basis matrix from one to the other 
// (where space of cusp forms is viewed as a Vector space)

change_basis_mat := function(B, NB);
    C := CuspForms(Level(B[1]));
    V,phi,psi := RSpace(C);
    BV := [psi(b) : b in B];
    NBV := [psi(nb) : nb in NB];
    M := ChangeRing(Matrix(BV), Rationals());
    NM := ChangeRing(Matrix(NBV), Rationals());
    T := M*NM^(-1);
    return T;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////////
/// coord_change /// 
////////////////////

// Input: bases B and NB for the same space of cusp forms
// Output: curves X and NX corresponding to these bases and the coordinate change map between the curves
// The level N should be such that X_0(N) is non-hyperelliptic of genus > 2.
// The basis B should be a 'nice' basis for which one can compute the canonical embedding in a reasonable time

coord_change := function(B, NB);
    X := canonic(B);
    T := change_basis_mat(B,NB);
    A<[x]> := AmbientSpace(X);
    var := Dimension(A)+1;
    R<[x]> := PolynomialRing(Rationals(), var);
    eqX := DefiningEquations(X);
    coord_change_eqs := [&+[(T^(-1))[i,j]*x[j] : j in [1..var]] : i in [1..var]];
    coord_change_eqs_inv := [&+[T[i,j]*x[j] : j in [1..var]] : i in [1..var]];
    coord_change_R := hom<R->R | coord_change_eqs_inv >;

    new_eqX := [coord_change_R(ee) : ee in eqX];
    NX := Curve(ProjectiveSpace(R),new_eqX); 
    coord_change_map := map< X -> NX | coord_change_eqs>;
    return X, NX, coord_change_map;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

///////////////////
/// level_basis /// 
///////////////////

// Input: N and M
// Output: a basis for the cusp forms at level N. 
// N must be divisible by M
// The code chooses a diagonalised basis for the cusp forms at level M
// and extends this to a basis at level N 
// ( uses the inclusion (S_2(M) -> S_2(N)) )

level_basis := function(N, M);
    CN := CuspForms(N);
    V,phi,psi := RSpace(CN);
    BM := all_diag_basis(M); // diagonal basis of cusp forms at level M
    U := sub<V | [psi(f) : f in BM]>; // corresponding subspace
    BU := [psi(bb) : bb in BM];
    VQ := ChangeRing(V, Rationals());
    UQ := ChangeRing(U, Rationals());
    BUQ := [UQ ! bb : bb in BU];
    BVQ := ExtendBasis(BUQ, VQ);
    denom := Denominator(Matrix(BVQ));
    BV := [  V ! [denom*bb[i] : i in [1..Dimension(VQ)]] : bb in BVQ];
    BNM := [phi(bb) : bb in BV];
    return BNM, BM;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

///////////////////
/// level_basis /// 
///////////////////

// Input: X, N, M
// X is a diagonalised model for X_0(N), M divides N
// Output: 
// - A map from X = X_0(N) to X_0(M) 
// - The curve X_0(M)
// - A different model for X_0(N) for which the quotient map is just a projection map
// - The change of coordinate map from the current model to the new model
// - The quotient (projection) map from the new model to the quotient curve

// X_0(N) and X_0(M) must both be of genus > 2 and non-hyperelliptic.
// I am looking to see what can be done in the quotient is an elliptic curve or hyperelliptic.

level_quo := function(X, N, M);
    BNM, BM := level_basis(N, M);
    B := all_diag_basis(N);
    _, Xl , coord := coord_change(B, BNM);
    XM := canonic(BM);
    A<[x]> := AmbientSpace(Xl);
    proj := map< Xl-> XM | [x[i] : i in [1..#BM]] >;
    phi := map< X -> XM | DefiningEquations(Expand(coord*proj)) >;
    return phi, XM, Xl, coord, proj;
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/*

///////////////
/// Example /// (see above for examples of using eqs_quo)
/////////////// (here we see how to use level_quo)

// We will consider an example with N = 86 and M = 43. 
// The curve X_0(43) is non-hyperelliptic of genus 3.
// the curve X_0(86) is non-hyperelliptic of genus 10.

time X, ws, pairs, NB, cusp := eqs_quos(86,[[2], [43], [86], [2,43]]); // 4 seconds

// This gives us the curve X_0(86) as well as 4 quotients.
// The first 3 quotients are by individual AL involutions
// The fourth is by the full AL group

// We now want the map to X_0(43) too.

time phi, X_0_43, Xl, coord, proj := level_quo(X, 86, 43); // 1.8 seconds

phi; // we get nice equations for phi

// Mapping from: Crv: X to Crv: X_0_43
// with equations : 
// 1/2*x[1] + 1/2*x[6] - 2*x[7] - x[8]
// 1/2*x[2] + x[3] + 1/2*x[9] - x[10]
// 1/2*x[3] - 1/2*x[4] + x[5] + 1/2*x[10]

time assert Degree(phi) eq 3; // 3.5 seconds, sanity check 

X_0_43; // we get nice equations for the quotient curve too

// Curve over Rational Field defined by x[1]^4 + 2*x[1]^2*x[2]^2 + 8*x[1]^2*x[2]*x[3] + 16*x[1]^2*x[3]^2 - 3*x[2]^4 + 8*x[2]^3*x[3] + 16*x[2]^2*x[3]^2 + 48*x[2]*x[3]^3 + 64*x[3]^4


// Xl is a different model for X_0(86)
// it's equations are more complicated
// The quotient map, proj, to X_0(43) is just a projection map though
// So it could be easier to work with for certain things
// The coord map allows us to pass from one model to the other

// The map phi can be used to compute the j-invariant of a point on X_0(86) 
// by passing to X_0(43), as the j-map factors via phi.

*/








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
    cleardenom := LCM([Denominator(x) : x in Eltseq(T)]);
    NB := [&+[cleardenom*T[i,j]*B[j] : j in [1..g]] : i in [1..g]];  // can change 1   
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
<85, [85]>,
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

/////////////////////////
/// atkinlehnersubgrp /// 
/////////////////////////

// Input: The level N, and a list of Hall divisors of N representing the corresponding Atkin-Lehner involutions.
// Output: The list of all (non-trivial) Hall divisors of N corresponding to all the Atkin-Lehner involutions in the subgroup generated.

function atkinlehnersubgrp(N,seq);
	boo := true;
	subgrp := seq;
	while boo do
		for a in subgrp do
			for b in subgrp do
				c := ExactQuotient(a*b,GCD(a,b)^2);
				if c ne 1 and not c in subgrp then
					Append(~subgrp,c);
					boo := true;
					break a;
				end if;
			end for;
			boo := false;
		end for;
	end while;
	return Sort(subgrp);
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
        elif g_quo gt 2 and N in hyper_stars then
            al_group := atkinlehnersubgrp(N,seq_al);
            if #al_group eq 2^(#PrimeFactors(N))-1 then 
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
// - A model for X_0(N), with all the Atkin-Lehner involutions diagonalised when X_0(N) is non-hyperelliptic of genus > 1
// - The Atkin-Lehner involutions on X_0(N) (listed in ascending order by index) (diagonalised if X_0(N) is non-hyperelliptic of genus > 1)
// - A list: for each sequence of AL-indices, a tuple consisting of the corresponding quotient curve and the map to the quotient curve
// - The basis of cuspforms used for the canonical embedding of X when X_0(N) is non-hyperelliptic of genus > 1, otherwise the q-expansions of generators are given
// - the infinity cusp on X (as a rational point)

// If X_0(N) has genus 0 or 1, then pairs will be empty

// auxiliary function to compare the size of two sets

size_comp := function(s1,s2);
    if #s1 gt #s2 then return 1;
    elif #s1 lt #s2 then return -1;
    else return 0; end if;
end function;

eqs_quos := function(N, list_als);
    // Start with case in which X_0(N) is genus 0, elliptic or hyperelliptic.
    if N in [1,2,3,4,5,6,7,8,9,10,12,13,16,18,25] cat  [ 11,14,15,17,19,20,21,24,27,32,36,49] cat [22,23,26,28,29,30,31,33,35,37,39,40,41,46,47,48,50,59,71] then 
        X := SmallModularCurve(N);
        al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
        ws := [AtkinLehnerInvolution(X,N,d) : d in al_inds];
        pairs := [* *];
        if Genus(X) gt 1 then 
            for seq_al in list_als do
                seqw := [ws[i] : i in [1..#ws] | al_inds[i] in seq_al];
                Y, rho := CurveQuotient(AutomorphismGroup(X,seqw));
                pairs := pairs cat [* <Y, rho> *];
            end for;
        end if;

        L<q> := LaurentSeriesRing(Rationals());
        NB := qExpansionsOfGenerators(N, L, 5*N);    
        cusp := Cusp(X, N, N);
        return X, ws, pairs, NB, cusp;
    end if;     
    // Now consider case in which X is canonically embedded
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
            con3 := [c : c in con | #c gt 2];
            maxcon3 := con3;
            for s,e in con3 do
                if s subset e and s ne e then
                    Exclude(~maxcon3,s);
                end if;
            end for;
            maxcon3 := Sort(maxcon3, size_comp);
            genY1 := -1;
            for i in [1..#maxcon3] do
                coords := Sort(SetToSequence(maxcon3[i]));
                P := ProjectiveSpace(Rationals(),#coords-1);
                proj := map<A->P|[x[i] : i in coords]>;
                Y1 := Curve(proj(X));
                genY1 := Genus(Y1);
                if genY1 eq g_quo then 
                    assert Dimension(Y1) eq 1 and IsIrreducible(Y1);
                    Y := Y1;
                    genY := genY1;
                    rho1 := map<X->Y | [x[i] : i in coords]>;
                    break;
                end if;
            end for;
            if genY1 ne g_quo then 
                Y, rho1 := CurveQuotient(AutomorphismGroup(X,seqw));  // longer, only used if projection map does not work.
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
                 pairs := pairs cat [* <Y, rho1>*];
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


// (Filip) checks whether X_0(n) has a degree 2 map to a hyperlliptic curve
is_bihyperelliptic:=function(n);
lst:= Divisors(n) ;
lst2:=[];
for a in lst do
if GCD(a, n div a) eq 1 then lst2:=lst2 cat [a]; end if;
end for;
tr:=false;
for w in lst2 do
if w ge 2 then
if (is_hyper_quo(n,[w])) then return true, w, genus_quo(n,[w]); end if;
end if;
end for;
return false;
end function;

// (Filip) returns the genera of all X_0(n)/w_d
genera_quo:=procedure(n);
lst:= Divisors(n) ;
lst2:=[];
for a in lst do
if GCD(a, n div a) eq 1 then lst2:=lst2 cat [a]; end if;
end for;
for w in lst2 do
if w ge 2 then
w, genus_quo(n,[w]);
end if;
end for;
end procedure;


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

time X, ws, pairs, NB, cusp := eqs_quos(74,[[2],[37],[74]]);  // 1.5 seconds

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

time X, ws, pairs, NB, cusp := eqs_quos(74,[[2,37]]);  // 1.2 seconds

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

time X, ws, pairs, NB, cusp := eqs_quos(60,[[3],[4],[5],[3,4],[4,5],[3,5],[3,4,5]]); // 5 seconds

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

time X, ws, pairs, NB, cusp := eqs_quos(125,[[125]]); // 1 second

Y := pairs[1][1]; // Hyperelliptic Curve defined by y^2 = x^6 + 2*x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 8*x+ 1
assert Genus(Y) eq 2;

// Example 6 //

// Let's check a model against Galbraith's calculations for a non-hyperelliptic quotient
// (It is easier to check with hyperelliptic quotients)

time X, ws, pairs, NB, cusp := eqs_quos(169,[[169]]);  // 1 second
Y := pairs[1][1];
// this matches Galbraith's model exactly in this case.

// Example 7 //

// Here is an example with X_0(N) hyperelliptic.
// In this case we just use the SmallModularCurve package functionalities

time X, ws, pairs, NB, cusp := eqs_quos(28, [[4], [7], [28], [4,28]]);

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
/// level_quo   /// 
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





////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////
//// jmap //////
////////////////

// Input: X, N
// X is a diagonalised model for X_0(N) when X is non-hyperelliptic of Genus > 1. Otherwise X is the small modular curve model.
// Output: Equations for the j-map as a map to P^1, a tuple of its numerator and denominator

// When X is non-hyperelliptic of genus > 1 it should be obtained from all_diag_X or eqs_quos
// If you want to run this code using a different model for X of this type then you can by changing the first few lines appropriately

// The following code is adapted from code sent to me (Philippe) by Jeremy Rouse

// An auxiliary function to help simplify matrices using LLL reduction

function nicefy(M)
  M0, T := EchelonForm(M);
  ee := Eltseq(M0);
  denom := LCM([ Denominator(ee[i]) : i in [1..#ee]]);
  M2 := Matrix(Integers(),NumberOfRows(M),NumberOfColumns(M),[ denom*ee[i] : i in [1..#ee]]);
  AA := Saturation(M2);
  chk, mult := IsConsistent(ChangeRing(M2,Rationals()),ChangeRing(AA,Rationals()));
  curbat := denom*mult*T;
  newlatbasismat, change := LLL(AA : Proof := false);
  finalbat := ChangeRing(change,Rationals())*curbat;
  return finalbat;
end function;

/////////////////////////////////////////////////////////

jmap := function(X, N);
    // Start with case in which X_0(N) is genus 0, elliptic or hyperelliptic.
    if N in [1,2,3,4,5,6,7,8,9,10,12,13,16,18,25] cat  [ 11,14,15,17,19,20,21,24,27,32,36,49] cat [22,23,26,28,29,30,31,33,35,37,39,40,41,46,47,48,50,59,71] then 
        jj := jInvariant(X,N);
        num := Numerator(jj);
        denom := Denominator(jj);
        jmap := map<X -> ProjectiveSpace(Rationals(),1) | [num, denom] >;
        return jmap, <num, denom>;  
    end if;
    // Now consider case in which X is canonically embedded

    B := all_diag_basis(N);
    g := #B;
    prec := 5*N;
    maxprec := prec+1;

    L<q> := LaurentSeriesRing(Rationals());

    E4 := Eisenstein(4,q : Precision := prec);
    E6 := Eisenstein(6,q : Precision := prec);
    j := 1728*E4^3/(E4^3 - E6^2);
    val := Valuation(j);
    degj := N*(&*[1+1/p : p in PrimeFactors(N)]);

    Bexp:=[L!qExpansion(B[i],maxprec) : i in [1..g]];

    r := Ceiling((degj / (2*(g-1))) + 1/2); // When degj / 2g-1 +1/2 is an integer, we should really take this +1, but for N < 200 I found that this worked in these cases (and is slightly nicer) so I will stick with it. For the other functions, we do need and take the +1 in these cases.
    maxd := r;
    R<[x]> := PolynomialRing(Rationals(),g);
    vars := [R.i : i in [1..g]];
    canring := [ <Bexp,vars>];

    for d in [2..maxd] do
        dimen := (2*d-1)*(g-1);
        fouriermat := ZeroMatrix(Rationals(),0,(maxprec-1));
        prds := [ <i,j> : i in [1..g], j in [1..#canring[d-1][1]]];
        done := false;
        curind := 1;
        newfourier := [];
        newvars := [];
        while (done eq false) do
            e1 := prds[curind][1];
            e2 := prds[curind][2];
            pp := Bexp[e1]*canring[d-1][1][e2];
            vecseq := &cat[ Eltseq(Coefficient(pp,j)) : j in [d..d+maxprec-2]];
            tempfouriermat := VerticalJoin(fouriermat,Matrix(Rationals(),1,(maxprec-1),vecseq));
            if Rank(tempfouriermat) eq NumberOfRows(tempfouriermat) then
                fouriermat := tempfouriermat;
                Append(~newfourier,pp);
                Append(~newvars,canring[1][2][e1]*canring[d-1][2][e2]);
                if NumberOfRows(tempfouriermat) eq dimen then
                    done := true;
	                Append(~canring,<newfourier,newvars>);
                end if;
            end if;
            if (done eq false) then
                curind := curind + 1;
                if (curind gt #prds) then
                    done := true;
	                Append(~canring,<newfourier,newvars>);
                end if;
            end if;
        end while;
    end for;

    jmat := ZeroMatrix(Rationals(),0,(maxprec-2));
    for i in [1..#canring[maxd][1]] do
        pp := j*canring[maxd][1][i];
        vecseq := &cat[ Eltseq(Coefficient(pp,j)) : j in [maxd+val..maxd+val+maxprec-3]];
        jmat := VerticalJoin(jmat,Matrix(Rationals(),1,(maxprec-2),vecseq));  
    end for;
    for j in [1..#canring[maxd][1]] do
        vecseq := &cat[ Eltseq(-Coefficient(canring[maxd][1][j],i)) : i in [maxd+val..maxd+val+maxprec-3]];
        jmat := VerticalJoin(jmat,Matrix(Rationals(),1,(maxprec-2),vecseq));
    end for;

    NN1 := NullSpace(jmat);
    M1 := Matrix(Basis(NN1));
    cb1 := nicefy(M1);
    jsol := (cb1*M1)[1];

    felt := &+[ jsol[i+#canring[maxd][1]]*canring[maxd][2][i] : i in [1..#canring[maxd][1]]]/&+[ jsol[i]*canring[maxd][2][i] : i in [1..#canring[maxd][1]]];

    num := Numerator(felt);
    denom := Denominator(felt);
    jmap := map<X -> ProjectiveSpace(Rationals(),1)|[num,denom]>;
   
    // checks for correctness
    mfnum := Evaluate(num,Bexp);
    mfdenom := Evaluate(denom,Bexp);
    elt := j - (mfnum/mfdenom);
    assert prec gt 2*degj+1; // If this fails then increase precision
    assert IsWeaklyZero(elt); // If this fails then increase precision
    return jmap, <num, denom>;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

///////////////
/// Example /// (see above for examples of using eqs_quo)
/////////////// (here we see how to use jmap)

// We will compute equations for the j-map on X_0(67)

/*
X, _, _, _, cusp := eqs_quos(67, []);

time j, num_denom := jmap(X,67);  // 6 seconds

pts := PointSearch(X,10);
for p in pts do 
    j(p);
end for;

// we see that we have two cusps and one point with j-invariant -147197952000 = -2^15 3^3 5^3 11^3
// this is as expected
*/

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////////
//// xy_coords ////
/////////////////////

// Input: X, N, M
// X is a diagonalised model for X_0(N) (for X non-hyperelliptic of Genus > 1)
// X_0(M) must be elliptic or hyperelliptic (see level_quo otherwise)
// Output: 
// 1. x-coordinate map as a quotient of polynomials
// 2. x-coordinate map as a quotient of polynomials
// 3. X_0(M) (the small modular curve model obtained from eqs_quos

// If you want to try and construct the map as a map to X_0(M), or its ambient projective space, then you can do so using the function construct_map_to_quotient which follows this function.
// However, this can be very slow... 
// So I prefer to work with these x- and y-maps
// See the examples later for how to use the x- and y-maps to compute the image of points.

// Note that the cusps are in the wrong affine chart to be evaluated at the x- and y-maps

// The following code is adapted from code sent to me (Philippe) by Jeremy Rouse

xy_coords := function(X,N,M);
    B := all_diag_basis(N);
    g := #B;
    degN := N*(&*[1+1/p : p in PrimeFactors(N)]);
    degM := M*(&*[1+1/p : p in PrimeFactors(M)]);
    deg_map := Integers() ! (degN / degM);
    
    
    prec := 5*N;
    maxprec := prec+1;
    Y := eqs_quos(M, []);

    L<q> := LaurentSeriesRing(Rationals());
    Bexp:=[L!qExpansion(B[i],maxprec) : i in [1..g]];
    R<[x]> := PolynomialRing(Rationals(),g);
    vars := [R.i : i in [1..g]];

    qexps := qExpansionsOfGenerators(M, L, prec);
    for f in qexps do
        val := Valuation(f);
        if f eq qexps[1] then 
            degf := 2*deg_map;
        else degf := Degree(HyperellipticPolynomials(Y))*deg_map;
        end if;
        
        r1 := (degf / (2*(g-1))) + 1/2;
        if IsIntegral(r1) then 
           r := Integers()! (r1+1);
        else r := Ceiling(r1);
        end if;
        maxd := r;
        
        canring := [ <Bexp,vars>];
        for d in [2..maxd] do
            dimen := (2*d-1)*(g-1);
            fouriermat := ZeroMatrix(Rationals(),0,(maxprec-1));
            prds := [ <i,j> : i in [1..g], j in [1..#canring[d-1][1]]];
            done := false;
            curind := 1;
            newfourier := [];
            newvars := [];
            while (done eq false) do
                e1 := prds[curind][1];
                e2 := prds[curind][2];
                pp := Bexp[e1]*canring[d-1][1][e2];
                vecseq := &cat[ Eltseq(Coefficient(pp,j)) : j in [d..d+maxprec-2]];
                tempfouriermat := VerticalJoin(fouriermat,Matrix(Rationals(),1,(maxprec-1),vecseq));
                if Rank(tempfouriermat) eq NumberOfRows(tempfouriermat) then
                    fouriermat := tempfouriermat;
                    Append(~newfourier,pp);
                    Append(~newvars,canring[1][2][e1]*canring[d-1][2][e2]);
                    if NumberOfRows(tempfouriermat) eq dimen then
                        done := true;
	                    Append(~canring,<newfourier,newvars>);
                    end if;
                end if;
                if (done eq false) then
                    curind := curind + 1;
                    if (curind gt #prds) then
                        done := true;
	                    Append(~canring,<newfourier,newvars>);
                    end if;
                end if;
            end while;
        end for;

        fmat := ZeroMatrix(Rationals(),0,(maxprec-2));
        for i in [1..#canring[maxd][1]] do
            pp := f*canring[maxd][1][i];
            vecseq := &cat[ Eltseq(Coefficient(pp,j)) : j in [maxd+val..maxd+val+maxprec-3]];
            fmat := VerticalJoin(fmat,Matrix(Rationals(),1,(maxprec-2),vecseq));  
        end for;
        for j in [1..#canring[maxd][1]] do
            vecseq := &cat[ Eltseq(-Coefficient(canring[maxd][1][j],i)) : i in [maxd+val..maxd+val+maxprec-3]];
            fmat := VerticalJoin(fmat,Matrix(Rationals(),1,(maxprec-2),vecseq));
        end for;

        NN1 := NullSpace(fmat);
        M1 := Matrix(Basis(NN1));
        cb1 := nicefy(M1);
        fsol := (cb1*M1)[1];

        felt := &+[ fsol[i+#canring[maxd][1]]*canring[maxd][2][i] : i in [1..#canring[maxd][1]]]/&+[ fsol[i]*canring[maxd][2][i] : i in [1..#canring[maxd][1]]];

        num := Numerator(felt);
        denom := Denominator(felt);
        // checks for correctness
        mfnum := Evaluate(num,Bexp);
        mfdenom := Evaluate(denom,Bexp);
        elt := f - (mfnum/mfdenom);
        assert prec gt 2*degf+1;  // If this fails then increase precision
        assert IsWeaklyZero(elt); // If this fails then increase precision
        if f eq qexps[1] then 
            xnum := num;
            xdenom := denom;
            xx := xnum / xdenom;
        else ynum := num;
             ydenom := denom;
             yy := ynum / ydenom;
        end if;
    end for;

    return xx, yy, Y;
end function;
    
///////////////////////////////////
//// construct_map_to_quotient ////
///////////////////////////////////

// As explained above, we can try and construct a map to X_0(M), or its ambient projective space if we really want to.
// The following function takes as input X_0(N), X_0(M), and the x and y expressions from above 
// The final input paramter is a true or false Boolean.
// if true then the codomain will be set to X_0(M)
// if false then the codomain will be set to the ambient projective space of X_0(M), this is faster

// Warning! This is very slow / does not terminate in a reasonable time if X_0(M) is hyperelliptic and tf = true
// Do not try and evaluate the map at cusps

construct_map_to_quotient := function(X,Y,xx,yy,tf);
    if tf then 
        map := map<X -> Y | [xx,yy,1]>;
    else map := map<X -> AmbientSpace(Y) | [xx,yy,1] >;
    end if;
    return map;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/*

////////////////
/// Examples /// (we see how to work with xy_coords)
////////////////

// We will use the following function, taken from "pullbacks.m" in these examples.
// For convenience we have included the function again here

pullback_points := function(X, pairs, N, bound);
    places := [];
    for i in [i : i in [1..#pairs]] do
        pair := pairs[i];
        Y := pair[1];
        rho := pair[2];
        if Genus(Y) eq 0 then 
            continue;
        elif IsHyperelliptic(Y) or Genus(Y) eq 1 then 
            pts := Points(Y : Bound := bound);
        else pts := PointSearch(Y, bound);
        end if;
        for R in pts do 
            place := Pullback(rho, Place(R));
            dec := Decomposition(place);
            if #dec eq 2 or (#dec eq 1 and dec[1][2] eq 2) then  // two rat points or a double rat point so ignore
                continue;
            else places := places cat [dec[1][1]];
            end if;
        end for;
     end for;
        return places;
end function;


// Example 1 (elliptic quotient)

N := 85;
M := 17;

al_seq := [ [m] : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
X, _, pairs := eqs_quos(N, al_seq);  // This is the curve X_0(85)
assert Genus(X) eq 7;

// The curve X_0(17) is an elliptic curve

time xx, yy, E := xy_coords(X,N,M); // 0.9 seconds

// In this case, since X_0(M) is elliptic and the genus of X_0(N) is not too large

// We can construct the map to X_0(M) relatively quickly if we really want to

time Pmap := construct_map_to_quotient(X,E,xx,yy,false); //0.001
Codomain(Pmap); // Projective space of dimension 2 over Rational Field
time Emap := construct_map_to_quotient(X,E,xx,yy,true); // 4.6 seconds
assert Codomain(Emap) eq E;
// However, if we want to work with points, we are best off sticking with the x and y coordinate expressions

// Let's compute some quadratic points on X_0(85) and evaluate our map on them
// We use the "pullback_points" function, available in the "pullbacks.m" file

time pullbacks := pullback_points(X,pairs,N, 10000); // 24 seconds

assert #pullbacks eq 6;

pl := pullbacks[2]; // this is a place on X
K<d> := ResidueClassField(pl);
assert Discriminant(Integers(K)) eq -4; // So K is the field Q(i)

// Pl is Place at (-1/2 : -1/2 : 1/192*d : -1/96*d : 1/96*d : -1/192*d : 1)

EK := ChangeRing(E,K);
ptK := Eltseq(RepresentativePoint(pl));  // Sequence of coordinates of the point
RK := [Evaluate(xx,ptK), Evaluate(yy,ptK), 1];  // The image point
SK := EK ! RK; // the image point on EK is (1/24*(d - 48) : 1/12*(-d - 36) : 1)

// Warning! Trying to base change Emap to K and compute the image directly is too slow
// In this example one can base change Pmap to K and use it
// but in more complicated examples or in the hyperelliptic case it does not work

// Here, we used a place as a starting point, but the same works if we have a point:

XK := ChangeRing(X,K);
QK := XK ! ptK; // Say this is out starting point.

qK := Eltseq(QK);
R2K := [Evaluate(xx,qK), Evaluate(yy,qK), 1];  
S2K := EK ! R2K;

assert S2K eq SK;  // same as before

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// Example 2 (hyperelliptic quotient)

// This example will be very similar to Example 1

N := 82;
M := 41;

al_seq := [ [m] : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
X, _, pairs := eqs_quos(N, al_seq);  // This is the curve X_0(82)
assert Genus(X) eq 9;

// The curve X_0(41) is a hyperelliptic curve of genus 3

time xx, yy, H := xy_coords(X,N,M); // 0.5 seconds

time Pmap := construct_map_to_quotient(X,H,xx,yy,false); // 0.1 seconds

// In this case it is fast to compute the map to weighted projective space

Codomain(Pmap); // Projective Space of dimension 2 over Rational Field with grading 1, 4, 1

// Warning! Do not try to make H the codomain with this example
// It will be too slow

// Again, we use the "pullback_points" function, available in the "pullbacks.m" file to access some quadratic points

time pullbacks := pullback_points(X,pairs,N, 10000); // 14.8 seconds
assert #pullbacks eq 6;

// Let's compute the image of all of these points.

// Warning! Do not try to do this by base changing Pmap to a quadratic field
// it is too slow. 
// It is much faster to work with the x- and y-coordinates!

time for pl in pullbacks do  // 0.01 seconds, this is almost instantaneous
    K := ResidueClassField(pl);
    print(Discriminant(Integers(K)));
    HK := BaseChange(H,K);
    ptK := Eltseq(RepresentativePoint(pl));
    RK := [Evaluate(xx,ptK), Evaluate(yy,ptK), 1];
    SK := HK ! RK;
    print(SK);
end for;

// Here is the output
// Note that the field K and "K.1" are different for the different points

// -4
// (-1 : 1/512*(-159*d + 1272) : 1)
// -4
// (1 : 1/24*(K.1 + 88) : 1)
// -4
// (1 : 1/128*(-159*K.1 + 605) : 1)
// -8
// (0 : 3/2*K.1 : 1)
// -4
// (1 : 1/24*(K.1 + 88) : 1)
// -8
// (0 : 3/2*K.1 : 1)


///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// Example 3 (large genus hyperelliptic quotient)

N := 118;
M := 59;

time X := eqs_quos(N, []); // 4.7 seconds
assert Genus(X) eq 14;
// X_0(M) is hyperelliptic of genus 5

time xx, yy, H := xy_coords(X,N,M); // 1.4 seconds

// with this larger genus example, we can see how even the map to the ambient projective space is slow
// time Pmap := construct_map_to_quotient(X,H,xx,yy,false); // 193 seconds
// not only is constructing the map slow, but trying to evaluate it at points would be slow too
// it is best to stick with the x and y expressions as in Examples 1 and 2

*/


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////////
//// gen_0_quo ///// // see xy_coords and level_quo for other level quotients
////////////////////

// Input: X, N, M
// X is a diagonalised model for X_0(N) for X non-hyperelliptic of Genus > 1. 
// X_0(M) is a genus 0 modular curve
// Output: Equations for the map X_0(N) -> X_0(M) = P^1 and a tuple of its numerator and denominator, and the curve X_0(M)

// X should be obtained from all_diag_X or eqs_quos
// If you want to run this code using a different model for X of this type then you can by changing the first few lines appropriately

// The following code is adapted from code sent to me (Philippe) by Jeremy Rouse


gen_0_quo := function(X, N, M);
   
    B := all_diag_basis(N);
    g := #B;
    prec := 5*N;
    maxprec := prec+1;

    degN := N*(&*[1+1/p : p in PrimeFactors(N)]);
    degM := M*(&*[1+1/p : p in PrimeFactors(M)]);
    degf := Integers() ! (degN / degM);
    
    L<q> := LaurentSeriesRing(Rationals());
    Y := eqs_quos(M, []);
    assert Genus(Y) eq 0;
    
    Bexp:=[L!qExpansion(B[i],maxprec) : i in [1..g]];
    f := qExpansionsOfGenerators(M, L, prec)[1];
    val := Valuation(f);
    r1 := (degf / (2*(g-1))) + 1/2;
    if IsIntegral(r1) then 
       r := Integers()! (r1+1);
    else r := Ceiling(r1);
    end if;

    maxd := r;

    R<[x]> := PolynomialRing(Rationals(),g);
    vars := [R.i : i in [1..g]];
    canring := [ <Bexp,vars>];

    for d in [2..maxd] do
        dimen := (2*d-1)*(g-1);
        fouriermat := ZeroMatrix(Rationals(),0,(maxprec-1));
        prds := [ <i,j> : i in [1..g], j in [1..#canring[d-1][1]]];
        done := false;
        curind := 1;
        newfourier := [];
        newvars := [];
        while (done eq false) do
            e1 := prds[curind][1];
            e2 := prds[curind][2];
            pp := Bexp[e1]*canring[d-1][1][e2];
            vecseq := &cat[ Eltseq(Coefficient(pp,j)) : j in [d..d+maxprec-2]];
            tempfouriermat := VerticalJoin(fouriermat,Matrix(Rationals(),1,(maxprec-1),vecseq));
            if Rank(tempfouriermat) eq NumberOfRows(tempfouriermat) then
                fouriermat := tempfouriermat;
                Append(~newfourier,pp);
                Append(~newvars,canring[1][2][e1]*canring[d-1][2][e2]);
                if NumberOfRows(tempfouriermat) eq dimen then
                    done := true;
	                Append(~canring,<newfourier,newvars>);
                end if;
            end if;
            if (done eq false) then
                curind := curind + 1;
                if (curind gt #prds) then
                    done := true;
	                Append(~canring,<newfourier,newvars>);
                end if;
            end if;
        end while;
    end for;

    fmat := ZeroMatrix(Rationals(),0,(maxprec-2));
    for i in [1..#canring[maxd][1]] do
        pp := f*canring[maxd][1][i];
        vecseq := &cat[ Eltseq(Coefficient(pp,j)) : j in [maxd+val..maxd+val+maxprec-3]];
        fmat := VerticalJoin(fmat,Matrix(Rationals(),1,(maxprec-2),vecseq));  
    end for;
    for j in [1..#canring[maxd][1]] do
        vecseq := &cat[ Eltseq(-Coefficient(canring[maxd][1][j],i)) : i in [maxd+val..maxd+val+maxprec-3]];
        fmat := VerticalJoin(fmat,Matrix(Rationals(),1,(maxprec-2),vecseq));
    end for;

    NN1 := NullSpace(fmat);
    M1 := Matrix(Basis(NN1));
    cb1 := nicefy(M1);
    fsol := (cb1*M1)[1];

    felt := &+[ fsol[i+#canring[maxd][1]]*canring[maxd][2][i] : i in [1..#canring[maxd][1]]]/&+[ fsol[i]*canring[maxd][2][i] : i in [1..#canring[maxd][1]]];

    num := Numerator(felt);
    denom := Denominator(felt);
    fmap := map<X -> Y|[num,denom]>;
   
    // checks for correctness
    mfnum := Evaluate(num,Bexp);
    mfdenom := Evaluate(denom,Bexp);
    elt := f - (mfnum/mfdenom);
    assert prec gt 2*degf+1; // If this fails then increase precision
    assert IsWeaklyZero(elt); // If this fails then increase precision
    return fmap, <num, denom>, Y;
end function;

////////////////////////////////////////////////////////////////////////////////

/*

// Example:

X := eqs_quos(111,[]); // This is a genus 11 curve
time map, tup, Y := gen_0_quo(X, 111, 3); // 4.5 seconds
// The map should have degree:
// Index of Gamma_0(N) divided by index of Gamma_0(M), which is

111*(&*[1+1/p : p in PrimeFactors(111)]) / (3*(&*[1+1/p : p in PrimeFactors(3)]));  // this is 38

// It takes a while, but we can check that the map does indeed have the right degree

time assert Degree(map) eq 38; // 22 seconds
 
*/

 

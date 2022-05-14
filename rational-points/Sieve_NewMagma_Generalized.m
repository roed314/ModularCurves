// Magma code to support the calculations in the paper Quadratic.Points on Non-Split Cartan Modular Curves.

// This code carries out the sieving (and Chabauty) calculations of Section 5.4.

// This code runs on Magma-2.26-2, whereas the file Sieve_OldMagma.m runs on Magma-2.25-3.

// First recreate the new model 

load "finiteindexsubgrpofJ0N.m";

R<x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8>:=PolynomialRing(Rationals(),8); 
Eq1:=x_1^2 - x_1*x_3 - x_1*x_4 - x_1*x_7 + x_1*x_8 + x_2*x_4 + x_2*x_5 + 2*x_3*x_4 
- 2*x_3*x_5 - x_3*x_8 + 2*x_4*x_5 +x_4*x_7 + x_5*x_8 - x_7^2 + x_7*x_8; 
Eq2:=-x_1*x_3 + 2*x_1*x_5 + x_1*x_8 - 2*x_3*x_4 - x_3*x_5 + x_3*x_6 - x_3*x_7 
- x_4*x_5 - x_4*x_6 + x_4*x_7 + x_4*x_8 - x_5^2 + x_5*x_6 - 3*x_5*x_8 - x_6*x_7 - 
3*x_6*x_8 + x_7^2 - x_8^2;
Eq3:=-x_1*x_3 + 2*x_1*x_4 + x_1*x_5 - 2*x_1*x_6 + 
4*x_1*x_8 + x_2*x_4 + x_2*x_5 - x_3*x_4 + x_3*x_6 - x_3*x_7 - x_4^2 + x_4*x_5 
- 2*x_4*x_8 + 2*x_5*x_7 + x_5*x_8 - 2*x_6*x_8 + x_7*x_8 - x_8^2;
Eq4:=x_1*x_3 
+ x_1*x_4 + x_1*x_5 - 3*x_1*x_6 + x_1*x_7 + 2*x_1*x_8 - x_2*x_3 - x_2*x_4 + x_2*x_5 
+ x_2*x_6 - x_3^2 - x_3*x_4 - x_3*x_5 + x_3*x_6 - x_3*x_8 - 2*x_4*x_5 - x_4*x_8
 + x_5*x_6 + x_5*x_7 + 2*x_6^2 - 2*x_6*x_7 + x_7^2 + x_7*x_8 - x_8^2; 
Eq5:=x_1*x_2 - x_1*x_3 + x_1*x_5 + x_1*x_6 - x_1*x_7 + x_1*x_8 + x_2^2 + x_2*x_3 
- x_2*x_4 - x_2*x_5 - x_2*x_6 + x_3^2 - x_3*x_4 - x_3*x_5 - x_3*x_6 + x_3*x_8
 - x_4^2 + x_4*x_5 + 2*x_4*x_6 + x_4*x_7 - 2*x_4*x_8 - x_5^2 + 2*x_5*x_6 + x_5*x_7
 - 2*x_5*x_8 + x_6*x_7 - x_6*x_8 + x_7*x_8 - x_8^2; 
Eq6:=2*x_1*x_2 + x_1*x_3 - x_1*x_4 + x_1*x_6 - x_1*x_7 - x_1*x_8 + x_2*x_3 - 2*x_2*x_4 
- x_2*x_5 - x_2*x_6 + x_2*x_7  +x_3^2 - 2*x_3*x_4 - x_3*x_6 - x_3*x_7 + x_4*x_5 
+ x_4*x_6 + x_4*x_7 + 2*x_4*x_8 + x_5*x_6 - 2*x_5*x_8 + x_6*x_7 - x_6*x_8;
 Eq7:=-x_1^2 + x_1*x_2 + 2*x_1*x_3 + x_1*x_5 - x_1*x_6 - x_1*x_7 + 2*x_1*x_8 - x_2^2
 - x_2*x_3 + x_2*x_6 + x_2*x_7  +x_2*x_8 - x_3*x_4 - x_3*x_5 - x_3*x_8 - x_4^2 + x_4*x_6 
+ x_5^2 - x_5*x_6 - x_6*x_7 - x_6*x_8; 
Eq8:=-x_1^2 - x_1*x_2 + x_1*x_5 + 2*x_1*x_6 + x_1*x_7 + x_1*x_8 + x_2*x_3 - x_2*x_4 
- x_2*x_5 + x_2*x_7 + x_2*x_8 - x_3*x_5 + x_3*x_6 - x_3*x_7 + x_4*x_5 - x_4*x_6
 + x_4*x_7 - x_5^2 + x_5*x_6 + x_5*x_7 - x_5*x_8 - 2*x_6*x_8 + x_7*x_8 - x_8^2; 
Eq9:=-2*x_1*x_2 + 2*x_1*x_3 - x_1*x_4 - x_1*x_5 + x_1*x_7 - x_1*x_8 - x_2*x_4 
+ 2*x_2*x_5 + 2*x_2*x_6 + x_2*x_8 - x_3^2 + x_3*x_4 + x_3*x_5 + x_3*x_6 + x_3*x_7
 - x_3*x_8 + x_4^2 + x_4*x_5 + x_4*x_7 - x_5^2 - 2*x_5*x_6 - x_5*x_7 + x_5*x_8
 - x_6*x_7 + x_6*x_8 - x_7^2+ x_7*x_8; 
Eq10:=-2*x_1*x_3 - x_1*x_4 + x_1*x_5 - x_1*x_7 + 2*x_1*x_8 + x_2^2 + x_2*x_3
 - x_2*x_4 - x_2*x_7 + x_3*x_4 + x_3*x_5 + 2*x_3*x_6 - 2*x_3*x_7 + 2*x_3*x_8
 - x_4^2 + 2*x_4*x_5 + 2*x_4*x_7 - x_4*x_8 - x_5^2 + 2*x_5*x_7 - x_5*x_8 
+ 2*x_6*x_7 - 2*x_6*x_8 + 2*x_7*x_8 - 2*x_8^2; 
Eq11:=-x_1*x_2 + 2*x_1*x_4 - x_1*x_6 + x_1*x_7 + x_1*x_8 - x_2^2 + 2*x_2*x_4 
+ x_2*x_5 - x_2*x_6 + 2*x_2*x_7  +2*x_2*x_8 - x_4*x_6 - x_4*x_7 - x_4*x_8 + x_5*x_6
 + x_5*x_7 + x_5*x_8;
 Eq12:=x_1*x_3 + 2*x_1*x_4 - x_1*x_5 - x_1*x_6 + x_1*x_7 + x_1*x_8 - x_2^2 - x_2*x_3
 - x_2*x_4 + x_2*x_5 + x_2*x_6 + x_2*x_7 - 2*x_2*x_8 - x_3^2 + 2*x_3*x_5 + x_3*x_6 
+ x_3*x_7 - x_3*x_8 + x_4*x_5 - x_4*x_6 - x_4*x_7 - x_4*x_8 - x_5*x_6 + x_5*x_7
 + 2*x_5*x_8 - x_6*x_7 + x_6*x_8 - x_7^2 + x_7*x_8;
 Eq13:=-x_1^2 + x_1*x_2 + 2*x_1*x_3 - x_1*x_4 + x_1*x_6 - x_1*x_7 - x_2*x_3 - 2*x_2*x_4
 - 2*x_2*x_5 - x_2*x_7 - x_2*x_8 - x_3^2 - x_3*x_5 + x_3*x_7 - x_3*x_8 + x_4^2 + x_4*x_5
 + 2*x_4*x_7 + x_4*x_8 + x_5*x_6 + x_5*x_7 - x_5*x_8 +2*x_6*x_8 + 2*x_7^2 + 2*x_7*x_8 - 2*x_8^2;
 Eq14:=x_1^2 + 2*x_1*x_2 - x_1*x_3 - x_1*x_4 + x_1*x_6 - x_1*x_8 - x_2^2 + 2*x_2*x_3 
- 2*x_2*x_5 + x_2*x_7 + 3*x_3^2 - x_3*x_4 - 2*x_3*x_6 - x_3*x_7 - x_4^2 + 3*x_4*x_6 
+ 2*x_5^2 + x_5*x_6 + x_5*x_7 - 2*x_6^2 - x_6*x_7 + x_6*x_8 - x_7^2 - 2*x_7*x_8 + 2*x_8^2; 
Eq15:=2*x_1^2 - 2*x_1*x_2 + x_1*x_4 + 3*x_1*x_5 - 2*x_1*x_6 - 2*x_1*x_7 - 2*x_1*x_8 + x_2^2
 - x_2*x_3 - 3*x_2*x_5 - x_2*x_7 -3*x_3*x_4 + x_3*x_6 + x_3*x_8 + x_4^2 + 3*x_4*x_5 - 2*x_4*x_6 
+ x_4*x_7 + x_4*x_8 + 2*x_5^2 - 4*x_5*x_6 - 2*x_5*x_8 +2*x_6*x_7 + x_7^2 -2*x_7*x_8 + x_8^2;
eqns:=[Eq1,Eq2,Eq3,Eq4,Eq5,Eq6,Eq7,Eq8,Eq9,Eq10,Eq11,Eq12,Eq13,Eq14,Eq15]; // List of equations

// Checking if there are exceptional points in residue disc of the point
// X: curve
// p: prime
// Xpp: reduction of X at prime above p
// WMatrix: matrix of involution w
// Qtaa: reduction of quadratic point to Xpp
// Qtbb: reduction of conjugate quadratic point to Xpp 
AreLonelyRanks := function (X, p, Xpp, WMatrix, Qtaa, Qtbb, doublePoint)
    //Rks := [];      // Ranks of residue disc matrices

    //print X;
	AmbientDim := Dimension(AmbientSpace(X)); //Assuming X is given in projective space
	CoordRing<[u]> := CoordinateRing(AmbientSpace(Xpp));

	row := [&+[RowSequence(WMatrix)[k][j] * u[j] : j in [1..AmbientDim + 1]] : k in [1..AmbientDim + 1]];
	wpp := iso<Xpp -> Xpp | row, row>; // w on Xpp

	V, phiD := SpaceOfDifferentialsFirstKind(Xpp);  // Holomorphic differentials on Xpp
	t := hom< V -> V | [(Pullback(wpp, phiD(V.k)))@@phiD - V.k : k in [1..Dimension(V)]] >; 
	T := Image(t);                                 // The space red(V_0)
	omegas := [phiD(T.k) : k in [1..Dimension(T)]]; 
						
	plQtaa := Place(Qtaa);
	plQtbb := Place(Qtbb);
			
	tQta := UniformizingParameter(Qtaa);  
	tQtb := UniformizingParameter(Qtbb);
	Ata := Matrix([[Evaluate(omega/Differential(tQta), plQtaa) : omega in omegas]]);
	Atb := Matrix([[Evaluate(omega/Differential(tQtb), plQtbb) : omega in omegas]]);

	if doublePoint then
		"We have a double rational point.";
		matrixSeq := [];
		
		//matrix is different if Q is a double point
		Append(~matrixSeq, [Evaluate(omega/Differential(tQta), plQtaa) : omega in omegas]);
		Append(~matrixSeq, [Evaluate((omega/Differential(tQta) - Evaluate(omega/Differential(tQta), plQtaa))/tQta, plQtaa) : omega in omegas]); 

		Ata := Matrix(matrixSeq);
		Atb := Matrix(matrixSeq); 
	end if;	

	ra := Rank(Ata);
	rb := Rank(Atb);  // Rank 1 means no exceptional points in residue class

	// TODO: rb never used again
			
	// An alert to say that there could potentially be an exceptional point in the residue class. 
	if ra eq 0 then 
		printf "WARNING: Point not lonely when Qtaa = %o and p = %o.\n", Qtaa, p;
	end if; 
	
	return ra;
end function;


// Change of coordinates map 
g:=hom<R->R | x_2,x_3,1/2*x_2-1/2*x_3-1/2*x_5,1/2*x_1+1/2*x_8,-1/2*x_1+1/2*x_8,1/2*x_2-1/2*x_6,
1/2*x_3-1/2*x_7,1/2*x_2-1/2*x_4>; 

Neqns:=[];
for i in [1..15] do
    Neqn:=g(eqns[i]); 
    Neqns:=Neqns cat [Neqn];
end for;

NX:=Curve(ProjectiveSpace(R),Neqns); 
Nw:=map<NX -> NX | [x_1,x_2,x_3,-x_4,-x_5,-x_6,-x_7,-x_8]>;  

Eqphi1:=-3*x_1+2*x_2;  Eqphi2:=-3*x_1+x_2+2*x_4-2*x_5; Eqphi3:=x_1+x_2+x_4-x_5;
eqnsphi:=[Eqphi1,Eqphi2,Eqphi3]; 
Nphis:=[];  //

for i in [1..3] do
	Nphi:=g(eqnsphi[i]); 
    Nphis:=Nphis cat [Nphi];
end for;

S<X,Y,Z>:=PolynomialRing(Rationals(),3);   
f:=(-Y-Z)*X^3+(2*Y^2+Z*Y)*X^2+(-Y^3+Z*Y^2-2*(Z^2)*Y+Z^3)*X+(2*Z^2*Y^2-3*Z^3*Y);
XNSplus13:=Curve(ProjectiveSpace(S),f);

Nphi:=map< NX -> XNSplus13 | Nphis >;  

SvnPts:=PointSearch(XNSplus13,100);   

///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////

pinsieve:=[3,5,31,43,53,61,73];  // Primes to be used in sieve 

M := 3^10*5^10*13^10*29^10;

//add known quadratic places, takes a minute or two, don't know why so slow...

_<x> := PolynomialRing(Integers());

Discriminants := [11, 67, 7, 2, 19, 163, 7];       
flds := [NumberField(x^2 + discriminant) : discriminant in Discriminants];   

pts := [];

"Adding quadratic places ...";
   
time Append(~pts, Place(NX(flds[1])![-5/13*flds[1].1, 2/13*flds[1].1, 3/13*flds[1].1, 0, -1, -2, 1, 1]));
time Append(~pts, Place(NX(flds[2])![-3/13*flds[2].1, -4/13*flds[2].1, -6/13*flds[2].1, 0, 4, -4, -2, 1]));
time Append(~pts, Place(NX(flds[3])![-7/13*flds[3].1, -5/13*flds[3].1, -1/13*flds[3].1, -1, 0, -1, 1, 1]));
time Append(~pts, Place(NX(flds[4])![ 4/13*flds[4].1, 1/13*flds[4].1, -5/13*flds[4].1, 0, 0, 1, 0, 0]));
/*time Append(~pts, Place(NX(flds[5])![-1/13*flds[5].1, 3/13*flds[5].1, -2/13*flds[5].1, 1, 1, 1, 0, 1]));
time Append(~pts, Place(NX(flds[6])![-3/13*flds[6].1, -2/91*flds[6].1, -3/91*flds[6].1, -12/7, -5/7, -10/7, 25/7, 1]));
time Append(~pts, Place(NX(flds[7])![-1/13*flds[7].1, 3/13*flds[7].1, 11/13*flds[7].1, 1, 0, -3, -1, 1]));*/

"Known quadratic places are: ", pts;

gens := [1*pts[1] - 1*pts[4], 1*pts[2] - 1*pts[4], 1*pts[3] - 1*pts[4]]; // generators of subgroup of MW group of finite index
basePoint := 1*pts[4];

///////////////////////////////////////////////////////////////////////////////////////////////

// X: curve
// QuotientX: quotient curve of X mod involution given by WMatrix
// WMatrix: matrix describing involution on X with quotient QuotientX
// QuadraticPts: known quadratic points on X with
// Fields: quadratic fields over which the QuadraticPoints are defined (field of definition of QuadraticPts[i] is Fields[i])
// Generators: degree 0 divisors on X which generate a subgroup A of finite index of J(Q), J = Jacobian(X)
// BasePoint: base point in X(Q)
// MWPrimes: primes p for the MW sieve
// M: modulus for the MW sieve
MWSieveFiniteIndex := function(X, QuotientX, WMatrix, QuadraticPts, Fields, Generators, BasePoint, MWPrimes, M)
	printf "Started sieve function ...\n";

	// abstract free abelian group A isomorphic to subgroup of J(Q) of finite indexgenerated by Generators (TODO: allow torsion?)
	A := AbelianGroup([0 : i in [1..#Generators]]);

	// data for sieve
	B, iA := sub< A | A >; 
	W := {Zero(A)};    

	// for all MWS primes, determine cosets W_{p,M}
	for p in MWPrimes do 
		printf "Sieving mod p = %o ...\n", p;

		known_divisors_mod_p := {};    // Build up to list of known divisors reduced mod p
		Rks := [];      // Ranks of residue disc matrices
		Fp := GF(p);
		Xp := ChangeRing(X, Fp);

		// assert IsNonSingular(Xp); // Long for each prime.

		///////////////////////////////////////////////////////////////////////////////////////////////

		// loop over all known points, compute their reductions mod p
		for i in [1..#QuadraticPts] do     
			Qa := Coordinates(RepresentativePoint(QuadraticPts[i]));
			Aut := Automorphisms(Fields[i]);
			Qb := Qa;
			doublePoint := true;
			
			if #Aut ne 1 then
				Qb := [Aut[2](crd) : crd in Qa]; // conjugate of Qa if it is not a double point
				doublePoint := false;
			end if;

			OK := RingOfIntegers(Fields[i]);
			dec := Factorization(p*OK);        
			pp := dec[1][1];                   // A prime above the rational prime p
			f := InertiaDegree(pp);            
			Fpp<t> := ResidueClassField(pp);  // Either GF(p) or GF(p^2) depending on inertia degree
			Xpp := ChangeRing(X,Fpp);

			unif := UniformizingElement(pp);   // Use to reduce point modulo p
			m := Minimum([Valuation(a, pp) : a in Qa | not a eq 0]);  
			Qared := [unif^(-m)*a : a in Qa]; 
			Qtaa := Xpp![Evaluate(a,Place(pp)) : a in Qared]; // Reduction of quadratic point to Xpp
			Qta := Xp(Fpp) ! Eltseq(Qtaa);      
 
			plQta := Place(Qta);               

			m := Minimum([Valuation(a, pp) : a in Qb | not a eq 0]); // Repeat with conjugate
			Qbred := [unif^(-m)*a : a in Qb];
			Qtbb := Xpp![Evaluate(a,Place(pp)) : a in Qbred];
			Qtb := Xp(Fpp) ! Eltseq(Qtbb);
			
			plQtb := Place(Qtb);

			////////////////////////////////////////////////////////////////////////////////
			// Checking if there are exceptional points in residue disc of the point
			Rks cat:= [AreLonelyRanks(X, p, Xpp, WMatrix, Qtaa, Qtbb, doublePoint)];
      		//print Rks;

			if Degree(plQta) eq 1 then   // if a point is defined over Fp
			   DivQ := plQta + plQtb;        // then form a divisor from the point and its conjugate
			elif Degree(plQta) eq 2 then   // if a point is defined over Fp^2
			   DivQ := Divisor(plQta);     // then form the divisor of its place
			else
				error "only places of degree <= 2 are implemented.";
			end if;

			known_divisors_mod_p join:= {DivQ};    // Include divisors in the reductions of our known points
		end for;  // End of loop over known quadratic points

		divisors_mod_p := [NewReduce(X, Xp, divisor) : divisor in Generators]; // reductions of (generators of subgroup of MW group) mod p
		bpp := NewReduce(X, Xp, BasePoint); // reduction of base point mod p

	///////////////////////////////////////////////////////////////////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////////

		places_of_degree_1_mod_p := Places(Xp, 1);   // The degree 1 places on Xp 
		places_of_degree_2_mod_p := Places(Xp, 2);   //  The degree 2 places on Xp 
		//Degree 2 divisors on Xp
		degree2divisors_mod_p := {1*pl1 + 1*pl2 : pl1 in places_of_degree_1_mod_p, pl2 in places_of_degree_1_mod_p} join {1*pl : pl in places_of_degree_2_mod_p}; 
		
		time C, phi, psi := ClassGroup(Xp); 
		JFp := TorsionSubgroup(C); // Jac(X)(F_p) =: J(F_p)

		JFpmodM, pi := quo< JFp | M * JFp >; // MJ(F_p)

		image_A_in_JFpmodM := sub< JFpmodM | [pi(JFp!psi(divisor_mod_p)) : divisor_mod_p in divisors_mod_p] >; // Image of A in J(F_p)/M
		// Set S_{p,M} = {degree 2 divisors D of X/F_p with D - bp in im(A in J(F_p)/M)}
		SpM := {divisor_mod_p : divisor_mod_p in degree2divisors_mod_p | pi((JFp!(psi(divisor_mod_p - bpp)))) in image_A_in_JFpmodM};
		TpM := {divisor_mod_p : divisor_mod_p in SpM | divisor_mod_p notin known_divisors_mod_p};   // Remove reductions of all known points,
		
		for i in [1..#QuadraticPts] do  // then add back in those that don't pass the Chabauty test
			if Rks[i] eq 0 then
				TpM join:= {known_divisors_mod_p[i]};
			end if; 
		end for;
		
		// TpM is now T_{p,M}
		iotaTpM := {pi(JFp!(psi(divisor_mod_p - bpp))) : divisor_mod_p in TpM};  // The set iota_{p,M}(T_{p,M}).

		// The map phi_{p,M}. (A is isomorphic to the subgroup of J(Q) of finite index generated by divs Generators)
		phi_pM := hom< A -> JFpmodM | [pi(JFp!psi(divisor_mod_p)) : divisor_mod_p in divisors_mod_p] >;
		Bp := sub< A | Kernel(phi_pM) >; // ker(A -> J(F_p)/M)
		printf "Index of Bp in A: %o\n", Index(A, Bp);
		Wp := {x@@phi_pM : x in iotaTpM}; // Bp-cosets W_{p,M} in A
		printf "#Wp is: %o\n", #Wp;
		printf "Calculations completed for p = %o.\n", p;  

		// perform the intersection of the W_{p,M} directly after each p to save time
		// We now intersect the coset lists W_{p,M}

		if #Wp eq 0 then
			printf "no cosets for p = %o => done.\n", p;
			return true;
		end if;

		Bp, iAp := sub < A | Bp >;   
		Bnew, iBp := sub < Bp | B meet Bp >; // Now intersect Bp + Wp and B + W.
		iAnew := iBp * iAp;
		
		A0, pi0  := quo<  A | iAnew(Bnew) >;
		Ap, pi0p := quo< A0 | pi0(iAp(Bp)) >;
		A1, pi01 := quo< A0 | pi0(iA(B)) >;
		
		pi1 := pi0 * pi01;
		pip := pi0 * pi0p;
		
		W := {x@@pi0 : x in {(pi1(y))@@pi01 + k : y in W, k in Kernel(pi01)} | pi0p(x) in pip(Wp)};
		printf "new #W after sieving mod %o is: %o\n", p, #W;
		
		B := Bnew;
		printf "Index of B in A: %o\n", Index(A, B);
		iA := iAnew;
		
		if #W eq 0 then
			printf "no cosets for p = %o => done.\n", p;
			return true;
		end if; 
	end for; // end of loop over MWprimes

	printf "WARNING: Cosets left: It is not clear whether we have found all quadratic points!\n";
	return false;
end function;

MWSieveFiniteIndex(NX, XNSplus13, Matrix(Nw), pts, flds, gens, basePoint, pinsieve, M);
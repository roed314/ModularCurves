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

M:=3^10*5^10*13^10*29^10;
A:=AbelianGroup([0,0,0]);

//add known quadratic places, takes a minute or two, don't know why so slow...

TQ<x> := PolynomialRing(Integers());

Discriminants := [11, 67, 7, 2, 19, 163, 7];       
flds := [NumberField(x^2 + discriminant) : discriminant in Discriminants];   

pts := [];

"Adding qudratic places...";
   
pts := Append(pts, Place(NX(flds[1])![-5/13*flds[1].1, 2/13*flds[1].1, 3/13*flds[1].1, 0, -1, -2, 1, 1]));
pts := Append(pts, Place(NX(flds[2])![-3/13*flds[2].1, -4/13*flds[2].1, -6/13*flds[2].1, 0, 4, -4, -2, 1]));
pts := Append(pts, Place(NX(flds[3])![-7/13*flds[3].1, -5/13*flds[3].1, -1/13*flds[3].1, -1, 0, -1, 1, 1]));
pts := Append(pts, Place(NX(flds[4])![4/13*flds[4].1, 1/13*flds[4].1, -5/13*flds[4].1, 0, 0, 1, 0, 0]));
pts := Append(pts, Place(NX(flds[5])![-1/13*flds[5].1, 3/13*flds[5].1, -2/13*flds[5].1, 1, 1, 1, 0, 1]));
pts := Append(pts, Place(NX(flds[6])![-3/13*flds[6].1, -2/91*flds[6].1, -3/91*flds[6].1, -12/7, -5/7, -10/7, 25/7, 1]));
pts := Append(pts, Place(NX(flds[7])![-1/13*flds[7].1, 3/13*flds[7].1, 11/13*flds[7].1, 1, 0, -3, -1, 1]));

"Known quadratic places are: ", pts;

gens := [1*pts[1] - 1*pts[4], 1*pts[2] - 1*pts[4], 1*pts[3] - 1*pts[4]];
basePoint := 1*pts[4];

///////////////////////////////////////////////////////////////////////////////////////////////

MWSieveFiniteIndex := function(X, QuotientX, WMatrix, QuadraticPts, Fields, Generators, BasePoint, MWPrimes)
	"Started sieve function...";

	Ws:=[**]; 
	Bs:=[**];

	for p in MWPrimes do 

		redpL := {};    // Build up to list of known divisors reduced mod p
		divsp := [];    // Build up to list of generators for G reduced mod p
		Rks := [];      // Ranks of residue disc matrices
		TQ<x> := PolynomialRing(Integers()); 
		Fp := GF(p);
		Xp := ChangeRing(X, Fp);

		// assert IsNonSingular(Xp); // Long for each prime.

	///////////////////////////////////////////////////////////////////////////////////////////////

		for i in [1..#QuadraticPts] do     
        
			Qa := Coordinates(RepresentativePoint(QuadraticPts[i]));
			Aut := Automorphisms(Fields[i]);
			Qb := [Aut[2](crd) : crd in Qa];

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
			plQtaa := Place(Qtaa); 
			plQta := Place(Qta);               

			m := Minimum([Valuation(a, pp) : a in Qb | not a eq 0]); // Repeat with conjugate
			Qbred := [unif^(-m)*a : a in Qb];
			Qtbb := Xpp![Evaluate(a,Place(pp)) : a in Qbred];
			Qtb := Xp(Fpp) ! Eltseq(Qtbb);
			plQtbb := Place(Qtbb);
			plQtb := Place(Qtb);

	////////////////////////////////////////////////////////////////////////////////

	// Checking if there are exceptional points in residue disc of the point
			AmbientDim := Dimension(AmbientSpace(X)); //Assuming X is given in projective space
			CoordRing<[u]>:=CoordinateRing(AmbientSpace(Xpp));

			row := [&+[RowSequence(WMatrix)[i][j] * u[j] : j in [1..AmbientDim + 1]] : i in [1..AmbientDim + 1]];
			wpp := iso<Xpp -> Xpp | row, row>;

			V, phiD := SpaceOfDifferentialsFirstKind(Xpp);  // Holomorphic differentials on Xpp
			t := hom<V -> V | [ (Pullback(wpp, phiD(V.i)))@@phiD -V.i : i in [1..8] ]>; 
			T := Image(t);                                 // The space red(V_0)
			oms := [phiD(T.i) : i in [1..Dimension(T)]]; 
			tQta := UniformizingParameter(Qtaa);  
			tQtb := UniformizingParameter(Qtbb);
			Ata := Matrix([[Evaluate(omega/Differential(tQta), plQtaa) : omega in oms]]);
			Atb := Matrix([[Evaluate(omega/Differential(tQtb), plQtbb) : omega in oms]]);  
			ra := Rank(Ata);
			rb := Rank(Atb);  // Rank 1 means no exceptional points in residue class
			
			// An alert to say that there could potentially be an exceptional point in the residue class. 
			if ra eq 0 then 
				print "Point Not Lonely When i =", i;
				print"and p =", p;
			end if; 
	
			Rks := Rks cat [ra];

	////////////////////////////////////////////////////////////////////////////////

			if Degree(plQta) eq 1 then   // if a point is defined over Fp
			   DivQ := plQta+plQtb;        // then form a divisor from the point and its conjugate
			end if;

			if Degree(plQta) eq 2 then   // if a point is defined over Fp^2
			   DivQ := Divisor(plQta);     // then form the divisor of its place
			end if;

			redpL := redpL join {DivQ};    // Include  divisors in the reductions of our known points
		end for;  // End of loop

		divsp := [NewReduce(X, Xp, genDiv) : genDiv in Generators];
		bpp := NewReduce(X, Xp, BasePoint);

	///////////////////////////////////////////////////////////////////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////////

		pls1p := Places(Xp, 1);   // The degree 1 places on Xp 
		pls2p := Places(Xp, 2);   //  The degree 2 places on Xp 
		//Degree 2 divisors on Xp
		degr2 := {1*pl1 + 1*pl2 : pl1 in pls1p, pl2 in pls1p} join {1*pl : pl in pls2p}; 
		
		time C, phi, psi := ClassGroup(Xp); 
		/*Z := FreeAbelianGroup(1);
		degr := hom<C -> Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;  
		JFp := Kernel(degr);     // This is isomorphic to J_X(\F_p)*/
		JFp := TorsionSubgroup(C);

		JFpmodM, pi := quo<JFp | M*JFp>; 

		imGhat := sub<JFpmodM | [pi(JFp!psi(divp)) : divp in divsp]>; // Image of G in JFpmodM
		poshat := {DD : DD in degr2 |pi((JFp!(psi(DD - bpp)))) in imGhat};  // Set S_{p,M}
		posP := {DD : DD in poshat | not DD in redpL};   // Remove reductions of all known points,
		
		for i in [1..#QuadraticPts] do  // then add back in those that don't pass the Chabuaty test
			if Rks[i] eq 0 then
				posP := posP join {redpL[i]};
			end if; 
		end for;
		
		// posP is now T_{p,M}
		jposP := Setseq({pi(JFp!(psi(DD - bpp))) : DD in posP});  // The set iota_{p,M}(T_{p,M}).

		h := hom<A -> JFpmodM | [pi(JFp!psi(divp)) : divp in divsp]>; // The map phi_{p,M}.
		Bp := Kernel(h);  
		Bp, iAp := sub<A|Bp>; 
		"Index of Bp in A: ", Index(A, Bp);
		Wp := {x@@h : x in jposP}; 
		"#Wp is: ", #Wp;
		Ws := Ws cat [* Wp *];  
		Bs := Bs cat [* Bp *];
		print "Calculations completed for p =", p;  
	end for;

	////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////

	// We now intersect the coset lists W_{p,M}

	B, iA := sub<A|A>; 
	W := {0*A.1};     

	for i in [1..#MWPrimes] do 
		if Ws[1] eq {} then
			print true;
		end if;  
		
		Bs[i], iAp := sub<A | Bs[i]>;   
		Bnew, iBp := sub<Bs[i] | B meet Bs[i]>; // Now intersect Bp+Wp and B+W.
		iAnew := iBp*iAp;
		
		A0, pi0 := quo<A | iAnew(Bnew)>;
		Ap, pi0p := quo<A0 | pi0(iAp(Bs[i]))>;
		A1, pi01 := quo<A0 | pi0(iA(B))>;
		
		pi1 := pi0*pi01;
		pip := pi0*pi0p;
		
		W := {x@@pi0 : x in {(pi1(y))@@pi01 + k : y in W, k in Kernel(pi01)} | pi0p(x) in pip(Ws[i])};
		"#W is: ", #W;
		
		B := Bnew;
		"Index of B in A: ", Index(A, B);
		iA := iAnew;
		
		if W eq {} then
			print "true at i =", i;
		end if; 
	end for;
	
	Wsieved := W; // Output of the final sieved cosets
	Bsieved := B; // Wsieved are cosets in Z^3 of Bsieved
	
	if Wsieved eq {} then
		print true;
	end if; // This means we have found all the quadratic points! 
end function;

MWSieveFiniteIndex(NX, XNSplus13, Matrix(Nw), pts, flds, gens, basePoint, pinsieve);

N := 137;
X, Xplus, pi, cusps, bp, Xplus_pts, bp_plus, divsX := finiteindexsubgrpofJ0N(N);
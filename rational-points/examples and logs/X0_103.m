load "X0p_NiceModel.m";
load "Chabauty_MWSieve_new.m";

SetLogFile("X0_103.log": Overwrite := true);

Curve_and_Map := function(X,d);
	R := AmbientSpace(X);
	RR<[u]> := CoordinateRing(R);
	n := Dimension(AmbientSpace(X));
	P := ProjectiveSpace(Rationals(), d - 1);
	proj := map<R -> P|[u[i] : i in [1..d]]>;
	Xwd := proj(X);
	mp := map<X -> Xwd|[u[i] : i in [1..d]]>;
	return Xwd, mp;
end function;


//we find models for X and X/w103

C := CuspForms(103);
"Dimension of CuspForms(103) is: ", Dimension(C);
g:=Dimension(C);
AL := AtkinLehnerOperator(C, 103);
N := Nullspace(Matrix(AL - 1));

"Dimesion of eigenspace lambda = 1 for w103 is: ", Dimension(N);

Nc := Nullspace(Matrix(AL + 1));

"Dimesion of eigenspace lambda = -1 for w103 is: ", Dimension(Nc);
"";

B := [&+[(Integers()!(2*Eltseq(Basis(N)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(N)]];
Bc := [&+[(Integers()!(2*Eltseq(Basis(Nc)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(Nc)]];

//X := modformeqns(Bc, B, 103, 500, false);
//let's change this to Philippe's code
X, ws := eqs_quos(103, [[103]]);
"Nice model for X0(103) is:";
X;
"";
RR<[u]> := CoordinateRing(AmbientSpace(X));
n := Dimension(AmbientSpace(X));
H := Matrix(RationalField(), g, g, [1,0,0,0,0,0,0,0, 0,1,0,0,0,0,0,0, 0,0,1,0,0,0,0,0, 0,0,0,1,0,0,0,0, 0,0,0,0,1,0,0,0, 0,0,0,0,0,1,0,0, 0,0,0,0,0,0,-1,0, 0,0,0,0,0,0,0,-1]);
rows := [[&+[RowSequence(H)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]]];
w := iso<X -> X | rows, rows>;

g2:=Dimension(Nc);
Xw, quotMap := Curve_and_Map(X, g-g2+1);
Xw;
RR<[v]> := CoordinateRing(AmbientSpace(Xw));
"Genus of X0(103) is ", Genus(X);
"Genus of X0(103)/w103 is ", Genus(Xw);
"";
ptsX:=PointSearch(X,1);
P1:=ptsX[1];
P2:=ptsX[2];
deg2pb:=[];
pls1 := [Place(P1), Place(P2)];
deg2:=[];
for i in [1..#pls1] do
	for j in [i..#pls1] do
		deg2 := Append(deg2, 1*pls1[i] + 1*pls1[j]);
		if w(RepresentativePoint(pls1[i])) eq RepresentativePoint(pls1[j]) then
			deg2pb := Append(deg2pb, 1*pls1[i] + 1*pls1[j]);
		end if;
	end for;
end for;
#deg2;
Dtor:=Divisor(P1)-Divisor(P2);
//We now show that the torsion is Z/17Z
IsPrincipal(17*Dtor);



primes:=[3,5,7];
A:=AbelianGroup([17]);
genusC:=2;
wMatrix:=Matrix(w);
gens:=[Dtor];
B0, iA0 := sub<A | A.1>;
W0 := {0*A.1};
bp:=deg2pb[1];
assert Degree(ResidueClassField(Decomposition(bp)[1,1])) eq 1;

B,iA,W:= MWSieve(X,wMatrix,genusC,primes, A, gens, bp, B0,iA0,W0,deg2);
B;
W;

// returns 1 - all points on X_0(103) are pullbbacks


load "new_models.m";
X,ws,pairs:= eqs_quos(103,[[103]]);
Xw:=pairs[1,1];

Xw;
f:=pairs[1,2];
//pokušajom s kvad točkama na X0(103)
load "quadPts.m";
deg2,p1,p2,plsbig:=searchDiv2(Xw,2,false);
[Degree(d): d in p1];
[Degree(d): d in p2];
//[Degree(d): d in plsbig];
pb1:=[Pullback(f,p):p in p1];
pb2:=[Pullback(f,p):p in p2];
//pb3:=[Pullback(f,p):p in plsbig];
pb:=pb1 cat pb2;
[Degree(d): d in pb];

pls1:=[]; pls2:=[]; 
for i:=1 to #pb do
dec:=Decomposition(pb[i]);
for j:=1 to #dec do	
	if Degree(dec[j,1]) eq 1 then pls1:=pls1 cat [dec[j,1]];end if;
	if Degree(dec[j,1]) eq 2 then pls2:=pls2 cat [dec[j,1]];end if;
end for;
end for;
for i in [1..#pls2] do
	if Degree(ResidueClassField(pls2[i])) gt 1 then
		K1<z>:=ResidueClassField(pls2[i]);
		d:=SquarefreeFactorization(Discriminant(K1));
		K<w>:=QuadraticField(d);
		w^2, pls2[i];
	end if;
end for;

j := jmap(X, 103);
print "j-invariant of the non-CM point over Q(sqrt 2885) is";
 j(RepresentativePoint(pls2[1]));
//(-24811430943412036323396353064960*z + 35982263935929364331785036841779200 : 1)
z^2;
//-363

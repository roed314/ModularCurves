// This script computes the map to the j-line for a non-hyperelliptic X_H.
// It takes the label as a command line parameter.
// Something like magma l:=7.168.3.1 findjmap.m

load "magma_gl2zhat.txt";
load "GL2GroupTheory.m";
load "ModularCurves.m";

tttt := Cputime();

if (not assigned l) then
  printf "This script assumes that l, the label of the X_H to compute, is given as a command line paramter.\n";
  printf "Something like magma l:=7.168.3.1 findjmap.m\n";
  quit;  
end if;
ind := Index([ magma_gl2zhat[i][1] : i in [1..#magma_gl2zhat]],l);
if (ind ne 0) then
  gp := magma_gl2zhat[ind][2];
else
  printf "Subgroup with that label not found in list.\n";
  quit;
end if;

N := Characteristic(BaseRing(gp));
gens := Generators(gp);

M := CreateModularCurveRec(N,gens);
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

numcusps := M`vinf;
N := M`N;
// oldprec := Ceiling(maxd*(N/3-2) + 2);
maxprec := Floor(N*(1 + maxd/6)+1);
// For 7.168.3.1, minimal prec = 16. 
printf "Precision chosen = %o.\n",maxprec;

printf "Starting model computation.\n";
ttemp := Cputime();

flag, psi, F := FindCanonicalModel(M,maxprec);
if flag then
  M`k := 2;
  M`F0 := F;
  M`psi := psi;
else
  printf "The modular curve with label %o is geometrically hyperelliptic.\n",l;
  quit;
end if;

modeltime := Cputime(ttemp);
printf "Done. Time taken was %o.\n",modeltime;

// Build canonical ring
assert M`k eq 2;
assert #M`F0 eq M`genus;

cuspforms := M`F0;
//polyring := ChangeRing(Parent(M`psi[1]),Rationals());
polyring := PolynomialRing(Rationals(),M`genus,"grevlex");
vars := [ polyring.i : i in [1..M`genus]];
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

canring := [<M`F0,vars>];
K := BaseRing(Parent(M`F0[1][1]));
qN := Parent(M`F0[1][1]).1;
LL := LaurentSeriesRing(K);
fielddeg := Degree(K);

// Let's choose monomials that will *always* work!

printf "Generating canonical ring.\n";
ttime := Cputime();
multcount := 0;
doneper := -1;
total := &+[ (2*d-1)*(M`genus-1) : d in [2..maxd]];
for d in [2..maxd] do
  dimen := (2*d-1)*(M`genus-1);
  fouriermat := ZeroMatrix(Rationals(),0,(maxprec-1)*fielddeg*numcusps);
  mons := MonomialsOfDegree(polyring,d);
  bas := [ mons[i] : i in [1..#mons] | not (mons[i] in initideal)];
  newfourier := [];
  newvars := [];
  for j in [1..#bas] do
    curmon := bas[j];
    // We have to be able to write curmon as a product of a degree (d-1)
    // monomial not in initideal, and a degree 1 element.
    // If we couldn't, then curmon would be in initideal
    ind := Index([ IsDivisibleBy(curmon,canring[d-1][2][k]) : k in [1..#canring[d-1][2]]],true);
    chk, q := IsDivisibleBy(curmon,canring[d-1][2][ind]);
    ind2 := Index(vars,q);
    multcount := multcount + 1;
    if Floor(100*multcount/total) gt doneper then
      doneper := Floor(100*multcount/total);
      printf "Doing multiplication %o of %o. %o\%% complete.\n",multcount,total,doneper;
    end if;  
    newprd := [ cuspforms[ind2][i]*canring[d-1][1][ind][i] : i in [1..numcusps]];
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
j := (1728*Eisenstein(4,qN : Precision := Ceiling((maxprec+2*N)/N))^3)/(Eisenstein(4,qN : Precision := Ceiling((maxprec+2*N)/N))^3 - Eisenstein(6,qN : Precision := Ceiling((maxprec+2*N)/N))^2);
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

C := Curve(ProjectiveSpace(Rationals(),M`genus-1),M`psi : Nonsingular := true);
Cvars := [ C.i : i in [1..M`genus]];
jmap := map<C -> ProjectiveSpace(Rationals(),1) | [num,denom]>;

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

printf "Model time = %o.\n",modeltime;
printf "GB time = %o.\n",gbtime;
printf "Canonical ring time = %o.\n",canringtime;
printf "Linear algebra time = %o.\n",lintime;
printf "Point search time = %o.\n",pttime;
printf "j-map time = %o.\n",jtime;
printf "Total time was %o sec.\n",Cputime(tttt);



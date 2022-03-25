// This script uses David Zywina's code to produce a universal elliptic curve
// for a ``quadratic refinement'' of a modular curve isomorphic to P^1.
// It takes as input a label of a subgroup H that doesn't contain -I
// as well as the label of <H,-I>.
// It requires the Fourier expansion of a modular function for X_<H,-I>.

if (not assigned l) then
  printf "This script requires a command line argument.\n";
  printf "The usage is magma l:=label l2:=coverlabel finescript.m";
  printf "The file modfunccoverlabel.txt must exist and contain the Fourier expansion of a generator of the function field.\n";
  quit;
end if;

SetLogFile("model" cat l cat ".out");
coverlabel := l2;

Attach("gl2.m");
load "gl2data.m";
load "magma_gl2zhat.txt";
load "modcurve.m";

F<t> := FunctionField(Rationals());

// This function takes two q-expansions and a degree bound
// The first one is a modular function, the second
// is a modular function of degree 1, and the
// third is a degree bound. This function tries to represent
// the first input as a rational function in the second.
// The two modular functions MUST belong to the same
// power series ring.
// The range of coefficients needed is from
// val2+deg*val1 to val2+deg*val1+2*deg+1

function ratfuncrep(modfunc,haup,deg)
  printf "Call to ratfuncrep with deg = %o.\n",deg;
  if IsWeaklyZero(modfunc) then
    return Parent(t)!0;
  end if;
  field := BaseRing(Parent(modfunc));
  q := Parent(modfunc).1;
  M := ZeroMatrix(field,2*deg+2,2*deg+2);
  den := ExponentDenominator(haup);
  val1 := Min(0,Valuation(haup)*den);
  val2 := Min(0,Valuation(modfunc)*den);
  //printf "den = %o.\n",den;
  timet := Cputime();
  printf "Building last %o rows of the matrix.\n",deg+1;
  printf "Using coefficients %o to %o.\n",(val2+deg*val1)/den,(val2+deg*val1+2*deg+1)/den;
  for m in [0..deg] do
    haupprec := (m*val1 + 2*deg+2)/den;
    func2 := -(haup + BigO(q^(haupprec)))^(deg-m)*modfunc;
    //printf "For m = %o, the precision on func2 is from %o to %o.\n",m,Valuati\
on(func2),AbsolutePrecision(func2);
    //printf "For m = %o, precision needed is from %o to %o.\n",m,(val2+(deg-m)*val1)/den,(val2+(deg-m)*val1+2*deg+1)/den;
    //printf "Coefficient range %o to %o.\n",(val2+deg*val1)/den,(val2+deg*val1+2*deg+1)/den;
    for n in [1..2*deg+2] do
      M[m+deg+2][n] := Coefficient(func2,(val2+deg*val1+n-1)/den);
    end for;
  end for;
  printf "Time taken was %o.\n",Cputime(timet);
  timet := Cputime();
  printf "Building the first %o rows of the matrix.\n",deg+1;
  for m in [0..deg] do
    haupprec := (val2+m*val1+2*deg+2)/den;
    func2 := (haup+BigO(q^(haupprec)))^(deg-m);
    //printf "For m = %o, precision on func2 ranges from %o to %o.\n",m,Valuati\
on(func2),AbsolutePrecision(func2);
    //printf "Precision needed is %o to %o.\n",(val2+(deg-m)*val1)/den,(val2+(d\
eg-m)*val1+2*deg+1)/den;
    for n in [1..2*deg+2] do
      M[m+1][n] := Coefficient(func2,(val2+deg*val1+n-1)/den);
    end for;
  end for;
  printf "Time taken was %o.\n",Cputime(timet);
  printf "Solving the linear system of size %ox%o.\n",2*deg+2,2*deg+2;
  timet := Cputime();
  V := Nullspace(M);
  printf "Time taken was %o.\n",Cputime(timet);
  printf "Null space has dimension %o.\n",Dimension(V);
  v := V.1;
  QQ := Rationals();
  // We really hope that all the entries of V can be coerced into QQ
  numcoeffs := [ QQ!v[i] : i in [1..deg+1]];
  denomcoeffs := [ QQ!v[i] : i in [deg+2..2*deg+2]];
  mult := LCM([Denominator(v[i]) : i in [1..2*deg+2]]);
  numcoeffs := [ numcoeffs[i]*mult : i in [1..deg+1]];
  denomcoeffs := [ denomcoeffs[i]*mult : i in [1..deg+1]];
  ret := &+[ numcoeffs[i]*t^(deg+1-i) : i in [1..deg+1]]/&+[ denomcoeffs[i]*t\
^(deg+1-i) : i in [1..deg+1]];
  // New ret check
  numer := &+[ numcoeffs[i]*t^(deg+1-i) : i in [1..deg+1]];
  denom := &+[ denomcoeffs[i]*t^(deg+1-i) : i in [1..deg+1]];
  for d in [2..Dimension(V)] do
    vd := V.d;
    numerd := &+[ (QQ!vd[i])*t^(deg+1-i) : i in [1..deg+1]];
    denomd := &+[ (QQ!vd[i])*t^(2*deg+2-i) : i in [deg+2..2*deg+2]];
    if (numerd*denom - numer*denomd) ne 0 then
      printf "ERROR in ratfuncrep! is not unique!\n";
      bad := 0;
      bad2 := 1/bad;
    end if;    
  end for;
  retcheck := &+[ numcoeffs[i]*(haup+BigO(q^AbsolutePrecision(modfunc)))^(deg+1-i) : i in [1..deg+1]]/&\
+[
  denomcoeffs[i]*(haup+BigO(q^AbsolutePrecision(modfunc)))^(deg+1-i) : i in [1..deg+1]];
  if IsWeaklyZero(retcheck - modfunc) then
    printf "Success! The linear system worked.\n";
    printf "The result was %o.\n",ret;
  else
    printf "Error! Solving the linear system failed!\n";
    bad := 0;
    bad2 := 1/bad;
  end if;
  return ret;
end function;

// Parse input data

N := StringToInteger(Split(l,".")[1]);
ind := Floor(StringToInteger(Split(l,".")[2])/2);
filename := "modfunc" cat coverlabel cat ".txt";
str := Read(filename);
haupt, Hcover := eval str;
Hcover := GL2Lift(Hcover,N);
cycfield := BaseRing(Parent(haupt));
ordofz := CyclotomicOrder(cycfield);
pow := Floor(N/ordofz);
expdenom := ExponentDenominator(haupt);

prec := 60*N;

K<zeta> := CyclotomicField(N);
R<q> := PuiseuxSeriesRing(K : Precision := prec);
newhaupt := R!0;
for n in [Valuation(haupt)*expdenom..AbsolutePrecision(haupt)*expdenom-1] do
  cof := Eltseq(Coefficient(haupt,n/expdenom));
  term := R!(&+[ cof[i]*zeta^(pow*(i-1)) : i in [1..#cof]]*q^(n/expdenom));
  newhaupt := newhaupt + term;
end for;
newhaupt := newhaupt + BigO(q^AbsolutePrecision(haupt));
haupt := newhaupt;

subind := Index([ magma_gl2zhat[i][1] : i in [1..#magma_gl2zhat]],l);
sub := magma_gl2zhat[subind][2];
GN := GL(2,Integers(N));
chk, elt := IsConjugateSubgroup(GN,Hcover,sub);
H := GL2MinimizeGenerators(Conjugate(sub,elt));
genlist := Generators(H);

// We transpose now.

gens := [ Transpose(g) : g in genlist];

M := CreateModularCurveRec(N,gens);
// The optimal precision involves the cusp width as well as the index.

printf "Computing weight 3 modular forms for H.\n";
M := FindModularForms(3,M,prec);
printf "Done.\n";

qq := Parent(haupt).1;
fn0 := M`F[1][1];
fn := Evaluate(fn0,qq^(1/N));

modfun := fn^2/Eisenstein(6,qq : Precision := prec);
jfourier := (1728*Eisenstein(4,qq : Precision := prec+2)^3)/(Eisenstein(4,qq : Precision := prec+2)^3 - Eisenstein(6,qq : Precision := prec+2)^2);

ratfun := ratfuncrep(modfun,haupt,Floor(ind/2));
jratfunc := ratfuncrep(jfourier,haupt,ind);

A0 := -27*jratfunc*(jratfunc-1728)*(jratfunc*ratfun)^2;
B0 := 54*jratfunc*(jratfunc-1728)^2*(jratfunc*ratfun)^3;

// Let's simplify it.

FF := Factorization(Numerator(A0)*Numerator(B0)*Denominator(A0)*Denominator(B0));
for i in [1..#FF] do
  multpow := Ceiling(Max(-Valuation(A0,FF[i][1])/4,-Valuation(B0,FF[i][1])/6));
  A0 := A0*(F!FF[i][1])^(4*multpow);
  B0 := B0*(F!FF[i][1])^(6*multpow);  
end for;

// A0 and B0 should be polynomials now.

A0num := Numerator(A0);
B0num := Numerator(B0);
Adenom := LCM([ Denominator(Coefficient(A0num,i)) : i in [0..Degree(A0num)]]);
Bdenom := LCM([ Denominator(Coefficient(B0num,i)) : i in [0..Degree(B0num)]]);
FF := Factorization(LCM([ Adenom, Bdenom ]));
for i in [1..#FF] do
  multpow := Ceiling(Max(Valuation(Adenom,FF[i][1])/4,Valuation(Bdenom,FF[i][1])/6));
  A0 := A0*(FF[i][1])^(4*multpow);
  B0 := B0*(FF[i][1])^(6*multpow);
end for;

// Now they should be integral.
A0num := Numerator(A0);
B0num := Numerator(B0);

Anum := GCD([ Numerator(Coefficient(A0num,i)) : i in [0..Degree(A0num)]]);
Bnum := GCD([ Numerator(Coefficient(B0num,i)) : i in [0..Degree(B0num)]]);
FF := Factorization(GCD(Anum,Bnum));
for i in [1..#FF] do
  multpow := Ceiling(Max(-Valuation(Anum,FF[i][1])/4,-Valuation(Bnum,FF[i][1])/6));
  A0 := A0*(FF[i][1])^(4*multpow);
  B0 := B0*(FF[i][1])^(6*multpow);
end for;
A := A0;
B := B0;

printf "Universal elliptic curve is y^2 = x^3 + (%o)*x + %o.\n",A,B;
modelfile := "model" cat l cat ".txt";
System("rm -f " cat modelfile);
PrintFile(modelfile,"F<t> := FunctionField(Rationals());");
PrintFile(modelfile,Sprintf("X := EllipticCurve([0,0,0,%o,%o]);",A,B));
PrintFile(modelfile,"return X;");
quit;

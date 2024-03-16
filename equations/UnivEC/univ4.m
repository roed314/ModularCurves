intrinsic nicefy(M::ModMatFldElt[FldRat]) -> ModMatFldElt[FldRat]
{Input: M Matrix
Simplify a Q-vector space. This script takes a matrix M
and finds the lattice of elements L where all the coordinates are integers.
Then it finds an LLL-reduced basis for that lattice. It returns
a square matrix that indicates which linear combinations of the rows of M
are the LLL-reduced basis}

  M0, T := EchelonForm(M);
  // Rows of T give current basis.
  ee := Eltseq(M0);
  denom := LCM([ Denominator(ee[i]) : i in [1..#ee]]);
  printf "Nicefying %ox%o matrix.\n",NumberOfRows(M),NumberOfColumns(M);
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
end intrinsic;

intrinsic fieldfind(G::GrpMat,K::FldCyc) -> FldNum, FldCycElt
{This function takes a subgroup of GL(1,Integers(N)) and an instance of Q(zeta_N)
and returns a simple representation of the corresponding subfield of
Q(zeta_N), as well as a primitive element for the extension.}

  N := Characteristic(BaseRing(G));
  z := K.1;  
  nprim := N;
  if (N mod 4 eq 2) then
    z := z^2;
    nprim := (N div 2);
  end if;
  if (N mod 4 eq 0) then
    nprim := (N div 2);
  end if;
  prim := &+[ z^(k*(Integers()!g[1][1])) : k in Divisors(nprim), g in G];
  es := Eltseq(prim);
  es2 := [ Integers()!es[i] : i in [1..#es]];
  g := GCD(es2);
  if (g ne 0) then
    prim := prim/g;
  end if;  
  minpoly := MinimalPolynomial(prim);
  assert Degree(minpoly) eq (EulerPhi(N)/#G);
  return NumberField(minpoly), prim;
end intrinsic;

intrinsic ComputeModelwithPrec(M::Rec) -> Rec, RngIntElt, RngIntElt, RngIntElt, RngIntElt, BoolElt
{Compute model and modular forms of M}
  M := FindModelOfXG(M,20);
  mult := M`mult;
  if (not assigned M`prec) then
    M`prec := 20;
    end if;

  maxd := 0;
  mind := 0;
  maxprec := 0;
  degL := 0;
  geomhyper := false;
  // Compute the degree of the line bundle used
  if (M`mult ne [ 1 : i in [1..M`vinf]]) or (M`k ne 2) then
    printf "Curve is geometrically hyperelliptic. mult = %o.\n",mult;
    geomhyper := true;
    k := M`k;
    degL:= ((k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps) - (&+M`mult);
    printf "degL = %o.\n",degL;
    maxd := Floor((M`index + M`genus - 1)/degL) + 1;
    mind := maxd - 1;
    // It seems like for 39.84.2.3, maxd should be 14, not 11.
    printf "Smallest degree that might work = %o. The degree %o definitely works.\n",mind,maxd;
    maxprec := Floor(M`N*(M`k*maxd/12 + 1)) + 1;
    if (maxprec gt M`prec) then
      printf "Now that we know it's geometrically hyperelliptic, we need more precision.\n";
      printf "New precision chosen = %o.\n",maxprec;
      delete M`has_point;
      M := FindModelOfXG(M,maxprec);
      printf "Recomputation of modular forms done.\n";
    end if;
  else
    printf "Curve is not geometrically hyperelliptic.\n";
    maxd := Floor((M`index)/(2*M`genus-2) + 3/2);
    if ((maxd-1) ge (M`index)/(2*M`genus-2)) and ((maxd-1) le ((M`index)/(2*M`genus-2) + 1/2)) then
      mind := maxd-1;
      printf "The smallest degree that might work is %o.\n",mind;
      printf "Degree %o definitly works.\n",maxd;  
    else
      mind := maxd;
      printf "The smallest degree that might work is %o and it definitely work//s.\n",maxd;
    end if;  
    maxprec := Floor(M`N*(1 + maxd/6)+1);
    if (maxprec gt M`prec) then
      printf "Now that we know it's non-hyperelliptic, we need more precision.\n";
      printf "New precision chosen = %o.\n",maxprec;
      delete M`has_point;    
      M := FindModelOfXG(M,maxprec);
      printf "Recomputation of modular forms done.\n";
    end if;   
  end if; 
  return M, maxd, mind, maxprec, degL, geomhyper;
end intrinsic;

intrinsic CuspsOrbits(M::Rec) -> SeqEnum[RngIntElt]
{Inputs: N::RngIntElt, cusps 
Computes the action of (Z/NZ)^* on the cusps of X_G.  This corresponds to the action of Gal(Q(zeta_N)/Q) on the cusps.}
  N := M`N;
  G := M`G;
  G0 := G;
  GL2 := GL(2,Integers(N));
  SL2 := SL(2,Integers(N));    
  U,pi:=UnitGroup(Integers(N));
  s:={};
  for u in Generators(U) do
    d:=Integers(N)!pi(u);
    b:=GL2![1,0,0,d];
    flag:=exists(g){g: g in G | Determinant(g) eq d};
    error if not flag, "Group G should have full determinant.";
    sigma:=[FindCuspPair(M,SL2!(g^(-1)*GL2!M`cusps[i]*b))[1]: i in [1..#M`cusps]];
    s:=s join {sigma};
  end for;
  // Let H and H0 be the intersection of G and G0, respectively, with SL(2,Z/N).  We now computes the action of H0/H on the cusps of X_G.
  H0:=G0 meet SL(2,Integers(N));
  Q,iotaQ:=quo<H0|M`H>;
  for g_ in Generators(Q) do
    g:= g_ @@ iotaQ;
    sigma:=[FindCuspPair(M,SL2!(g^(-1)*SL2!M`cusps[i]))[1]: i in [1..#M`cusps]];
    s:=s join {sigma};
  end for;

  S:=sub<SymmetricGroup(#M`cusps)|s>;
  ind:=[[i:i in O]: O in Orbits(S)];  // orbits of cusps under the actions of G0 and Gal_Q.
  chosencusps := [ ind[j][1] : j in [1..#ind]];
  chosencusps := Sort(chosencusps);
  chosenmult := [ M`mult[c] : c in chosencusps];
  printf "Galois orbits of cusps are: %o.\n",{* #ind[j] : j in [1..#ind]*};
  return chosencusps;
end intrinsic;

intrinsic RewriteFourierExpansion(M::Rec, chosencusps::SeqEnum[RngIntElt], maxprec::RngIntElt) -> SeqEnum, RngIntElt, Tup
{Rewriting Fourier expansions over smaller fields}
  modforms0 := [ [ M`F0[i][c] : c in chosencusps] : i in [1..#M`F0]];
  N := M`N;
  GL2 := GL(2,Integers(N));  
  U,pi:=UnitGroup(Integers(N));
  GL2Galois := sub<GL2 | [[1,0,0,pi(u)] : u in Generators(U)]>;
  z := Parent(Coefficient(modforms0[1][1],0)).1;
  R<x> := PolynomialRing(Rationals());
  fourierlist := <>;
  totalprec := 0;
  KKlist := <>;
  for c in [1..#chosencusps] do
    galoiscusp0 := GL2Galois meet Conjugate(M`G,M`cusps[chosencusps[c]]);
    // The subfield of Q(zeta_N) corresponding to galoiscusp is the field of definition of the Fourier coeffs.
    galoiscusp := Sort([g[2][2] : g in galoiscusp0]);
    //printf "For cusp %o, Galois group is %o.\n",c,galoiscusp;
    KK, prim := fieldfind(sub<GL(1,Integers(N)) | [[g[2][2]] : g in Generators(galoiscusp0)]>,Parent(z));
    printf "For cusp %o, Fourier coefficient field is %o.\n",c,R!DefiningPolynomial(KK);
    PP<qN> := LaurentSeriesRing(KK);
    Embed(KK,Parent(z),prim);
    Append(~KKlist,<KK,prim>);
    totalprec := totalprec + maxprec*Degree(KK);
    curfour := <>;
    for i in [1..#modforms0] do
      newfourier := &+[ KK!Coefficient(modforms0[i][c],l)*qN^l : l in [0..AbsolutePrecision(modforms0[i][c])-1]] + BigO(qN^AbsolutePrecision(modforms0[i][c]));
      Append(~curfour,newfourier);
    end for;
    Append(~fourierlist,curfour);
  end for;
  modforms := << fourierlist[j][i] : j in [1..#chosencusps]> : i in [1..#modforms0]>;
  return modforms, totalprec, KKlist;
end intrinsic;

intrinsic CanonicalRing(polyring::RngMPol, M::Rec, chosencusps::SeqEnum[RngIntElt], modforms::Tup, maxd::RngIntElt) -> Tup, SeqEnum
{Compute the (log)-canonical ring of M}
  Ffield := FieldOfFractions(polyring);
  vars := [ polyring.i : i in [1..#modforms]];
  gens := [ Evaluate(M`psi[j],vars) : j in [1..#M`psi]];
  ttemp := Cputime();
  printf "Computing Grobner basis for ideal.\n";
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

  canring := <<modforms,vars>>;
  // Let's choose monomials that will *always* work!

  printf "Generating log-canonicalish ring.\n";
  multcount := 0;
  doneper := -1;
  total := &+[ #[s : s in MonomialsOfDegree(polyring,d) | not (s in initideal)] : d in [2..maxd]];
  for d in [2..maxd] do
    mons := MonomialsOfDegree(polyring,d);
    bas := [ mons[i] : i in [1..#mons] | not (mons[i] in initideal)];
    newfourier := <>;
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
      newprd := < modforms[ind2][i]*canring[d-1][1][ind][i] : i in [1..#chosencusps]>;
      Append(~newfourier,newprd);
      Append(~newvars,curmon);
    end for;
    Append(~canring,<newfourier,newvars>);
  end for;
  return canring, vars;
end intrinsic;

intrinsic jMap(polyring::RngMPol, M::Rec, chosencusps::SeqEnum[RngIntElt], canring::Tup, modforms::Tup, prec::SeqEnum[RngIntElt]) -> RngMPolElt, RngMPolElt, Crv
{Compute the j-map as an element of the function field of M}
  totalprec := prec[1]; maxprec := prec[2]; maxd := prec[3]; mind := prec[4];
  N := M`N;
  FFFF<qN> := LaurentSeriesRing(Rationals());
  j := (1728*Eisenstein(4,qN : Precision := Ceiling((maxprec+2*N)/N))^3)/(Eisenstein(4,qN : Precision := Ceiling((maxprec+2*N)/N))^3 - Eisenstein(6,qN : Precision := Ceiling((maxprec+2*N)/N))^2);
  j := Evaluate(j,qN^N);

  func := j;
  done := false;

  curd := mind;
  jmat := ZeroMatrix(Rationals(),0,totalprec);
  for i in [1..#canring[curd][1]] do
    vecseq := [];
    for jj in [1..#chosencusps] do
      pp := (func*canring[curd][1][i][jj]);
      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-N..-N+maxprec-1]]);
    end for;
    jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;

  for i in [1..#canring[curd][1]] do
    vecseq := [];
    for jj in [1..#chosencusps] do
      pp := -canring[curd][1][i][jj];
      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-N..-N+maxprec-1]]);
    end for;
    jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;
  NN := NullSpace(jmat);
  dimdim := Dimension(NN);
  printf "For d = %o, dimension of null space is %o.\n",curd,dimdim;
  if dimdim ge 1 then
    done := true;
  end if;

  if (done eq false) then
    curd := maxd;
    jmat := ZeroMatrix(Rationals(),0,totalprec);
    for i in [1..#canring[curd][1]] do
      vecseq := [];
      for jj in [1..#chosencusps] do
        pp := (func*canring[curd][1][i][jj]);
        vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-N..-N+maxprec-1]]);
      end for;
      jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
    end for;

    for i in [1..#canring[curd][1]] do
      vecseq := [];
      for jj in [1..#chosencusps] do
        pp := -canring[curd][1][i][jj];
        vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-N..-N+maxprec-1]]);
      end for;
      jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
    end for;
    NN := NullSpace(jmat);
    printf "For d = %o, dimension of null space is %o.\n",curd,Dimension(NN);
  end if;

  canringdim := #canring[curd][1];
  nullmat := Matrix(Basis(NN));
  changemat := nicefy(nullmat);
  v := (changemat*nullmat)[1];
  denom := &+[ (polyring!v[i])*canring[curd][2][i] : i in [1..canringdim]];
  num := &+[ (polyring!v[i+canringdim])*canring[curd][2][i] : i in [1..canringdim]];
  weakzero := [ &+[ v[i]*canring[curd][1][i][j] : i in [1..canringdim]]*func - &+[ v[i+canringdim]*canring[curd][1][i][j] : i in [1..canringdim]] : j in [1..#chosencusps]];
  assert &and [ IsWeaklyZero(weakzero[i]) : i in [1..#chosencusps]];

  C := Curve(ProjectiveSpace(Rationals(),#modforms-1),M`psi);
  return num, denom, C;
end intrinsic;

intrinsic RatioFromWeight3Form(M::Rec, M2::Rec, arg::List) ->
 RngMPolElt, RngMPolElt
{Compute f^2/E_6 as an element of the function of M, where f is a weight 3 modular form for the fine curve
arg::[polyring::RngMPol, geomhyper::BoolElt, KKlist::Tup, canring::Tup,
 chosencusps::SeqEnum[RngIntElt], degL::RngIntElt, irregcusps::BooCanonical, totalprec::RngIntElt, maxprec::RngIntElt]}

  polyring := arg[1]; geomhyper := arg[2]; KKlist := arg[3]; canring := arg[4]; chosencusps := arg[5]; degL := arg[6];
  irregcusps := arg[7]; totalprec := arg[8]; maxprec := arg[9];
  N := M`N;
  N2 := M2`N;
  GL2 := GL(2,Integers(N));
  U,pi:=UnitGroup(Integers(N));
  newmaxprec := (maxprec-1)*Ceiling((N2/N))+1;
  if irregcusps then
    newmaxprec := (maxprec-1)*Ceiling((2*N2/N))+1;
  end if;
  //M2 := FindModularForms(3,M2,(maxprec-1)*Ceiling((N2/N))+1);
  M2 := FindModularForms(3, M2, newmaxprec);

  FFFF<qN> := LaurentSeriesRing(Rationals());
  E6 := 0;
  E6 := Eisenstein(6,qN : Precision := Ceiling((maxprec+2*N)/N));
  E6 := Evaluate(E6,qN^N);

  modforms3 := [ M2`F[1][c]^2 : c in [1..#M2`cusps]]; // weight 6 
  modforms3_new := [f/E6: f in ConvertModularFormExpansions(M, M2, [1,0,0,1], modforms3)];
  printf "Rewriting Fourier expansions over smaller fields.\n";
  GL2Galois := sub<GL2 | [[1,0,0,pi(u)] : u in Generators(U)]>;
  z := Parent(Coefficient(modforms3_new[1],0)).1;
  R<x> := PolynomialRing(Rationals());
  fourierlist := <>;
  // Only make a list of the Fourier expansions of (M2`F[1][i]^2/E6)
  totalprec := 0;
  for c in [1..#chosencusps] do
    galoiscusp0 := GL2Galois meet Conjugate(M`G,M`cusps[chosencusps[c]]);
    // The subfield of Q(zeta_N) corresponding to galoiscusp is the field of definition of the Fourier coeffs.
    galoiscusp := Sort([g[2][2] : g in galoiscusp0]);
    //printf "For cusp %o, Galois group is %o.\n",c,galoiscusp;
    KK := KKlist[c][1];
    prim := KKlist[c][2];
    PP<qN> := LaurentSeriesRing(KK);
    Embed(KK,Parent(z),prim);
    totalprec := totalprec + maxprec*Degree(KK);
    newfourier := &+[ KK!Coefficient(modforms3_new[chosencusps[c]],l)*qN^l : l in [0..AbsolutePrecision(modforms3_new[chosencusps[c]])-1]] + BigO(qN^AbsolutePrecision(modforms3_new[chosencusps[c]]));
    Append(~fourierlist,newfourier);
  end for;
  modf := fourierlist;

  // Now represent modf as a ratio of elements in the log-canonicalish ring.
  // A modular form of weight k has (k/12)*Index(subgroup) many zeros in H/subgroup.
  // This means that the ratio of two holomorphic modular forms of weight 6
  // is a modular function of degree <= (1/2)*index.

  curd := 0;
  if geomhyper then
    curd := Floor(((M`index/2) + M`genus - 1)/degL) + 1;;
  else  
    curd := Floor((M`index)/(4*M`genus-4) + 3/2);
  end if;

  fmat := ZeroMatrix(Rationals(),0,totalprec);
  for i in [1..#canring[curd][1]] do
    vecseq := [];
    for jj in [1..#chosencusps] do
      pp := (modf[jj]*canring[curd][1][i][jj]);
      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [0..maxprec-1]]);
    end for;
    fmat := VerticalJoin(fmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;

  for i in [1..#canring[curd][1]] do
    vecseq := [];
    for jj in [1..#chosencusps] do
      pp := -canring[curd][1][i][jj];
      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [0..maxprec-1]]);
    end for;
    fmat := VerticalJoin(fmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;
  NN := NullSpace(fmat);
  dimdim := Dimension(NN);
  printf "For d = %o, dimension of null space is %o.\n",curd,dimdim;
  assert dimdim ge 1;

  canringdim := #canring[curd][1];
  nullmat := Matrix(Basis(NN));
  changemat := nicefy(nullmat);
  v := (changemat*nullmat)[1];
  fdenom := &+[ (polyring!v[i])*canring[curd][2][i] : i in [1..canringdim]];
  fnum := &+[ (polyring!v[i+canringdim])*canring[curd][2][i] : i in [1..canringdim]];
  weakzero := [ &+[ v[i]*canring[curd][1][i][j] : i in [1..canringdim]]*modf[j] - &+[ v[i+canringdim]*canring[curd][1][i][j] : i in [1..canringdim]] : j in [1..#chosencusps]];
  assert &and [ IsWeaklyZero(weakzero[i]) : i in [1..#chosencusps]];
  return fnum, fdenom;
end intrinsic; 

// Input: C::Crv, g::RngIntElt -> DivCrvElt
// Given a curve C of genus g, returns a divisor of low degree on C 
function LowDegreeDivisor(C, g)
  P1 := ProjectiveSpace(Rationals(),1);

  // The P^1 case
  E := 0;
  phi := 0;
  if (g eq 0) and (#DefiningEquations(C) eq 0) then
    E := Divisor(C![1,0]);
  end if;
  // The pointless conic case
  if (g eq 0) and (#DefiningEquations(C) gt 0) then
    E := -CanonicalDivisor(C);
  end if;

  if (g ge 1) then
    pts := PointSearch(C,100);
    if #pts gt 0 then
      E := Divisor(C!Eltseq(pts[1]));
    else
      if (g ge 1) then
        phi := map<C -> P1 | [C.1,C.2]>;
        D := Divisor(C,(P1![1,0])@@phi);
        supp := Support(D);
        E := Divisor(supp[1]);
      end if;  
    end if;
  end if;
  return E;
end function;

// Initial reduction of the coefficients A and B in V^2 = U^3 + A*U + B
function FirstReduction(polyring, C, E, r, x, A, B)
  QC := FunctionField(C);
  vals := [ QC.i : i in [1..Rank(polyring)-1]] cat [QC!1];
  rfunc := Evaluate(r,vals);
  xfunc := Evaluate(x,vals);
  rdiv := Divisor(rfunc);
  xdiv := Divisor(xfunc);
  printf "Decomposing divisors.\n";
  decomp1 := Decomposition(rdiv);
  decomp2 := Decomposition(xdiv+E);
  allsup := [ decomp1[i][1] : i in [1..#decomp1]];
  for i in [1..#decomp2] do
    if not (decomp2[i][1] in allsup) then
      Append(~allsup,decomp2[i][1]);
    end if;
  end for;
  // Valuation of A and B at all divisors in their support
  avals := [ 2*Valuation(rdiv,allsup[j])+Valuation(xdiv,allsup[j]) : j in [1..#allsup]];
  bvals := [ 3*Valuation(rdiv,allsup[j])+2*Valuation(xdiv,allsup[j]) : j in [1..#allsup]];
  // A divisor D to "take out". We want to remove 4D from A and 6D from B.
  changevals := [ Min(Round(avals[j]/4),Round(bvals[j]/6)) : j in [1..#allsup]];
  change := &+[ changevals[j]*allsup[j] : j in [1..#allsup]];

  Adeg := &+[ avals[j]*Degree(allsup[j]) : j in [1..#allsup] | avals[j] ge 0 ];
  Bdeg := &+[ bvals[j]*Degree(allsup[j]) : j in [1..#allsup] | bvals[j] ge 0 ];
  printf "Starting degree of A = %o, degree of B = %o.\n",Adeg,Bdeg;

  redD, rr, E, func := Reduction(change,E);
  // We have change = redD + r*E - div(func).
  // In this case, redD has degree 0 and the support of E is contained in allsup
  newavals := [ avals[j] - 4*Valuation(change,allsup[j]) + 4*Valuation(redD,allsup[j]) + 4*rr*Valuation(E,allsup[j]) : j in [1..#allsup]];
  newbvals := [ bvals[j] - 6*Valuation(change,allsup[j]) + 6*Valuation(redD,allsup[j]) + 6*rr*Valuation(E,allsup[j]) : j in [1..#allsup]];

  newAdeg := &+[ newavals[j]*Degree(allsup[j]) : j in [1..#allsup] | newavals[j] ge 0];
  newBdeg := &+[ newbvals[j]*Degree(allsup[j]) : j in [1..#allsup] | newbvals[j] ge 0];
  printf "Final degree of A = %o. Final degree of B = %o.\n",newAdeg,newBdeg;

  if (newAdeg gt Adeg) and (newBdeg gt Bdeg) then
    newA := -27*rfunc^2*xfunc;
    newB := 54*rfunc^3*xfunc^2;
  else
    newA := -27*rfunc^2*xfunc*func^4;
    newB := 54*rfunc^3*xfunc^2*func^6;
  end if;

  // Now, let's do the simplification at places of Q.

  numA0 := Coefficients(Numerator(newA));
  d := LCM([ Denominator(numA0[i]) : i in [1..#numA0]]);
  numA0 := [ Integers()!(d*numA0[i]) : i in [1..#numA0]];
  denomA0 := Coefficients(Denominator(newA));
  d := LCM([ Denominator(denomA0[i]) : i in [1..#denomA0]]);
  denomA0 := [ Integers()!(d*denomA0[i]) : i in [1..#denomA0]];
  numA := GCD(numA0);
  denomA := GCD(denomA0);

  numB0 := Coefficients(Numerator(newB));
  d := LCM([ Denominator(numB0[i]) : i in [1..#numB0]]);
  numB0 := [ Integers()!(d*numB0[i]) : i in [1..#numB0]];
  denomB0 := Coefficients(Denominator(newB));
  d := LCM([ Denominator(denomB0[i]) : i in [1..#denomB0]]);
  denomB0 := [ Integers()!(d*denomB0[i]) : i in [1..#denomB0]];
  numB := GCD(numB0);
  denomB := GCD(denomB0);

  pf1 := PrimeFactors(numA);
  pf2 := PrimeFactors(denomA);
  pf3 := PrimeFactors(numB);
  pf4 := PrimeFactors(denomB);
  allprimes := pf1;
  for j in [1..#pf2] do
    if not pf2[j] in allprimes then
      Append(~allprimes,pf2[j]);
    end if;
  end for;
  for j in [1..#pf3] do
    if not pf3[j] in allprimes then
      Append(~allprimes,pf3[j]);
    end if;
  end for;
  for j in [1..#pf4] do
    if not pf4[j] in allprimes then
      Append(~allprimes,pf4[j]);
    end if;
  end for;
  change := [ Min(Round(Valuation(numA/denomA,allprimes[j])/4),Round(Valuation(numB/denomB,allprimes[j])/6)) : j in [1..#allprimes]];
  changemult := &*[ allprimes[j]^change[j] : j in [1..#allprimes]];
  newA := newA/changemult^4;
  newB := newB/changemult^6;

  // Reparse newA and newB to be ratios of elements in the polynomial ring. 

  newA2num0 := Evaluate(Numerator(newA),[polyring.i : i in [1..Rank(polyring)-1]]);
  cofs1, mons1 := CoefficientsAndMonomials(newA2num0);
  degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
  newA2denom0 := Evaluate(Denominator(newA),[polyring.i : i in [1..Rank(polyring)-1]]);
  cofs2, mons2 := CoefficientsAndMonomials(newA2denom0);
  degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
  deg := Max(degnum,degdenom);
  newA2num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
  newA2denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];

  newB2num0 := Evaluate(Numerator(newB),[polyring.i : i in [1..Rank(polyring)-1]]);
  cofs1, mons1 := CoefficientsAndMonomials(newB2num0);
  degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
  newB2denom0 := Evaluate(Denominator(newB),[polyring.i : i in [1..Rank(polyring)-1]]);
  cofs2, mons2 := CoefficientsAndMonomials(newB2denom0);
  degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
  deg := Max(degnum,degdenom);
  newB2num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
  newB2denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];

  return newA2num, newA2denom, newB2num, newB2denom; 
end function;

// The function below takes as input a group and outputs the maximal N for which the universal elliptic curve
// has a point of order N. 
function torsionorder(GG)
  N0 := Characteristic(BaseRing(GG));
  maxtors := 1;
  for d in Divisors(N0) do
    if (d gt maxtors) then
      torsdeg := GL2TorsionDegree(sub<GL(2,Integers(d)) | [ Transpose(t) : t in Generators(GG)]>);
      if torsdeg eq 1 then
        maxtors := d;
      end if;
    end if;
  end for;
  return maxtors;
end function;

// The function below takes as input a curve C, its function field QC, the polynomial ring used for the curve C, 
// elements A and B in QC, and an d >= 3.  It finds points of order d on V^2 = U^3 + A*U + B
// and puts the curve into the form V^2 + a1 UV + a3 V = U^3 + a2 U^2.
// The function below handles the case that d = 2.
function KTform(C,QC,polyring,A,B,d)
  // First, tweak our QC if C is P^1. This fixes a Magma bug, which should be fixed in V2.28-8.
  Ffieldpoly := 0;
  if #DefiningEquations(C) eq 0 then
    P1case := true;
    newQC := FunctionField(Rationals());
    Ffieldpoly := FunctionField(newQC);
  else
    P1case := false;
    Ffieldpoly := FunctionField(QC);
  end if;  
  if P1case then
    Afunc := Evaluate(Numerator(A),[newQC.1,1])/Evaluate(Denominator(A),[newQC.1,1]);
    Bfunc := Evaluate(Numerator(B),[newQC.1,1])/Evaluate(Denominator(B),[newQC.1,1]);
  else
    vals := [ QC.i : i in [1..Rank(polyring)-1]] cat [QC!1];    
    Afunc := Evaluate(Numerator(A),vals)/Evaluate(Denominator(A),vals);
    Bfunc := Evaluate(Numerator(B),vals)/Evaluate(Denominator(B),vals);
  end if;
  rawE := EllipticCurve([0,0,0,Afunc,Bfunc]);
  divpol0 := &*[ Evaluate(DivisionPolynomial(rawE,e),Ffieldpoly.1)^(MoebiusMu(Integers()!(d/e))) : e in Divisors(d)];
  divpol := Numerator(divpol0);
  // The roots of divpol are x-coordinates of points of exact order d.
  printf "Finding roots of division polynomial.\n";
  rts := Roots(divpol);
  printf "Done.\n";
  pts := [];
  for j in [1..#rts] do
    chk, P := IsPoint(rawE,rts[j][1]);
    if chk then
      if P[2] ne 0 then
        Append(~pts,-P);
      end if;
    end if;
  end for;
  rets := [];
  for k in [1..#pts] do
    printf "Trying point %o of %o.\n",k,#pts;
    x0 := pts[k][1];
    y0 := pts[k][2];
    if P1case then
      x0 := Evaluate(x0,QC.1);
      y0 := Evaluate(y0,QC.1);
    end if;
    alist := aInvariants(rawE);
    K<x,y> := PolynomialRing(QC,2);
    if P1case then
      alist := [ Evaluate(alist[i],QC.1) : i in [1..#alist]];
    end if;
    pol := y^2 + alist[1]*x*y + alist[3]*y - (x^3 + alist[2]*x^2 + alist[4]*x + alist[5]);
    // Step 1 - Move (x0,y0) to the origin.
    pol2 := Evaluate(pol,[x+x0,y+y0]);
    // Step 2 - Rotate so tangent line is horizontal. This step will crash if (x0,y0) has order 2.
    newalist := [ MonomialCoefficient(pol2,x*y), -MonomialCoefficient(pol2,x^2), MonomialCoefficient(pol2,y), -MonomialCoefficient(pol2,x), 0];
    s := newalist[4]/newalist[3];
    pol3 := Evaluate(pol2,[x,y+s*x]);
    a1 := MonomialCoefficient(pol3,x*y);
    a2 := -MonomialCoefficient(pol3,x^2);
    a3 := MonomialCoefficient(pol3,y);
    /* The following is a reduction process that could potentially improve a1, a2 and a3.
    It requires a low degree effective divisor E, but it also doesn't seem to help at all
    if we start with a pre-simplified short Weierstrass form
    printf "Decomposing divisors.\n";
    decomp1 := Decomposition(Divisor(a1));
    decomp2 := Decomposition(Divisor(a2));
    decomp3 := Decomposition(Divisor(a3));
    allsup := [ decomp1[i][1] : i in [1..#decomp1]];
    for i in [1..#decomp2] do
      if not (decomp2[i][1] in allsup) then
        Append(~allsup,decomp2[i][1]);
      end if;
    end for;
    for i in [1..#decomp3] do
      if not (decomp3[i][1] in allsup) then
        Append(~allsup,decomp3[i][1]);
      end if;
    end for;
    // Valuation of a1, a2, and a3 at all divisors in their support
    a1vals := [ Valuation(a1,allsup[j]) : j in [1..#allsup]];
    a2vals := [ Valuation(a2,allsup[j]) : j in [1..#allsup]];
    a3vals := [ Valuation(a3,allsup[j]) : j in [1..#allsup]];
    // A divisor D to "take out". We want to remove D from a1, 2D from a2, and 3D from a3.
    changevals := [ Min([ a1vals[j], Round(a2vals[j]/2),Round(a3vals[j]/3)]) : j in [1..#allsup]];
    change := &+[ changevals[j]*allsup[j] : j in [1..#allsup]];

    a1deg := &+[ a1vals[j]*Degree(allsup[j]) : j in [1..#allsup] | a1vals[j] ge 0 ];
    a2deg := &+[ a2vals[j]*Degree(allsup[j]) : j in [1..#allsup] | a2vals[j] ge 0 ];
    a3deg := &+[ a3vals[j]*Degree(allsup[j]) : j in [1..#allsup] | a3vals[j] ge 0 ];
    printf "Starting degree of a1, a2 and a3 are %o, %o, %o.\n",a1deg,a2deg,a3deg;

    redD, rr, E, func := Reduction(change,E);
    // We have change = redD + r*E - div(func).
    // In this case, redD has degree 0 and the support of E is contained in allsup
    newa1vals := [ a1vals[j] - Valuation(change,allsup[j]) + Valuation(redD,allsup[j]) + rr*Valuation(E,allsup[j]) : j in [1..#allsup]];
    newa2vals := [ a2vals[j] - 2*Valuation(change,allsup[j]) + 2*Valuation(redD,allsup[j]) + 2*rr*Valuation(E,allsup[j]) : j in [1..#allsup]];
    newa3vals := [ a3vals[j] - 3*Valuation(change,allsup[j]) + 3*Valuation(redD,allsup[j]) + 3*rr*Valuation(E,allsup[j]) : j in [1..#allsup]];
    newa1deg := &+[ newa1vals[j]*Degree(allsup[j]) : j in [1..#allsup] | a1vals[j] ge 0 ];
    newa2deg := &+[ newa2vals[j]*Degree(allsup[j]) : j in [1..#allsup] | a2vals[j] ge 0 ];
    newa3deg := &+[ newa3vals[j]*Degree(allsup[j]) : j in [1..#allsup] | a3vals[j] ge 0 ];
    */
    // Post-processing
    allprimes := [];
    if (a1 ne 0) then
      newa1num0 := Evaluate(Numerator(a1),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs1, mons1 := CoefficientsAndMonomials(newa1num0);
      degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
      newa1denom0 := Evaluate(Denominator(a1),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs2, mons2 := CoefficientsAndMonomials(newa1denom0);
      degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
      deg := Max(degnum,degdenom);
      newa1num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
      newa1denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];
      numa1 := Coefficients(newa1num);
      d := LCM([ Denominator(numa1[i]) : i in [1..#numa1]]);
      numa1 := [ Integers()!(d*numa1[i]) : i in [1..#numa1]];
      denoma1 := Coefficients(newa1denom);
      d := LCM([ Denominator(denoma1[i]) : i in [1..#denoma1]]);
      denoma1 := [ Integers()!(d*denoma1[i]) : i in [1..#denoma1]];
      numa1 := GCD(numa1);
      denoma1 := GCD(denoma1);
      allprimes := PrimeFactors(numa1*denoma1);
    else
      newa1num := polyring!0;
      newa1denom := polyring!1;
      numa1 := 0;
      denoma1 := 0;
    end if;
    if (a2 ne 0) then
      newa2num0 := Evaluate(Numerator(a2),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs1, mons1 := CoefficientsAndMonomials(newa2num0);
      degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
      newa2denom0 := Evaluate(Denominator(a2),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs2, mons2 := CoefficientsAndMonomials(newa2denom0);
      degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
      deg := Max(degnum,degdenom);
      newa2num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
      newa2denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];
      numa2 := Coefficients(newa2num);
      d := LCM([ Denominator(numa2[i]) : i in [1..#numa2]]);
      numa2 := [ Integers()!(d*numa2[i]) : i in [1..#numa2]];
      denoma2 := Coefficients(newa2denom);
      d := LCM([ Denominator(denoma2[i]) : i in [1..#denoma2]]);
      denoma2 := [ Integers()!(d*denoma2[i]) : i in [1..#denoma2]];
      numa2 := GCD(numa2);
      denoma2 := GCD(denoma2);
      if #allprimes eq 0 then
        allprimes := PrimeFactors(numa2*denoma2);
      else
        for p in PrimeFactors(numa2) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
        for p in PrimeFactors(denoma2) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
      end if;
    else
      newa2num := polyring!0;
      newa2denom := polyring!1;
      numa2 := 0;
      denoma2 := 0;
    end if;    
    if (a3 ne 0) then
      newa3num0 := Evaluate(Numerator(a3),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs1, mons1 := CoefficientsAndMonomials(newa3num0);
      degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
      newa3denom0 := Evaluate(Denominator(a3),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs2, mons2 := CoefficientsAndMonomials(newa3denom0);
      degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
      deg := Max(degnum,degdenom);
      newa3num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
      newa3denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];
      numa3 := Coefficients(newa3num);
      d := LCM([ Denominator(numa3[i]) : i in [1..#numa3]]);
      numa3 := [ Integers()!(d*numa3[i]) : i in [1..#numa3]];
      denoma3 := Coefficients(newa3denom);
      d := LCM([ Denominator(denoma3[i]) : i in [1..#denoma3]]);
      denoma3 := [ Integers()!(d*denoma3[i]) : i in [1..#denoma3]];
      numa3 := GCD(numa3);
      denoma3 := GCD(denoma3);
      if #allprimes eq 0 then
        allprimes := PrimeFactors(numa3*denoma3);
      else
        for p in PrimeFactors(numa3) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
        for p in PrimeFactors(denoma3) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
      end if;
    else
      newa3num := polyring!0;
      newa3denom := polyring!1;
      numa3 := 0;
      denoma3 := 0;
    end if;
    nums := [numa1,numa2,numa3];
    denoms := [denoma1,denoma2,denoma3];
    //printf "nums = %o, denoms = %o.\n",nums,denoms;
    change := [ Min([ Round(Valuation(nums[i]/denoms[i],allprimes[j])/i) : i in [1..3] | nums[i] ne 0]) : j in [1..#allprimes]];
    changemult := &*[ allprimes[j]^change[j] : j in [1..#allprimes]];
    nm := Numerator(1/changemult);
    dm := Denominator(1/changemult);
    newa1num := newa1num/dm;
    newa2num := newa2num/dm^2;
    newa3num := newa3num/dm^3;
    newa1denom := newa1denom*nm;
    newa2denom := newa2denom*nm^2;
    newa3denom := newa3denom*nm^3;
    Append(~rets,[newa1num,newa1denom,newa2num,newa2denom,newa3num,newa3denom]);
  end for;
  lengths := [ #Sprintf("%o",rets[i]) : i in [1..#rets]];
  min, bestind := Min(lengths);
  return rets[bestind];
end function;

// The function below takes a universal elliptic curve in short Weierstrass form
// V^2 = U^3 + A*U + B and writes it in the form V^2 = U^3 + a*U^2 + b*U
function KTform2(C,QC,polyring,A,B)
  // First, tweak our QC if C is P^1. This fixes a Magma bug, which should be fixed in V2.28-8.
  Ffieldpoly := 0;
  if #DefiningEquations(C) eq 0 then
    P1case := true;
    newQC := FunctionField(Rationals());
    Ffieldpoly := FunctionField(newQC);
  else
    P1case := false;
    Ffieldpoly := FunctionField(QC);
  end if;  
  if P1case then
    Afunc := Evaluate(Numerator(A),[newQC.1,1])/Evaluate(Denominator(A),[newQC.1,1]);
    Bfunc := Evaluate(Numerator(B),[newQC.1,1])/Evaluate(Denominator(B),[newQC.1,1]);
  else
    vals := [ QC.i : i in [1..Rank(polyring)-1]] cat [QC!1];    
    Afunc := Evaluate(Numerator(A),vals)/Evaluate(Denominator(A),vals);
    Bfunc := Evaluate(Numerator(B),vals)/Evaluate(Denominator(B),vals);
  end if;
  rawE := EllipticCurve([0,0,0,Afunc,Bfunc]);
  divpol := DivisionPolynomial(rawE,2);
  // The roots of divpol are x-coordinates of points of exact order d.
  printf "Finding roots of division polynomial.\n";
  rts := Roots(divpol);
  printf "Done. There were %o.\n",#rts;
  pts := [];
  for j in [1..#rts] do
    chk, P := IsPoint(rawE,rts[j][1]);
    if chk then
      Append(~pts,P);
    end if;
  end for;
  rets := [];
  assert #pts ge 1;
  for k in [1..#pts] do
    //printf "Trying point %o of %o.\n",k,#pts;
    x0 := pts[k][1];
    y0 := pts[k][2];
    if P1case then
      x0 := Evaluate(x0,QC.1);
      y0 := Evaluate(y0,QC.1);
    end if;
    alist := aInvariants(rawE);
    K<x,y> := PolynomialRing(QC,2);
    if P1case then
      alist := [ Evaluate(alist[i],QC.1) : i in [1..#alist]];
    end if;
    pol := y^2 + alist[1]*x*y + alist[3]*y - (x^3 + alist[2]*x^2 + alist[4]*x + alist[5]);
    // Step 1 - Move (x0,y0) to the origin.
    pol2 := Evaluate(pol,[x+x0,y+y0]);
    a2 := -MonomialCoefficient(pol2,x^2);
    a4 := -MonomialCoefficient(pol2,x);
    //printf "Initial a2 = %o, initial a4 = %o.\n",a2,a4;
    /* The following is a reduction process that could potentially improve a2 and a4.
    It requires a low degree effective divisor E, but it also doesn't seem to help at all
    if we start with a pre-simplified short Weierstrass form
    printf "Decomposing divisors.\n";
    decomp1 := Decomposition(Divisor(a2));
    decomp2 := Decomposition(Divisor(a4));
    allsup := [ decomp1[i][1] : i in [1..#decomp1]];
    for i in [1..#decomp2] do
      if not (decomp2[i][1] in allsup) then
        Append(~allsup,decomp2[i][1]);
      end if;
    end for;
    // Valuation of a2, a4 at all divisors in their support
    a2vals := [ Valuation(a2,allsup[j]) : j in [1..#allsup]];
    a4vals := [ Valuation(a4,allsup[j]) : j in [1..#allsup]];
    // A divisor D to "take out". We want to remove 2D from a2, and 4D from a4.
    changevals := [ Min([ a1vals[j], Round(a2vals[j]/2),Round(a4vals[j]/4)]) : j in [1..#allsup]];
    change := &+[ changevals[j]*allsup[j] : j in [1..#allsup]];

    a2deg := &+[ a2vals[j]*Degree(allsup[j]) : j in [1..#allsup] | a2vals[j] ge 0 ];
    a4deg := &+[ a4vals[j]*Degree(allsup[j]) : j in [1..#allsup] | a4vals[j] ge 0 ];
    printf "Starting degree of a2 and a4 are %o, %o, %o.\n",a2deg,a4deg;

    redD, rr, E, func := Reduction(change,E);
    // We have change = redD + r*E - div(func).
    // In this case, redD has degree 0 and the support of E is contained in allsup
    newa2vals := [ a2vals[j] - 2*Valuation(change,allsup[j]) + 2*Valuation(redD,allsup[j]) + 2*rr*Valuation(E,allsup[j]) : j in [1..#allsup]];
    newa4vals := [ a4vals[j] - 4*Valuation(change,allsup[j]) + 4*Valuation(redD,allsup[j]) + 4*rr*Valuation(E,allsup[j]) : j in [1..#allsup]];
    newa2deg := &+[ newa2vals[j]*Degree(allsup[j]) : j in [1..#allsup] | a2vals[j] ge 0 ];
    newa4deg := &+[ newa4vals[j]*Degree(allsup[j]) : j in [1..#allsup] | a4vals[j] ge 0 ];
    */
    // Post-processing
    allprimes := [];
    if (a2 ne 0) then
      newa2num0 := Evaluate(Numerator(a2),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs1, mons1 := CoefficientsAndMonomials(newa2num0);
      degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
      newa2denom0 := Evaluate(Denominator(a2),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs2, mons2 := CoefficientsAndMonomials(newa2denom0);
      degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
      deg := Max(degnum,degdenom);
      newa2num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
      newa2denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];
      numa2 := Coefficients(newa2num);
      d := LCM([ Denominator(numa2[i]) : i in [1..#numa2]]);
      numa2 := [ Integers()!(d*numa2[i]) : i in [1..#numa2]];
      denoma2 := Coefficients(newa2denom);
      d := LCM([ Denominator(denoma2[i]) : i in [1..#denoma2]]);
      denoma2 := [ Integers()!(d*denoma2[i]) : i in [1..#denoma2]];
      numa2 := GCD(numa2);
      denoma2 := GCD(denoma2);
      if #allprimes eq 0 then
        allprimes := PrimeFactors(numa2*denoma2);
      else
        for p in PrimeFactors(numa2) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
        for p in PrimeFactors(denoma2) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
      end if;
    else
      newa2num := polyring!0;
      newa2denom := polyring!1;
      numa2 := 0;
      denoma2 := 0;
    end if;    
    if (a4 ne 0) then
      newa4num0 := Evaluate(Numerator(a4),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs1, mons1 := CoefficientsAndMonomials(newa4num0);
      degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
      newa4denom0 := Evaluate(Denominator(a4),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs2, mons2 := CoefficientsAndMonomials(newa4denom0);
      degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
      deg := Max(degnum,degdenom);
      newa4num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
      newa4denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];
      numa4 := Coefficients(newa4num);
      d := LCM([ Denominator(numa4[i]) : i in [1..#numa4]]);
      numa4 := [ Integers()!(d*numa4[i]) : i in [1..#numa4]];
      denoma4 := Coefficients(newa4denom);
      d := LCM([ Denominator(denoma4[i]) : i in [1..#denoma4]]);
      denoma4 := [ Integers()!(d*denoma4[i]) : i in [1..#denoma4]];
      numa4 := GCD(numa4);
      denoma4 := GCD(denoma4);
      if #allprimes eq 0 then
        allprimes := PrimeFactors(numa4*denoma4);
      else
        for p in PrimeFactors(numa4) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
        for p in PrimeFactors(denoma4) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
      end if;
    else
      newa4num := polyring!0;
      newa4denom := polyring!1;
      numa4 := 0;
      denoma4 := 0;
    end if;
    nums := [numa2,numa4];
    denoms := [denoma2,denoma4];
    //printf "nums = %o, denoms = %o.\n",nums,denoms;
    if #allprimes eq 0 then
      changemult := 1;
    else
      change := [ Min([ Round(Valuation(nums[i]/denoms[i],allprimes[j])/i) : i in [1..2] | nums[i] ne 0]) : j in [1..#allprimes]];
      changemult := &*[ allprimes[j]^change[j] : j in [1..#allprimes]];
    end if;  
    nm := Numerator(1/changemult);
    dm := Denominator(1/changemult);
    newa2num := newa2num/dm^2;
    newa4num := newa4num/dm^4;
    newa2denom := newa2denom*nm^2;
    newa4denom := newa4denom*nm^4;
    //printf "Final a2 = %o/%o, final a4 = %o/%o.\n",newa2num,newa2denom,newa4num,newa4denom;
    Append(~rets,[newa2num,newa2denom,newa4num,newa4denom]);
  end for;
  lengths := [ #Sprintf("%o",rets[i]) : i in [1..#rets]];
  min, bestind := Min(lengths);
  return rets[bestind];
end function;

function FinalReduction(C,H0,QC,polyring,newA2num,newA2denom,newB2num,newB2denom)
  d := torsionorder(H0);
  a_inv := [];
  if d eq 1 then
    a_inv := [newA2num,newA2denom,newB2num,newB2denom];
    printf "We're done.\n";
  end if;
  if d eq 2 then
    lst := KTform2(C,QC,polyring,newA2num/newA2denom,newB2num/newB2denom);
    a_inv := [0, lst[1]/lst[2], 0, lst[3]/lst[4], 0];
    printf "Final model is a2 = (%o)/(%o), a4 = (%o)/(%o).\n",lst[1],lst[2],lst[3],lst[4];
  end if;
  if d ge 3 then
    use := Min([ e : e in Divisors(d) | e ge 3]);
    lst := KTform(C,QC,polyring,newA2num/newA2denom,newB2num/newB2denom,use);
    a_inv := [lst[1]/lst[2], lst[3]/lst[4], lst[5]/lst[6], 0];
    printf "Final model is a1 = (%o)/(%o), a2 = (%o)/(%o), a3 = (%o)/(%o).\n",lst[1],lst[2],lst[3],lst[4],lst[5],lst[6];
  end if;
  return a_inv;
end function;

intrinsic ComputeUnivECModels(InputLabels::MonStgElt, generators::MonStgElt) -> SeqEnum[RngMPolElt]
{Main function that computes a model for the universal elliptic curve of a fine curve}
  // Read in labels 
  tttt := Cputime();
  LinesOfInputFile := Split(Read(InputLabels), "\n");
  for line in LinesOfInputFile do 
    tmp := Split(line, ":");
    l1 := tmp[1];
    quadratic_refinements := Split(tmp[2], ",");
    l0 := quadratic_refinements[1];
    N0 := StringToInteger(Split(l0,".")[1], 10); // Level for H_0
    gens0 := GetModularCurveGenerators(l0, generators);
    N := StringToInteger(Split(l1,".")[1], 10); // Level for <H,-I>
    GL2 := GL(2,Integers(N));
    SL2 := SL(2,Integers(N)); 
    U,pi:=UnitGroup(Integers(N));
    gens := gens0 cat [ GL(2,Integers(N0))![-1,0,0,-1]];
    gens := [ Transpose(g) : g in gens];
    gp := sub<GL(2,Integers(N0))|gens>;
    _, gp := GL2Level(gp);
    M := CreateModularCurveRec(N, Generators(gp) : use_minimal_level := false);
    printf "Starting model computation with low precision.\n";
    ttemp := Cputime();

    M, maxd, mind, maxprec, degL, geomhyper := ComputeModelwithPrec(M);
    modeltime := Cputime(ttemp); 
    printf "Model and modular forms done. Total time = %o.\n",modeltime;
  // Post-processing on q-expansions

  postproctime := Cputime();

  // Step 1 - Determine Galois orbits of cusps and choose one representative from each
  printf "Determining Galois action on cusps.\n";
  chosencusps := CuspsOrbits(M);
  printf "Using %o Fourier expansions (out of %o).\n",#chosencusps,#M`cusps;

  G := M`G;

  // Step 2 - Rewrite modular coefficients as elements of smaller subfield
  printf "Rewriting Fourier expansions over smaller fields.\n";
  modforms, totalprec, KKlist := RewriteFourierExpansion(M, chosencusps, maxprec);
  postproctime := Cputime(postproctime);
  printf "Done with post-processing. Time taken was %o.\n",postproctime;

  // Step 3 - Build log-canonicalish ring
  polyring := PolynomialRing(Rationals(),#modforms,"grevlex");
  varsnames := ["x","y","z","w","t","u","v","r","s","a","b","c","d","e","f","g","h","i","k","l","m","n","o","p","q","j"];
  AssignNames(~polyring,[varsnames[j] : j in [1..#modforms]]);
  Ffield := FieldOfFractions(polyring);

  ttime := Cputime();
  canring,vars := CanonicalRing(polyring, M, chosencusps, modforms, maxd);
  canringtime := Cputime(ttemp);
  printf "Canonical ring time was %o.\n",canringtime;

  // Step 4 - Write down j-map 
  ttemp := Cputime();
  FFFF<qN> := LaurentSeriesRing(Rationals());
  num, denom, C := jMap(polyring, M, chosencusps, canring, modforms, [totalprec,maxprec,maxd,mind]);

  printf "Model time = %o.\n",modeltime;
  printf "Canonical ring time = %o.\n",canringtime;
  printf "Total coarse model time was %o sec.\n",Cputime(tttt);
  printf "Model represented by %o.\n",C;


  // Processing index-2 refinements 
  for ele in quadratic_refinements do
  //try 
      l2 := ele;
      print <l1, l2>;

  //tttt := Cputime();

  N2 := StringToInteger(Split(l2,".")[1],10); // Level for H 
  gens0 := GetModularCurveGenerators(l2, generators);
  gens0 := [ Transpose(g) : g in gens0 ];

  H0 := sub<GL(2,Integers(N2))|gens0>;
  tmpgp := GL2Lift(gp, N2);
  boo, gamma := IsConjugateSubgroup(GL(2, Integers(N2)), tmpgp, H0);
  assert boo;
  H0 := Conjugate(H0, gamma);
  gens0 := Generators(H0);

  printf "Starting fine model computation.\n";
  g := StringToInteger(Split(l1,".")[3],10);
  printf "Genus of modular curve is %o.\n",g;

  M2 := CreateModularCurveRec(N2,gens0);
  irregcusps := not (&and M2`regular);
  if irregcusps then
    printf "There are irregular cusps!!!\n";
  end if;
    // What happens if X_H has irregualr cusps? Then the Fourier expansion of wt. 3 modular forms
    // might not be power series in q^(1/N)?

  // Step 5 - Compute a weight 3 modular form on the fine curve 

  printf "Finding weight 3 modular forms.\n";
  tt := Cputime();
  fnum, fdenom := RatioFromWeight3Form(M, M2, [*polyring,geomhyper,KKlist,canring,chosencusps,degL,irregcusps,totalprec,maxprec*]);
  mftime := Cputime(tt);
  printf "Time needed was %o.\n",mftime;

  j := (Ffield!(num/denom));
  r := (Ffield!(fnum/fdenom));
  x := 1 - 1728/j;
  A := -27*r^2*x;
  B := 54*r^3*x^2;

  // Step 6 - Reduce equation 
  // Now, let's try to do some simplifying. The code below is likely to only work well in the case
  // that we can quickly do divisor and Riemann-Roch computations on C.
  QC := FunctionField(C);
  E := LowDegreeDivisor(C, M`genus);
  printf "Using effective divisor of degree %o", Degree(E);
  newA2num, newA2denom, newB2num, newB2denom := FirstReduction(polyring, C, E, r, x, A, B);

  printf "Modular curve model: %o.\n",[ Evaluate(M`psi[j],vars) : j in [1..#M`psi]];
  printf "Numerator of A = %o.\n",newA2num;
  printf "Denominator of A = %o.\n",newA2denom;
  printf "Numerator of B = %o.\n",newB2num;
  printf "Denominator of B = %o.\n",newB2denom;

  printf "Starting A size = %o. Ending A size = %o.\n",#Sprintf("%o",A),#Sprintf("%o",newA2num/newA2denom);
  printf "Starting B size = %o. Ending B size = %o.\n",#Sprintf("%o",B),#Sprintf("%o",newB2num/newB2denom);

  a_inv := FinalReduction(C,H0,QC,polyring,newA2num,newA2denom,newB2num,newB2denom);
  print(a_inv);
  return a_inv;

  // fprintf "univmodels_level_3-10.txt", "%o|[%o/%o,%o/%o]\n", l2, newA2num, newA2denom, newB2num, newB2denom; 

  //catch e
    //fprintf "errors.txt", "l1:=%o, l2:=%o\n", l1, l2;
    //printf "had an error somewhere";
  //end try; 

  end for;
  end for;
end intrinsic;

//quit;


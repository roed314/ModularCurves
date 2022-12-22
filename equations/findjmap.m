// This script computes the map to the j-line for a non-hyperelliptic X_H.
// It takes the label as a command line parameter.
// Something like magma l:=7.168.3.1 findjmap.m

// AttachSpec("equations.spec");
// load "LMFDB_interface.m";
// load "GL2GroupTheory.m";
// load "ModularCurvesMy.m";

// This will now run in the main script

/*
if (not assigned l) then
  printf "This script assumes that l, the label of the X_H to compute, is given as a command line paramter.\n";
  printf "Something like magma l:=7.168.3.1 findjmap.m\n";
  quit;  
end if;
*/

// Simplify a Q-vector space. This script takes a matrix M
// and finds the lattice of elements L where all the coordinates are integers.
// Then it finds an LLL-reduced basis for that lattice. It returns
// a square matrix that indicates which linear combinations of the rows of M
// are the LLL-reduced basis

intrinsic MissingMonomials(I, maxd) -> SeqEnum
{Finds the monomials of degree 2..maxd that are not contained in the monomial ideal I.
 Returns a sequence M so that the missing monomials of degree d can be accessed by M[d].  Note that M[1] = [], regardless of I.}
    R := Parent(I.1);
    Md := [mon : mon in MonomialsOfDegree(R, 2) | not (mon in I)];
    M := [[], Md];
    r := Rank(R);
    for d in [3..maxd] do
        nmon := Binomial(r+d-1, d);
        if nmon gt r * #M[#M] then
            Md := {mon * R.i : mon in M[#M], i in [1..r]};
        else
            Md := MonomialsOfDegree(R, d);
        end if;
        Append(~M, [mon : mon in Md | not mon in I]);
    end for;
    return M;
end intrinsic;

function nicefy(M)
  M0, T := EchelonForm(M);
  // Rows of T give current basis.
  ee := Eltseq(M0);
  denom := LCM([ Denominator(ee[i]) : i in [1..#ee]]);
  vprint User1: Sprintf("Nicefying %ox%o matrix.",NumberOfRows(M),NumberOfColumns(M));
  M2 := Matrix(Integers(),NumberOfRows(M),NumberOfColumns(M),[ denom*ee[i] : i in [1..#ee]]);
  vprint User1: "Computing saturation.";
  //SetVerbose("Saturation",2);
  AA := Saturation(M2);
  vprint User1: "Done.";
  chk, mult := IsConsistent(ChangeRing(M2,Rationals()),ChangeRing(AA,Rationals()));
  curbat := denom*mult*T;
  vprint User1: "Calling LLL.";
  newlatbasismat, change := LLL(AA : Proof := false);
  vprint User1: "Done.";
  finalbat := ChangeRing(change,Rationals())*curbat;
  return finalbat;
end function;

// This function takes a subgroup of GL(1,Integers(N)) and an instance of Q(zeta_N)
// and returns a simple representation of the corresponding subfield of
// Q(zeta_N), as well as a primitive element for the extension.

function fieldfind(G, K)
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
end function;

//intrinsic FindJMap(N::RngIntElt, gens::SeqEnum) -> Crv, RngMPolElt, RngMPolElt
//{.}
// Outputs X, j, model_type,
function FindJMap(N, gens, label)
  tttt := ReportStart(label, "FindJMap");
//  gens := GetModularCurveGenerators(l);

//  N := StringToInteger(Split(l,".")[1],10);
//  gens := [ Transpose(g) : g in gens];
  gp := sub<GL(2,Integers(N))|gens>;

  M := CreateModularCurveRec(N,gens);
  
  ttemp := ReportStart(label, "model and modular forms");
  vprint User1: "Starting model computation with low precision";
  prec := RequiredPrecision(M);
  M := FindModelOfXG(M,prec);
  mult := M`mult;
  if (not assigned M`prec) then
    M`prec := prec;
  end if;

  if (M`genus eq 1) and (assigned M`has_point) and (M`has_point) then
    // I'm just taking a guess on the precision here.
    // Test cases: 6.6.1.1, 6.12.1.1, 11.55.1.1, 8.48.1.3, 9.54.1.1, 20.72.1.23, 8.96.1.109
    // Minimal prec for 11.55.1.1 is 81
    success := false;
    prec := 2*M`index;
    // I'm pretty sure we only need 2*index + N, 
    // but just in case we loop
    while (not success) do
	M := FindModelOfXG(M,prec);
	PP := Parent(M`f[1][1]);
	jinv0 := jInvariant(PP.1);
	jinv := Evaluate(jinv0,PP.1^N);
	jinv2 := [ jinv : i in [1..M`vinf]];
	success, ecjmap := FindRelationElliptic(M,jinv2);
	prec +:= N;
    end while;

    vprint User1: Sprintf("Minimal model is %o.", M`C);
    vprint User1: Sprintf("j-map is %o.", ecjmap);
    // Write data to a file here and then stop.
    // 5 is the code for hyperelliptic models
    // For now, we decided it includes Weierstrass equations
    ReportEnd(label, "model and modular forms", ttemp);
    ReportEnd(label, "FindJMap", tttt);
    return M`C, ecjmap, 5, M`f cat [[1 : i in [1..#M`cusps]]], M;
  end if;

  maxd := 0;
  mind := 0;
  maxprec := 0;
  geomhyper := false;
  // Compute the degree of the line bundle used
  if (M`mult ne [ 1 : i in [1..M`vinf]]) or (M`k ne 2) then
      vprint User1: "Curve is geometrically hyperelliptic.";
      geomhyper := true;
      k := M`k;
      degL:= ((k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps) - (&+M`mult);
      old_degL := 0;
      while (old_degL ne degL) do
	  old_degL := degL;
	  maxd := Floor((M`index + M`genus - 1)/degL) + 1;
	  mind := maxd - 1;
	  vprint User1: Sprintf("Smallest degree that might work = %o. The degree %o definitely works.", mind, maxd);
	  maxprec := Floor(N*(M`k*maxd/12 + 1)) + 1;
	  if (maxprec gt M`prec) then
	      vprint User1: "Now that we know it's geometrically hyperelliptic, we need more precision.";
	      vprint User1: Sprintf("New precision chosen = %o.", maxprec);
	      delete M`has_point;
	      M := FindModelOfXG(M,maxprec);
	      vprint User1: "Recomputation of modular forms done.";
	      k := M`k;
	      degL:= ((k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps) - (&+M`mult);
	  end if;
      end while;
  else
      vprint User1: "Curve is not geometrically hyperelliptic.";
      maxd := Floor((M`index)/(2*M`genus-2) + 3/2);
      if ((maxd-1) ge (M`index)/(2*M`genus-2)) and ((maxd-1) le ((M`index)/(2*M`genus-2) + 1/2)) then
	  mind := maxd-1;
	  vprint User1: Sprintf("The smallest degree that might work is %o.", mind);
	  vprint User1: Sprintf("Degree %o definitly works.", maxd);
      else
	  mind := maxd;
	  vprint User1: Sprintf("The smallest degree that might work is %o and it definitely works.", maxd);
      end if;
      maxprec := Floor(N*(1 + maxd/6)+1);
      if (maxprec gt M`prec) then
	  vprint User1: "Now that we know it's non-hyperelliptic, we need more precision.";
	  vprint User1: Sprintf("New precision chosen = %o.", maxprec);
	  delete M`has_point;
	  M := FindModelOfXG(M,maxprec);
	  vprint User1: "Recomputation of modular forms done.";
      end if;
  end if;
  modeltime := Cputime(ttemp);
  ReportEnd(label, "model and modular forms", ttemp);

  // Post-processing on q-expansions

  // Step 1 - Determine Galois orbits of cusps and choose one representative from each

  // Computes the action of (Z/NZ)^* on the cusps of X_G.  This corresponds to the action of Gal(Q(zeta_N)/Q) on the cusps.
  postproctime := ReportStart(label, "determining Galois action on cusps");
  G := gp;
  G0 := gp;
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
  // Let H and H0 be the intersection of G and G0, respectively, with SL(2,Z/N).  We now compute the action of H0/H on the cusps of X_G.
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
  chosenmult := [ mult[c] : c in chosencusps];
  vprint User1: Sprintf("Galois orbits of cusps are: %o.", {* #ind[j] : j in [1..#ind] *});
  vprint User1: Sprintf("Using %o Fourier expansions (out of %o).", #chosencusps, #M`cusps);
  modforms0 := [ [ M`F0[i][c] : c in chosencusps] : i in [1..#M`F0]];

  // Step 2 - Rewrite modular coefficients as elements of smaller subfield

  vprint User1: "Rewriting Fourier expansions over smaller fields.";
  GL2Galois := sub<GL2 | [[1,0,0,pi(u)] : u in Generators(U)]>;
  z := Parent(Coefficient(modforms0[1][1],0)).1;
  R<x> := PolynomialRing(Rationals());
  fourierlist := <>;
  totalprec := 0;
  for c in [1..#chosencusps] do
      galoiscusp0 := GL2Galois meet Conjugate(G,M`cusps[chosencusps[c]]);
      // The subfield of Q(zeta_N) corresponding to galoiscusp is the field of definition of the Fourier coeffs.
      galoiscusp := Sort([g[2][2] : g in galoiscusp0]);
      //vprint User1: Sprintf("For cusp %o, Galois group is %o.", c, galoiscusp);
      KK, prim := fieldfind(sub<GL(1,Integers(N)) | [[g[2][2]] : g in Generators(galoiscusp0)]>,Parent(z));
      vprint User1: Sprintf("For cusp %o, Fourier coefficient field is %o.", c, R!DefiningPolynomial(KK));
      PP<qN> := LaurentSeriesRing(KK);
      Embed(KK,Parent(z),prim);
      totalprec := totalprec + maxprec*Degree(KK);
      curfour := <>;
      for i in [1..#modforms0] do
	  newfourier := &+[ KK!Coefficient(modforms0[i][c],l)*qN^l : l in [0..AbsolutePrecision(modforms0[i][c])-1]] + BigO(qN^AbsolutePrecision(modforms0[i][c]));
	  Append(~curfour,newfourier);
      end for;
      Append(~fourierlist,curfour);
  end for;
  modforms := << fourierlist[j][i] : j in [1..#chosencusps]> : i in [1..#modforms0]>;
  ReportEnd(label, "determining Galois action on cusps", postproctime);
  postproctime := Cputime(postproctime);

  // Build log-canonicalish ring

  polyring := PolynomialRing(Rationals(),#modforms,"grevlex");
  vars := [ polyring.i : i in [1..#modforms]];
  gens := [ Evaluate(M`psi[j],vars) : j in [1..#M`psi]];
  ttemp := ReportStart(label, "Grobner basis for ideal");
  I := ideal<polyring | gens>;
  G := GroebnerBasis(I);
  ReportEnd(label, "Grobner basis for ideal", ttemp);
  gbtime := Cputime(ttemp);
  LMs := [ LeadingMonomial(G[i]) : i in [1..#G]];
  initideal := ideal<polyring | LMs>;

  // canring is a list of pairs.
  // The first thing in a pair is list of lists of Fourier expansions
  // of the degree d generators of the canonical ring.
  // The second thing in a pair is list of degree d monomials representing the
  // elements.

  canring := <<modforms,vars>>;

  // Let's choose monomials that will *always* work!

  ttemp := ReportStart(label, "log-canonicalish ring");
  multcount := 0;
  doneper := -1;
  missing_monomials := MissingMonomials(initideal, maxd);
  total := &+[ #mons : mons in missing_monomials];
  for d in [2..maxd] do
      bas := missing_monomials[d];
      newfourier := <>;
      newvars := [];
      for curmon in bas do
	  // We have to be able to write curmon as a product of a degree (d-1)
	  // monomial not in initideal, and a degree 1 element.
	  // If we couldn't, then curmon would be in initideal
	  ind := Index([ IsDivisibleBy(curmon,canring[d-1][2][k]) : k in [1..#canring[d-1][2]]],true);
	  chk, q := IsDivisibleBy(curmon,canring[d-1][2][ind]);
	  ind2 := Index(vars,q);
	  multcount := multcount + 1;
	  if Floor(100*multcount/total) gt doneper then
	      doneper := Floor(100*multcount/total);
	      vprint User1: Sprintf("Doing multiplication %o of %o. %o\%% complete.", multcount, total, doneper);
	  end if;
	  newprd := < modforms[ind2][i]*canring[d-1][1][ind][i] : i in [1..#chosencusps]>;
	  Append(~newfourier,newprd);
	  Append(~newvars,curmon);
      end for;
      Append(~canring,<newfourier,newvars>);
  end for;
  ReportEnd(label, "log-canonicalish ring", ttemp);
  canringtime := Cputime(ttemp);

  ttemp := ReportStart(label, "linear algebra");
  FFFF<qN> := LaurentSeriesRing(Rationals());
  j := (1728*Eisenstein(4,qN : Precision := Ceiling((maxprec+2*N)/N))^3)/(Eisenstein(4,qN : Precision := Ceiling((maxprec+2*N)/N))^3 - Eisenstein(6,qN : Precision := Ceiling((maxprec+2*N)/N))^2);
  j := Evaluate(j,qN^N);

  func := j;
  done := false;
  
/*
curd := mind;
jmat := ZeroMatrix(Rationals(),0,totalprec);
for i in [1..#canring[curd][1]] do
  vecseq := [];
  for jj in [1..#chosencusps] do
    pp := (func*canring[curd][1][i][jj]);
    vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [curd*chosenmult[jj]-N..curd*chosenmult[jj]-N+maxprec-2]]);
  end for;
  jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
end for;

for i in [1..#canring[curd][1]] do
  vecseq := [];
  for jj in [1..#chosencusps] do
    pp := -canring[curd][1][i][jj];
    vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [curd*chosenmult[jj]-N..curd*chosenmult[jj]-N+maxprec-2]]);
  end for;
  jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
end for;
NN := NullSpace(jmat);
dimdim := Dimension(NN);
vprint User1: Sprintf("For d = %o, dimension of null space is %o.", curd, dimdim);
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
      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [curd*chosenmult[jj]-N..curd*chosenmult[jj]-N+maxprec-2]]);
    end for;
    jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;

  for i in [1..#canring[curd][1]] do
    vecseq := [];
    for jj in [1..#chosencusps] do
      pp := -canring[curd][1][i][jj];
      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [curd*chosenmult[jj]-N..curd*chosenmult[jj]-N+maxprec-2]]);
    end for;
    jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;
  NN := NullSpace(jmat);
  vprint User1: Sprintf("For d = %o, dimension of null space is %o.", curd, Dimension(NN));
end if;
*/

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
  vprint User1: Sprintf("For d = %o, dimension of null space is %o.", curd, dimdim);
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
      vprint User1: Sprintf("For d = %o, dimension of null space is %o.", curd, Dimension(NN));
  end if;

  // Now actually write down the map to the j-line

  ReportEnd(label, "linear algebra", ttemp);
  lintime := Cputime(ttemp);

  canringdim := #canring[curd][1];
  nullmat := Matrix(Basis(NN));
  changemat := nicefy(nullmat);
  v := (changemat*nullmat)[1];
  denom := &+[ (polyring!v[i])*canring[curd][2][i] : i in [1..canringdim]];
  num := &+[ (polyring!v[i+canringdim])*canring[curd][2][i] : i in [1..canringdim]];
  weakzero := [ &+[ v[i]*canring[curd][1][i][j] : i in [1..canringdim]]*func - &+[ v[i+canringdim]*canring[curd][1][i][j] : i in [1..canringdim]] : j in [1..#chosencusps]];
  assert &and [ IsWeaklyZero(weakzero[i]) : i in [1..#chosencusps]];

  C := Curve(ProjectiveSpace(Rationals(),#modforms-1),M`psi);
  jmap := map<C -> ProjectiveSpace(Rationals(),1) | [num,denom]>;

  vprint User1: Sprintf("Model time = %o.", modeltime);
  vprint User1: Sprintf("GB time = %o.", gbtime);
  vprint User1: Sprintf("Canonical ring time = %o.", canringtime);
  vprint User1: Sprintf("Linear algebra time = %o.", lintime);
  ReportEnd(label, "FindJMap", tttt);

  // canonical model is 0, other is -1
  model_type := (geomhyper) select -1 else 0;
  return C, num/denom, model_type, M`F0, M;
end function;
//end intrinsic;

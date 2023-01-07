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
    R := I^0;
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

intrinsic RelativeJMap(cover_label::MonStgElt, covered_label::MonStgElt, conjugator::SeqEnum, max_rel_index::RngIntElt) -> Crv, SeqEnum, SeqEnum, Rec
{}
    tt := ReportStart(cover_label, "RelativeJMap");
    N0, gens0 := GetLevelAndGensFromLabel(cover_label);
    N, gens := GetLevelAndGensFromLabel(covered_label);

    GLN := GL(2, Integers(N));
    GLN0 := GL(2, Integers(N0));
    G := sub<GLN | [GLN!v : v in gens]>;
    G0 := sub<GLN0 | [GLN0!v : v in gens0]>;
    // Have to invert the conjugator since we're transposing the gens
    conjugator := Transpose(GLN0!conjugator)^-1;
    G0 := G0^conjugator;
    assert ChangeRing(G0, Integers(N)) subset G;
    gens0 := [Eltseq(g) : g in Generators(G0)];

    M0 := CreateModularCurveRec(N0, gens0);
    g0 := M0`genus;
    assert g0 ge 3;
    t0 := ReportStart(cover_label, "CoverModel");
    M0, model_type0 := FindModelOfXG(M0, 1, cover_label);
    ReportEnd(cover_label, "CoverModel", t0);
    assert model_type0 eq 0;
    F0 := M0`F0;
    S0 := Universe(M0`psi);
    AssignCanonicalNames(~S0);
    C0 := Curve(Proj(S0), M0`psi);

    LMFDBWriteXGModel(C0, model_type0, cover_label);

    M := CreateModularCurveRec(N, gens);
    t := ReportStart(cover_label, "CoveredModel");
    M, model_type := FindModelOfXG(M, max_rel_index, covered_label);
    ReportEnd(cover_label, "CoveredModel", t);
    assert model_type eq 0;
    F := M`F0;
    g := M`genus;
    S := Universe(M`psi);
    AssignCanonicalNames(~S);
    C := Curve(Proj(S), M`psi);
    // Check that the curve is the same as the one already found
    D, _g, _model_type := LMFDBReadXGModel(covered_label);
    if D ne M`psi then
        print "error: relative-j model mismatch";
        if #D ne #M`psi then
            print "lengths different: ", #D, #M`psi;
        end if;
        for i in [1..Min(#D, #M`psi)] do
            if D[i] ne M`psi[i] then
                print i, D[i], "versus", M`psi[i];
            end if;
        end for;
    end if;

    t1 := ReportStart(cover_label, "ConvertModularFormExpansions");
    F1 := [ConvertModularFormExpansions(M0, M, [1,0,0,1], f) : f in F];
    // The entries in F1 are laurent series, but we need power series to fit with F
    R := Parent(F0[1][1]);
    F1 := [[R!qexp : qexp in f] : f in F1];
    // We need to express every entry in F1 in terms of F0
    rels := FindRelations(F1 cat F0, 1);
    mat := Matrix(Rationals(), #rels, g+g0, [[Coefficient(rels[i], j, 1) : j in [1..g + g0]] : i in [1..#rels]]);
    mat := EchelonForm(mat);
    ReportEnd(cover_label, "ConvertModularFormExpansions", t1);
    assert mat[g,g] eq 1;
    proj := [&+[mat[i,g + j] * S0.j : j in [1..g0]] : i in [1..g]];
    ReportEnd(cover_label, "RelativeJMap", tt);
    return C0, proj, F0, M0;
end intrinsic;

function LiftToTrivariate(R, f, d)
    Rlift := OriginalRing(Parent(f));
    f := Rlift!f;
    coeffs, mons := CoefficientsAndMonomials(f);
    exps := [Exponents(m) : m in mons];
    mons := [Monomial(R, e cat [d - &+e]) : e in exps];
    return Polynomial(coeffs, mons);
end function;

intrinsic AbsoluteJMap(label::MonStgElt, max_rel_index:RngIntElt) -> Crv, FldFunRatMElt, RngIntElt, SeqEnum, Rec
{Outputs a model X, j as a multivariate rational function in the ambient variables of X, the model type (5 if an elliptic curve, 8 if geometrically hyperelliptic, 0 if canonical model), F0 (a sequence of modular forms as computed by FindModelOfXG) and M (the ModularCurveRec)}
  N, gens := GetLevelAndGensFromLabel(label);
  tttt := ReportStart(label, "AbsoluteJMap");
//  gens := GetModularCurveGenerators(l);

//  N := StringToInteger(Split(l,".")[1],10);
//  gens := [ Transpose(g) : g in gens];
  gp := sub<GL(2,Integers(N))|gens>;

  M := CreateModularCurveRec(N,gens);
  M, model_type, mind, maxd, maxprec := FindModelOfXG(M, max_rel_index, label);
  if model_type eq 5 then
    LMFDBWriteXGModel(M`C, model_type, label);
    ReportEnd(label, "AbsoluteJMap", tttt);
    // Need to homogenize the map to the j-line
    num := Numerator(M`map_to_jline);
    den := Denominator(M`map_to_jline);
    d := Max(Degree(num), Degree(den));
    R := PolynomialRing(Rationals(), 3);
    num := LiftToTrivariate(R, num, d);
    den := LiftToTrivariate(R, den, d);
    return M`C, [num, den], model_type, M`f cat [[1 : i in [1..#M`cusps]]], M;
  end if;
  C := Curve(ProjectiveSpace(Rationals(), #M`F0 - 1), M`psi);

  LMFDBWriteXGModel(C, model_type, label);
  modeltime := Cputime(tttt);

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
  chosenmult := [ M`mult[c] : c in chosencusps];
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

  jmap := map<C -> ProjectiveSpace(Rationals(),1) | [num,denom]>;

  vprint User1: Sprintf("Model time = %o.", modeltime);
  vprint User1: Sprintf("GB time = %o.", gbtime);
  vprint User1: Sprintf("Canonical ring time = %o.", canringtime);
  vprint User1: Sprintf("Linear algebra time = %o.", lintime);
  ReportEnd(label, "AbsoluteJMap", tttt);

  return C, [num, denom], model_type, M`F0, M;
end intrinsic;

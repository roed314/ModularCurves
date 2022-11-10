import "OpenImage/main/ModularCurves.m" : FindCuspPair, CreateModularCurveRec;
import "OpenImage/main/GL2GroupTheory.m" : LiftMatrix;
import "findjmap.m" : fieldfind;

declare type CspDat;

declare attributes CspDat: cusp, field, ind, coords;

intrinsic CuspData(cusp::SetCspElt, field::Fld, ind::RngIntElt) -> CspDat
{.}
    c := New(CspDat);
    c`cusp := cusp;
    c`field := field;
    c`ind := ind;
    return c;
end intrinsic;

intrinsic CuspData(cusp::SetCspElt, field::Fld,
		   ind::RngIntElt, coords::Pt) -> CspDat
{.}
    c := New(CspDat);
    c`cusp := cusp;
    c`field := field;
    c`ind := ind;
    c`coords := coords;
    return c;
end intrinsic;

intrinsic Print(c::CspDat, level::MonStgElt)
{.}
    if level eq "Magma" then
	if assigned c`coords then
	    printf "CuspData(%m,%m,%m,%m)", c`cusp, c`field, c`ind, c`coords;
	else
	    printf "CuspData(%m,%m,%m)", c`cusp, c`field, c`ind;
	end if;
	return;
    end if;
    printf "Cusp %o defined over %o", c`cusp, c`field;
    if assigned c`coords then
	printf " with coordinates %o", c`coords;
    end if;
    return;
end intrinsic;

intrinsic CuspOrbits(N::RngIntElt, gens::SeqEnum) -> SeqEnum[SeqEnum[CspDat]]
{.}
    if N eq 1 then
       return [[CuspData(Cusp(1,0), Rationals(), 1)]];
    end if;
    // Step 1 - Determine Galois orbits of cusps and choose one representative from each

  // Computes the action of (Z/NZ)^* on the cusps of X_G.  This corresponds to the action of Gal(Q(zeta_N)/Q) on the cusps.
  printf "Determining Galois action on cusps.\n";
  M := CreateModularCurveRec(N, gens);
  gp := sub<GL(2,Integers(N))|gens>;
  G := gp;
  G0 := gp;
  GL2 := GL(2,Integers(N));
  SL2 := SL(2,Integers(N));    
  U,pi:=UnitGroup(Integers(N));
  s:={};
  stabs := [{Integers(N) | } : c in M`cusps];
  for u in Generators(U) do
      d:=Integers(N)!pi(u);
      b:=GL2![1,0,0,d];
      flag:=exists(g){g: g in G | Determinant(g) eq d};
      error if not flag, "Group G should have full determinant.";
      sigma:=[FindCuspPair(M,SL2!(g^(-1)*GL2!M`cusps[i]*b))[1]: i in [1..#M`cusps]];
      s:=s join {sigma};
      for i in [1..#M`cusps] do
	  if sigma[i] eq i then
	      Include(~stabs[i], d);
	  end if;
      end for;
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

  M_lifts := [[LiftMatrix(M`cusps[i], 1) : i in orb] : orb in ind];
  acs := [[[m_lift[1,1], m_lift[2,1] mod (N*m_lift[1,1]) ] : m_lift in orb]
	  : orb in M_lifts];
  cusps := [[Cusp((ac[2] eq 0) select ac[1] else ac[1] mod (N*ac[2]), ac[2])
	     : ac in orb] : orb in acs];
  stabs := [stabs[orb[1]] : orb in ind];
  K := CyclotomicField(N);
  fields := [* *];
  R<x> := PolynomialRing(Rationals());
  for i in [1..#stabs] do
      KK, prim := fieldfind(sub<GL(1, Integers(N)) | [[d] : d in stabs[i]]>,K);
      printf "For cusp %o, field of definition is %o.\n",cusps[i][1],
	     R!DefiningPolynomial(KK);
      Embed(KK,K,prim);
      if Degree(KK) gt 1 then
	  AssignNames(~KK, [Sprintf("a_%o", i)]);
      end if;
      Append(~fields, KK);
  end for;
  cusps := [[CuspData(cusps[i][j], fields[i], ind[i][j]) :
	     j in [1..#cusps[i]] ] : i in [1..#cusps]];
  printf "Galois orbits of cusps are: %o.\n",{* #ind[j] : j in [1..#ind]*};
  // printf "Orbits are: %o", cusps;

  return cusps;
end intrinsic;

intrinsic CuspUpdateCoordinates(~cusp::CspDat, X::Crv,
			  F::SeqEnum[SeqEnum[RngSerPowElt]])
{.}
   cuspInd := cusp`ind;
   K := cusp`field;
   v := Minimum([Valuation(f[cuspInd]) : f in F]);
   pt := [Coefficient(f[cuspInd], v) : f in F];
   pt_X := ChangeRing(X, Universe(pt))!pt;
   pt_X := ChangeRing(X, K)!Eltseq(pt_X);
   cusp`coords := pt_X;
   return;
end intrinsic;

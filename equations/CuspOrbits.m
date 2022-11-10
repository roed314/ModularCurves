import "OpenImage/main/ModularCurves.m" : FindCuspPair, CreateModularCurveRec;
import "OpenImage/main/GL2GroupTheory.m" : LiftMatrix;

intrinsic CuspOrbits(N::RngIntElt, gens::SeqEnum) -> SetEnum[SetEnum[SetCspElt]]
{.}
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

  M_lifts := [[LiftMatrix(M`cusps[i], 1) : i in orb] : orb in ind];
  cusps := {{Cusp(m_lift[1,1], m_lift[2,1]) : m_lift in orb} : orb in M_lifts};
  
  printf "Galois orbits of cusps are: %o.\n",{* #ind[j] : j in [1..#ind]*};
  // printf "Orbits are: %o", cusps;

  return cusps;
end intrinsic;

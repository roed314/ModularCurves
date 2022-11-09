// running in equations
AttachSpec("equations.spec");
AttachSpec("~/github/CHIMP/CHIMP.spec");
AttachSpec("~/github/Gm-Reduce/spec");
SetVerbose("GmReduce",true);
load "OpenImage/main/GL2GroupTheory.m";
load "OpenImage/main/ModularCurves.m";
import "Zywina/findjinvmap.m": GetPrecisionAndDegrees, FindJMapInv;

QQ := Rationals();
gens := GetModularCurveGenerators("42.48.4.5");
N := Characteristic(BaseRing(Parent(gens[1])));
rec := CreateModularCurveRec(N,gens);
//bool, polys, fs := FindCanonicalModel(rec,20);
//rec := FindModelOfXG(rec, 40);
rec := FindModelOfXG(rec, 150);
/*
  S := Parent(polys[1]);
  S := ChangeRing(S,QQ);
*/
S := Parent(rec`psi[1]);
C := Curve(Proj(S),rec`psi);
print C;
//Ps := PointSearch(C,20);
K := RationalsAsNumberField();
C := ChangeRing(C,K);
//Ps := [C!Eltseq(el) : el in Ps];
//Ps := [Place(el) : el in Ps];
KC<x,y,z> := FunctionField(AffinePatch(C,1));
//time small3 := SmallFunctions(Ps,3);
/*
  E4, E6, j := JMap(rec);
  jC := RationalFunctionToFunctionFieldElement(C,j);
  Degree(jC);
  pts, mults := Support(Divisor(Differential(jC)));
  [* jC(RepresentativePoint(el)) : el in pts *];
*/
//BestModel(jC);

maxprec, mind, maxd := GetPrecisionAndDegrees(rec);
j, num, den := FindJMapInv(rec, maxprec, mind, maxd);

// now make plane model with j as a coordinate
//jC := Evaluate(num, [KC.1,KC.2,1,KC.3])/Evaluate(den, [KC.1,KC.2,1,KC.3]);
jC := RationalFunctionToFunctionFieldElement(C,num/den);
JMapSanityCheck(jC);
ChangeDirectory("~/github/Gm-Reduce");
BestModel(jC);

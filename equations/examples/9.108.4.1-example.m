// running in equations
AttachSpec("equations.spec");
AttachSpec("~/github/CHIMP/CHIMP.spec");
AttachSpec("~/github/Gm-Reduce/spec");
SetVerbose("GmReduce",true);
load "OpenImage/main/GL2GroupTheory.m";
load "OpenImage/main/ModularCurves.m";
import "Zywina/findjinvmap.m": GetPrecisionAndDegrees, FindJMapInv;

QQ := Rationals();
gens := GetModularCurveGenerators("9.108.4.1");
N := Characteristic(BaseRing(Parent(gens[1])));
rec := CreateModularCurveRec(N,gens);
//bool, polys, fs := FindCanonicalModel(rec:prec0:=20);
rec := FindModelOfXG(rec);
/*
  S := Parent(polys[1]);
  S := ChangeRing(S,QQ);
*/
S := Parent(rec`psi[1]);
C := Curve(Proj(S),rec`psi);
print C;
Ps := PointSearch(C,20);
K := RationalsAsNumberField();
C := ChangeRing(C,K);
Ps := [C!Eltseq(el) : el in Ps];
Ps := [Place(el) : el in Ps];
KC<x,y,z> := FunctionField(AffinePatch(C,1));
//time small3 := SmallFunctions(Ps,3);
E4, E6, j := JMap(rec);
jC := RationalFunctionToFunctionFieldElement(C,j);
BestModel(jC);

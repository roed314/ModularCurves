// running in equations
AttachSpec("equations.spec");
AttachSpec("~/github/CHIMP/CHIMP.spec");
AttachSpec("~/github/Gm-Reduce/spec");
SetVerbose("GmReduce",true);
load "OpenImage/main/GL2GroupTheory.m";
load "OpenImage/main/ModularCurves.m";
import "Zywina/findjinvmap.m": GetDegrees, GetPrecision, FindJMapInv;

t0 := Cputime();
QQ := Rationals();
gens := GetModularCurveGenerators("42.48.4.5");
N := Characteristic(BaseRing(Parent(gens[1])));
print "Creating modular curve record";
rec := CreateModularCurveRec(N,gens);
//bool, polys, fs := FindCanonicalModel(rec:prec0:=20);
//print "Computing model of X_H";
rec := FindModelOfXG(rec);
//S := Parent(rec`psi[1]);
//C := Curve(Proj(S),rec`psi);
//printf "initial model: %o", C;
//Ps := PointSearch(C,20);
//K := RationalsAsNumberField();
//C := ChangeRing(C,K);
//Ps := [C!Eltseq(el) : el in Ps];
//Ps := [Place(el) : el in Ps];
//KC<x,y,z> := FunctionField(C);
//time small3 := SmallFunctions(Ps,3);
/*
  E4, E6, j := JMap(rec);
  jC := RationalFunctionToFunctionFieldElement(C,j);
  Degree(jC);
  pts, mults := Support(Divisor(Differential(jC)));
*/

print "Computing j-map";
mind, maxd := GetDegrees(rec, false); // not hyperelliptic
maxprec := GetPrecision(rec, maxd, false); // not hyperelliptic
rec, j, num, den := FindJMapInv(rec, maxprec, mind, maxd);
S := Parent(rec`psi[1]);
C := Curve(Proj(S),rec`psi);


K := RationalsAsNumberField();
C := ChangeRing(C,K);
KC<x,y,z> := FunctionField(C);

// now make plane model with j as a coordinate
//jC := Evaluate(num, [KC.1,KC.2,1,KC.3])/Evaluate(den, [KC.1,KC.2,1,KC.3]);
jC := RationalFunctionToFunctionFieldElement(C,num/den);
JMapSanityCheck(jC);
print "Computing plane model";
ChangeDirectory("~/github/Gm-Reduce");
f := BestModel(jC);
printf "found plane model %o\n", f;
t1 := Cputime();
printf "that took %o seconds\n", t1-t0;
C_plane := Curve(Spec(Parent(f)), f);

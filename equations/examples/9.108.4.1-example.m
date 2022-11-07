// running in equations/Zywina
AttachSpec("ModCrv.spec");
AttachSpec("~/github/CHIMP/CHIMP.spec");
AttachSpec("~/github/Gm-Reduce/spec");
SetVerbose("GmReduce",true);
load "../LMFDB_interface.m";

QQ := Rationals();
ChangeDirectory("~/github/ModularCurves/equations");
gens := GetModularCurveGenerators("9.108.4.1");
ChangeDirectory("Zywina");
N := Characteristic(BaseRing(Parent(gens[1])));
rec := CreateModularCurveRec(N,gens);
//bool, polys, fs := FindCanonicalModel(rec,20);
rec := FindModelOfXG(rec, 20);
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
KC<x,y,z> := FunctionField(C);
time small3 := SmallFunctions(Ps,3);


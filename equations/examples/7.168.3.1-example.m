QQ := Rationals();
gens := GetModularCurveGenerators("7.168.3.1");
N := Characteristic(BaseRing(Parent(gens[1])));
rec := CreateModularCurveRec(N,gens);
bool, polys, fs := FindCanonicalModel(rec:prec0:=20);
S := Parent(polys[1]);
S := ChangeRing(S,QQ);
C := Curve(Proj(S),polys);

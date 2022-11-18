AttachSpec("equations.spec");
AttachSpec("~/github/CHIMP/CHIMP.spec");
load "OpenImage/main/GL2GroupTheory.m";
load "OpenImage/main/ModularCurves.m";
import "Zywina/findjinvmap.m": GetDegrees, GetPrecision, FindJMapInv;

QQ := Rationals();
prec := 150;
gens := GetModularCurveGenerators("30.60.5.1");
N := Characteristic(BaseRing(Parent(gens[1])));
print "Creating modular curve record";
rec := CreateModularCurveRec(N,gens);
//bool, polys, fs := FindCanonicalModel(rec,200);
//PlaneModelFromQExpansions(rec,prec);
rec := FindModularForms(2,rec,prec);
rec := FindCuspForms(rec);
fs := rec`F0;

found_bool := false;
m := 3;
while not found_bool do
  printf "trying m = %o\n", m;
  rels := FindRelations(fs[1..3],m);
  if #rels gt 0 then
    print "relation found!";
    found_bool := true;
  end if;
  m +:= 1;
end while;

f := rels[1];
C := Curve(Proj(Parent(f)), f);
Genus(C);

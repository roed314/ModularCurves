
AttachSpec("spec");
SetVerbose("ModAbVarRec",3);
input := Split(Read("labelwithhecke_missing.txt"), "\n");

import "reconstructiongenus2.m" : AlgebraizedInvariantsG2, ReconstructCurveG2, IgusaInvariantsG2;

load "TracePolarization.m";
m := 106; //try m := 94
line := Split(input[m], ":");


//function doline(line)


	label := line[1];
	level := eval(line[2]);
	hc := eval(line[3]);
	f := MakeNewformModSym(level, hc);
	P := PeriodMatrix(f : prec := 140);
	print "finished constructing period matrix!";
	QQ := RationalsExtra(Precision(BaseRing(P)));
	GeoEndoRep := GeometricEndomorphismRepresentation(P, QQ);
  	F, h := InclusionOfBaseExtra(BaseRing(GeoEndoRep[1][1]));
  	GeoEndoRepBase := EndomorphismRepresentation(GeoEndoRep, F, h);

	one := GeoEndoRepBase[1][2];
  	gen := GeoEndoRepBase[2][2];
  	minpoly := MinimalPolynomial(gen); //need to make (D + sqrt(D)) where D is the discriminant
    Piprime,M,map := FindZFStructure(P, GeoEndoRepBase);
    Pi, E, pol := TracePrincipalPolarization(Piprime,M);
    C, hL, b, e := ReconstructCurveG2(Pi, QQ);
    print C;


//end function;
//AttachSpec("~/projects/CHIMP/CHIMP.spec");
//AttachSpec("~/projects/ModularCurves/abelian-varieties/spec");

AttachSpec("spec");

SetVerbose("ModAbVarRec",2);
//input := "441.2.a.h:441:[<2,[-7,0,1]>,<5,[0,1]>,<13,[0,1]>]";
input := "23.2.a.a:23:[]:1";
s := Split(input, ":");
label := s[1];
level := StringToInteger(s[2]);
hc := eval s[3];
prec := 100;

// figure out the right number of qexp coeffs
ncoeffs := Ceiling(20*Sqrt(level)*Log(10)*prec/(2*Pi(ComplexField())));

time f := MakeNewformModSym(level, hc);

time P := PeriodMatrix(f : prec:=prec, ncoeffs:=ncoeffs);

time P2, G2 := PeriodMatrixWithMaximalOrder(P);
G2[2][2];

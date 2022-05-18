AttachSpec("~/projects/CHIMP/CHIMP.spec");
AttachSpec("~/projects/ModularCurves/abelian-varieties/spec");
SetVerbose("ModAbVarRec", 2);
SetVerbose("ModularSymbols", 2);
s := Split(input, ":");
label := s[1];
level := StringToInteger(s[2]);
hc := eval s[3];
prec := StringToInteger(prec);
ncoeffs := Ceiling(20*Sqrt(level)*Log(10)*prec/(2*Pi(ComplexField())));
time f := MakeNewformModSym(level, hc);
try
  b, out := ReconstructGenus2Curve(f : prec:=prec, ncoeffs:=ncoeffs);
  if not b then
    error "failed to find *any* curves!!";
  end if;
catch e
  WriteStderr(e);
  exit 1;
end try;
StripWhiteSpace(Sprintf("%o:%o", label, MachinePrint(out)));
exit;

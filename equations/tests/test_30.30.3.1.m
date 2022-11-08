AttachSpec("equations.spec");
C, fs, j, N := LMFDBReadModel("output_data/30.30.3.1");
P1 := ProjectiveSpace(PolynomialRing(Rationals(),2));
j := Evaluate(j`J, GeneratorsSequence(CoordinateRing(C)));
jmap := map<C->P1|[Numerator(j), Denominator(j)]>;
cm_m4_pt := P1![1728,1];
// This curve has two CM points with CM discriminant 1728
assert #Points(cm_m4_pt@@jmap) eq 1;
exit;

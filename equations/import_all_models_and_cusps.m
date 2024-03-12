Labels := {};
Curves := AssociativeArray();
Points := AssociativeArray();
F := Open("outputfile.txt", "r");
s := Gets(F);
R := PolynomialRing(Rationals());

i := 0;
while not(IsEof(s)) do
	i +:= 1;
	if i mod 1000 eq 0 then
		print i;
	end if;
	T := eval s;
	if s[1] eq "<" then
		if not(T[1] in Labels) then
			Include(~Labels, T[1]);
			Points[T[1]] := AssociativeArray();
			Curves[T[1]] := AssociativeArray();
		end if;
		Points[T[1]][T[2]] := [* *];
		Curves[T[1]][T[2]] := <T[3], T[4]>;
		i1 := T[1];
		i2 := T[2];
	else
		for PtOrbit in T do
			Append(~Points[i1][i2], PtOrbit);
		end for;
	end if;
	s := Gets(F);
end while;

vars := "xyzwtuvrsabcdefghiklmnopqj";
function ParsePolynomial(s, n)
	for i in [1..n] do
		s := ReplaceCharacter(s, vars[i], "x[" cat Sprint(i) cat "]");
	end for;
	return s;
end function;

function CurvesAndPoints(label, i)
	C := Curves[label][i];
	Pts := Points[label][i];
	n := C[1];	// Number of variables
	T<[x]> := PolynomialRing(Rationals(), n);
	AssignNames(~T, [vars[i] : i in [1..n]]);
	f := [eval ParsePolynomial(g, n) : g in C[2]];
	if i eq 4 then
		A := WeightedProjectiveSpace(T, [4,6]);
	else
		A := ProjectiveSpace(T);
	end if;
	C := Curve(A, f);
	CPts := [* *];
	for PtOrbit in Pts do
		K := NumberField(R!PtOrbit[1]);
		for Pt in PtOrbit[2] do
			coord := [K!c : c in Pt];
			Append(~CPts, BaseChange(C, K)!coord);
		end for;
	end for;
	return C, CPts;
end function;

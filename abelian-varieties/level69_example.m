//AttachSpec("~/projects/CHIMP/CHIMP.spec")
function GetPeriodMatrices(N : prec := 80, ncoeffs := 10000)
    SetDefaultRealFieldPrecision(prec + 10);
    C:=ComplexFieldExtra(prec);
    Q:=RationalsExtra(prec);
    Pis := [* *];
    for A in Decomposition(JZero(N)) do
        if Dimension(A) ne 2 then continue; end if;
        print A;
        Pi := Matrix(Periods(A, ncoeffs)); // no control over precision really, instead use Eran's code
        print "Periods computed";
        // Change convention
        Pi := Transpose(ChangeRing(Pi, C));
        g := #Rows(Pi);
        P1 := Submatrix(Pi,1,1,g,g);
        P2 := Submatrix(Pi,1,g+1,g,g);
        Pi = HorizontalJoin(P2,P1);
        Append(~Pis, <Newform(A), Pi>);
    end for;
    return Pis;
end function;
foo := GetPeriodMatrices(69);
Pi := foo[1][2]; // this the Pi of the newform
GeoRep := GeometricEndomorphismRepresentation(Pi, Rationals());
sqrt5 := GeoRep[2][2];
one := GeoRep[1][2];
CC := BaseRing(Pi);
SupPi := Transpose(Matrix(Rows(Transpose(2*Pi)) cat Rows(Transpose(PiWeCare*Matrix(CC, one + sqrt5)))));
kernel, bool := IntegralRightKernel(SupPi);
assert bool;
S, P, Q := SmithForm(Matrix(Integers(), kernel));
E := Transpose(Submatrix(P^-1, 1,1, 4, 8));
Pi2 := SupPi*Matrix(CC, E);
GeoRep2 := GeometricEndomorphismRepresentation(Pi2, Rationals());
_, pol := SomePrincipalPolarization(Pi2);
E, F := FrobeniusFormAlternating(Matrix(Integers(), pol));
H := ReconstructCurve(Pi2*Transpose(Matrix(CC, F)), Rationals());
// This is Noam's curve
G2Invariants(H);

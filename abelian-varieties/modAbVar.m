function GetCurve(N : prec := 80, ncoeffs := 10000)
    SetDefaultRealFieldPrecision(prec + 10);
    C:=ComplexFieldExtra(prec);
    Q:=RationalsExtra(prec);
    Hs := [];
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
        _, pol := SomePrincipalPolarization(Pi); pol;
        print "Principal polarization found";
        E, F := FrobeniusFormAlternating(Matrix(Integers(), pol)); E,F;
        H := ReconstructCurve(Pi*Transpose(ChangeRing(F, C)), Q);
        // TODO can we twist it, yes we can
        print "Curve found";
        print H;
        Append(~Hs, <Newform(A), H>);
    end for;
    return Hs;
end function;


function BigCRT(moduli)
    oldmod := 1;
    oldvals := [0];
    for E in moduli do
        m, sols := Explode(E);
        print m;
        newvals := [];
        for sol in sols do
            for ov in oldvals do
                Append(~newvals,CRT([ov, sol], [oldmod, m]));
            end for;
        end for;
        oldmod *:= m;
        oldvals := newvals;
    end for;
    return [oldval - oldmod * (oldval div (oldmod div 2)) : oldval in oldvals];
end function;


function IsCorrectTwist(C, f)
    M := ModularAbelianVariety(f);
    D := Discriminant(C);
    N := Level(f);
    for p in PrimesUpTo(1000) do
        if (Numerator(D) mod p eq 0) or (N mod p eq 0) then 
            print "skipping";
            print p;
            continue;
        end if;
        if EulerFactor(C,p) ne Reverse(FrobeniusPolynomial(M, p)) then
            print p;
            print EulerFactor(C,p);
            print Reverse(FrobeniusPolynomial(M, p));
            return false;
        end if;
    end for;
    return true;
end function;

// given two lists of primes find integers that are squares mod the first and non-squares mod the second

function SquaresMod(mods, nonmods)
    inp := [];
    for m in mods do
       Append(~inp, <m, [i : i in [0.. m-1] | KroneckerSymbol(i, m) eq 1 ]>);
    end for;
    for m in nonmods do
       Append(~inp, <m, [i : i in [0.. m-1] | KroneckerSymbol(i, m) eq -1 ]>);
    end for;
    return BigCRT(inp);
end function;
function SmallestSquareMod(mods,nonmods)
    L := SquaresMod(mods, nonmods);
    L2 := [<Abs(l), l> : l in L];
    print L2;
    return Sort(L2)[1][2];
end function;


function FindCorrectTwist(C, f)
    M := ModularAbelianVariety(f);
    D := Discriminant(C);
    N := Level(f);
    sqps := [];
    nsqps := [];
    for p in PrimesUpTo(12) do
        if (Numerator(D) mod p eq 0) or (N mod p eq 0) then 
            print "skipping";
            print p;
            continue;
        end if;
        if EulerFactor(C,p) ne Reverse(FrobeniusPolynomial(M, p)) then
            Append(~nsqps, p);
        else
            Append(~sqps, p);
        end if;
    end for;
    return SmallestSquareMod(sqps, nsqps);
end function;

// Run after GetModelLMFDB.m
// Usage: magma -b label:={1} GetJFactorization.m >> stdout/{1} 2>&1

AttachSpec("equations.spec");
SetColumns(0);
if assigned verbose or assigned debug then
    SetVerbose("User1", 1);
end if;
if assigned debug then
    SetDebugOnError(true);
end if;
if (not assigned label) then
    printf "This script assumes that label, the label of the X_H to compute, is given as a command line paramter.\n";
    printf "Something like magma label:=7.168.3.a.1 GetJFactorization.m\n";
    quit;
end if;

function parenwrap(f)
    f := sprint(f);
    if "+" in f or "-" in f then
        f := "(" * f * ")";
    end if;
    return f;
end function;

function show_exp(fe)
    f, e := Explode(fe);
    f := parenwrap(f);
    if e eq 1 then
        return f;
    end if;
    return f * "^" * sprint(e);
end function;

function getfac(j)
    ZZ := Integers();
    leading := [];
    facs := [];
    nfacs := [];
    R := Universe(j);
    jdegs := {Degree(coord) : coord in j};
    for coord in j do
        fac, u := Factorization(coord);
        nfac := [fe[2] : fe in fac | fe[1] ne R.(Rank(R))]; // skip homogenizing terms
        if #nfac eq 0 then
            nfac := 0;
        else
            nfac := &+nfac;
        end if;
        Append(~nfacs, Sprint(nfac));
        rescaled := [];
        for fe in fac do
            f, e := Explode(fe);
            f, d := ClearDenominators(f);
            u /:= d^e;
            Append(~rescaled, <f, e>);
        end for;
        Append(~leading, u);
        if #rescaled eq 1 and fac[1][2] eq 1 then
            // irreducible
            s := sprint(rescaled[1][1]);
        else
            s := Join([show_exp(fe) : fe in rescaled], "*");
        end if;
        Append(~facs, s);
    end for;
    facs := "{" * Join(facs, ",") * "}";
    nfacs := "{" * Join(nfacs, ",") * "}";

    d := LCM([Denominator(u) : u in leading]);
    if leading[#leading] lt 0 then
        d := -d;
    end if;
    leading := [ZZ!(u * d) : u in leading];
    d := GCD(leading);
    leading := [u div d : u in leading];
    if &and[u eq 1 : u in leading] then
        leading := "\\N";
    else
        // Factor leading coefficients
        leadfac := [];
        for u in leading do
            if u in [1, -1] then
                Append(~leadfac, Sprint(u));
            else
                fac, sgn := Factorization(u);
                sgn := (sgn eq 1) select "" else "-";
                Append(~leadfac, sgn * Join([show_exp(pe) : pe in fac], "*"));
            end if;
        end for;
        leading := "{" * Join([Sprint(u) : u in leadfac], ",") * "}";
    end if;
    jdegs := Join([Sprint(d) : d in jdegs], ","); // Should be length 1

    return facs, leading, nfacs, jdegs;
end function;

X, model_type, codomain, j := LMFDBReadJMap(label);
if codomain eq "" then
    fname := "jfacs/" * label;
    assert #j eq 2;
    facs, leading, nfacs, jdegs := getfac(j);
    Write(fname, Sprintf("1|%o|%o|%o|%o", facs, leading, nfacs, jdegs) : Overwrite);
    facs, leading, nfacs, jdegs := getfac([j[1] - 1728*j[2], j[2]]);
    Write(fname, Sprintf("3|%o|%o|%o|%o", facs, leading, nfacs, jdegs));
end if;
exit;

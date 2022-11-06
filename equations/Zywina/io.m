declare type JMapData;
declare attributes JMapData: E4,E6,J;

function strip(X)
    // Strips spaces and carraige returns from string; much faster than StripWhiteSpace.
    return Join(Split(Join(Split(X," "),""),"\n"),"");
end function;

function sprint(X)
    // Sprints object X with spaces and carraige returns stripped.
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return strip(Sprintf("%o",X));
end function;

intrinsic LMFDBWriteModel(X::Rec, j::JMapData, fname::MonStgElt)
{Write the model, the q-expansions, and j-map to a file for input into the LMFDB database}
    Kq<q> := Parent(X`F0[1][1]);
    K := BaseRing(Kq);
    if Type(K) ne FldRat then
        AssignNames(~K, ["zeta"]);
	cyc_ord := CyclotomicOrder(K);
    else
	cyc_ord := 1;
    end if;
    // Need to figure out what to do about q-expansions
    uvars := Eltseq("XYZWTUVRSABCDEFGHIJKLMNOPQ");
    lvars := Eltseq("xyzwtuvrsabcdefghijklmnopq");
    DP := X`psi;
    R := Parent(DP[1]);
    if (#uvars lt Rank(R)) then
	uvars := [Sprintf("X_{%o}", i) : i in [1..Rank(R)]];
	lvars := [Sprintf("x_{%o}", i) : i in [1..Rank(R)]];
    end if;
    AssignNames(~R, uvars[1..Rank(R)]);
    S := Parent(j`J);
    AssignNames(~S, lvars[1..Rank(R)]);
    E4_str := (assigned j`E4) select sprint(j`E4) else "";
    E6_str := (assigned j`E6) select sprint(j`E6) else "";
    Write(fname, Sprintf("{%o}|{%o}|{%o,%o}|{%o}", Join([sprint(f) : f in DP], ","), Join([Join([sprint(f) : f in fs],",") : fs in X`F0], ","), E4_str, E6_str, sprint(j`J), cyc_ord));
    return;
end intrinsic;




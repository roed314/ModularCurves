import "Zywina/findjinvmap.m" : FindJMapInv, GetPrecision, GetDegrees;
import "Zywina/ModularCurves.m" : CreateModularCurveRec, FindCanonicalModel;
import "Code to compute models for genus 0 groups.m" : ComputeModel;

intrinsic ProcessModel(label::MonStgElt) -> Rec, RngMPolElt, RngMPolElt
{.}
    level := StringToInteger(Split(label, ".")[1]);
    genus := StringToInteger(Split(label, ".")[3]);
    input := Read("input_data/" * label);
    input_lines := Split(input, "\n");
    if IsEmpty(input_lines) then
	gens := [];
    else
	gens := [StringToInteger(x) : x in Split(input_lines[1], ",")];
    end if;
    // Should be a list of 2x2 matrices, so number of elements divisible by 4.
    assert #gens mod 4 eq 0;
    // Here we transpose the matrices, because Zywina's code uses the 
    // transposed convention of Galois action
    gens := [[gens[4*i-3],gens[4*i-1],gens[4*i-2],gens[4*i]] 
	     : i in [1..#gens div 4]];
    // Apparently, Rakvi's code does not handle X(1)
    if (genus eq 0) and (not IsEmpty(gens)) then
	// !! TODO - is this precision always enough?
	Ggens := {GL(2,Integers(level))!g : g in gens};
	X, j := ComputeModel(level,Ggens,10);
	return X, Numerator(j), Denominator(j);
    end if;
    M := CreateModularCurveRec(level, gens);
    if IsEmpty(gens) then
	P1<s,t> := ProjectiveSpace(Rationals(),1);
	_<q> := PowerSeriesRing(Rationals());
	M`F0 := [[jInvariant(q)]];
	M`psi := [CoordinateRing(P1) |];
	return M, s, t;
    end if;
    is_hyp := M`genus le 2;
    printf "Starting model computation.\n";
    ttemp := Cputime();
    F := [];
    psi := [];
    if (not is_hyp) then
	mind, maxd := GetDegrees(M, is_hyp);
	prec := GetPrecision(M, maxd, is_hyp);
	flag, psi, F := FindCanonicalModel(M, prec);
	is_hyp := not flag;
    end if;
    mind, maxd := GetDegrees(M, is_hyp);
    prec := GetPrecision(M, maxd, is_hyp);
    if is_hyp then   
	F, psi := CanonicalRing(M : Precision := 11+prec);
	M`F0 := F;
	M`psi := psi;
    else
	M`k := 2;
	M`F0 := F;
	M`psi := psi;
    end if;
    modeltime := Cputime(ttemp);
    printf "Done. Time taken was %o.\n",modeltime;
    printf "Model time = %o.\n",modeltime;    
    X, jmap, num, denom := FindJMapInv(M, prec, mind, maxd);
    printf "Skipping E4, E6 computation.\n";
    // eis_time := Cputime();
    // j`E4, j`E6, _ := JMap(M);
    // printf "E4,E6 time taken was %o. \n", eis_time;    
    return X, num, denom;
end intrinsic;

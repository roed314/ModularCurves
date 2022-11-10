import "findjmap.m" : FindJMap;
import "OpenImage/main/ModularCurves.m" : CreateModularCurveRec;
import "Code to compute models for genus 0 groups.m" : ComputeModel;

intrinsic ProcessModel(label::MonStgElt) -> Crv, FldFunRatMElt[FldRat],
                                            RngIntElt, SeqEnum[CspDat]
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
	X, j, has_rational_pt := ComputeModel(level,Ggens,10);
	model_type := (has_rational_pt) select 1 else 2;
	cusps := CuspOrbits(level, gens);
	return X, j, model_type, cusps;
    end if;
    // handling X(1)
    if IsEmpty(gens) then
	M := CreateModularCurveRec(level, gens);
	P1 := ProjectiveSpace(Rationals(),1);
	_<q> := PowerSeriesRing(Rationals());
	M`F0 := [[jInvariant(q)]];
	M`psi := [CoordinateRing(P1) |];
	cusps := CuspOrbits(level, gens)[1];
	cusps[1]`coords := P1![1,0];
	// 1 is for P1 model
	return P1, FunctionField(P1).1, 1, cusps;
    end if;
     // Replacing this by Jeremy's new function
    X, j, model_type, F := FindJMap(level, gens);
    cusps := CuspOrbits(level, gens);
    // We only need one representative of each orbit
    cusps := [orb[1] : orb in cusps];
    for i in [1..#cusps] do
	CuspUpdateCoordinates(~cusps[i], X, F);
    end for;
    return X, j, model_type, cusps;
end intrinsic;

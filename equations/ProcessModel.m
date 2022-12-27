import "Code to compute models for genus 0 groups.m" : ComputeModel;

intrinsic GetLevelAndGensFromLabel(label::MonStgElt) ->
	  RngIntElt, SeqEnum[SeqEnum[RngIntElt]]
{.}
    level := StringToInteger(Split(label, ".")[1]);
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
    return level, gens;
end intrinsic;

intrinsic FindModelOfXG(M::Rec, label::MonStgElt) -> Rec, RngIntElt, RngIntElt, RngIntElt
{Version of FindModelOfXG that automatically chooses precision and sets the random seed to try to make the model more consistent.  Returns the ModularCurveRec, the model type, mind and maxd (see below)}
    ttemp := ReportStart(label, "model and modular forms");
    vprint User1: "Starting model computation with low precision";
    N := M`N;
    prec := RequiredPrecision(M);
    SetSeed(0);
    M := FindModelOfXG(M,prec);
    if (not assigned M`prec) then
        M`prec := prec;
    end if;
    if (M`genus eq 1) and (assigned M`has_point) and (M`has_point) then
        // I'm just taking a guess on the precision here.
        // Test cases: 6.6.1.1, 6.12.1.1, 11.55.1.1, 8.48.1.3, 9.54.1.1, 20.72.1.23, 8.96.1.109
        // Minimal prec for 11.55.1.1 is 81
        success := false;
        prec := 2*M`index;
        // I'm pretty sure we only need 2*index + N,
        // but just in case we loop
        while (not success) do
            SetSeed(0);
	    M := FindModelOfXG(M,prec);
	    PP := Parent(M`f[1][1]);
	    jinv0 := jInvariant(PP.1);
	    jinv := Evaluate(jinv0,PP.1^N);
	    jinv2 := [ jinv : i in [1..M`vinf]];
	    success, ecjmap := FindRelationElliptic(M,jinv2);
            M`map_to_jline := ecjmap;
            M`prec := prec;
	    prec +:= N;
        end while;

        vprint User1: Sprintf("Minimal model is %o.", M`C);
        vprint User1: Sprintf("j-map is %o.", ecjmap);
        // Write data to a file here and then stop.
        // 5 is the code for hyperelliptic models
        // For now, we decided it includes Weierstrass equations
        ReportEnd(label, "model and modular forms", ttemp);
        return M, 5, 0, 0;
    end if;

    maxd := 0;
    mind := 0;
    maxprec := 0;
    // Compute the degree of the line bundle used
    if (M`mult ne [ 1 : i in [1..M`vinf]]) or (M`k ne 2) then
        vprint User1: "Curve is geometrically hyperelliptic.";
        model_type := -1; // "other"
        k := M`k;
        degL:= ((k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps) - (&+M`mult);
        old_degL := 0;
        while (old_degL ne degL) do
	    old_degL := degL;
	    maxd := Floor((M`index + M`genus - 1)/degL) + 1;
	    mind := maxd - 1;
	    vprint User1: Sprintf("Smallest degree that might work = %o. The degree %o definitely works.", mind, maxd);
	    maxprec := Floor(N*(M`k*maxd/12 + 1)) + 1;
	    if (maxprec gt M`prec) then
	        vprint User1: "Now that we know it's geometrically hyperelliptic, we need more precision.";
	        vprint User1: Sprintf("New precision chosen = %o.", maxprec);
	        delete M`has_point;
                SetSeed(0);
	        M := FindModelOfXG(M,maxprec);
	        vprint User1: "Recomputation of modular forms done.";
	        k := M`k;
	        degL:= ((k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps) - (&+M`mult);
	    end if;
        end while;
    else
        vprint User1: "Curve is not geometrically hyperelliptic.";
        model_type := 0; // canonical model
        maxd := Floor((M`index)/(2*M`genus-2) + 3/2);
        if ((maxd-1) ge (M`index)/(2*M`genus-2)) and ((maxd-1) le ((M`index)/(2*M`genus-2) + 1/2)) then
	    mind := maxd-1;
	    vprint User1: Sprintf("The smallest degree that might work is %o.", mind);
	    vprint User1: Sprintf("Degree %o definitly works.", maxd);
        else
	    mind := maxd;
	    vprint User1: Sprintf("The smallest degree that might work is %o and it definitely works.", maxd);
        end if;
        maxprec := Floor(N*(1 + maxd/6)+1);
        if (maxprec gt M`prec) then
	    vprint User1: "Now that we know it's non-hyperelliptic, we need more precision.";
	    vprint User1: Sprintf("New precision chosen = %o.", maxprec);
	    delete M`has_point;
            SetSeed(0);
	    M := FindModelOfXG(M, maxprec);
	    vprint User1: "Recomputation of modular forms done.";
        end if;
    end if;
    ReportEnd(label, "model and modular forms", ttemp);
    return M, model_type, mind, maxd;
end intrinsic;

BareGenus := recformat<genus>;

intrinsic ProcessModel(label::MonStgElt) -> Crv, SeqEnum,
                                            RngIntElt, SeqEnum[CspDat], Rec
{.}
    genus := StringToInteger(Split(label, ".")[3]);
    // Apparently, Rakvi's code does not handle X(1)
    if label eq "1.1.0.a.1" then
        // handle X(1)
	P1<x,y>:=Curve(ProjectiveSpace(Rationals(),1));
	cusps := CuspOrbits(1, [])[1];
	cusps[1]`coords := P1![1,0];
	// 1 is for P1 model
	return P1, FunctionField(P1).1, 1, cusps, rec<BareGenus|genus:=0>;
    elif (genus eq 0) then
        level, gens := GetLevelAndGensFromLabel(label);
	// !! TODO - is this precision always enough?
	Ggens := {GL(2,Integers(level))!g : g in gens};
        t0 := ReportStart(label, "Genus0Model");
	X<x,y,z>, j, has_rational_pt := ComputeModel(level,Ggens,10);
        ReportEnd(label, "Genus0Model", t0);
	// converting the function field element to something we can work with
	if Type(j) eq FldFunRatUElt then
	    num := Evaluate(ChangeRing(Numerator(j), Rationals()), x);
 	    denom := Evaluate(ChangeRing(Denominator(j), Rationals()), x);
	    // This assumes Parametrization is consistent with ParametrizationMatrix
	    // would be better to have this part inside Rakvi's code
	    param_Q := AlgebraMap(Parametrization(X)^(-1));
	    t := param_Q(Domain(param_Q).1) / param_Q(Domain(param_Q).2);
 	    num := Evaluate(num, [t,1,1]);
 	    denom := Evaluate(denom, [t,1,1]);
 	    j := num / denom;
	else
	    fun_coeffs := Eltseq(j);
	    coeff_coeffs := [<Coefficients(Numerator(f)),
			      Coefficients(Denominator(f))> : f in fun_coeffs];
	    function eval_at(c, a)
		return &+([0] cat [Rationals()!c[i]*(x/z)^(i-1) : i in [1..#c]]);
	    end function;
	    ev_coeffs := [eval_at(c[1], x/z)/eval_at(c[2],x/z) 
			  : c in coeff_coeffs]; 
	    j := &+([0] cat [ev_coeffs[i]*(y/z)^(i-1) 
			     : i in [1..Degree(Parent(j))]]);
	end if;
	model_type := (has_rational_pt) select 1 else 2;
	cusps := CuspOrbits(level, gens);
	// !! TODO - fix this so that the cusps on H will match the cusps on
	// the model
	// We only need one representative of each orbit
	cusps := [orb[1] : orb in cusps];
	P1 := ProjectiveSpace(Rationals(),1);
	jmap := map<X->P1 | [Numerator(j), Denominator(j)]>;
	cusp_scheme := (P1![1,0]) @@ jmap;
	cusp_coords := AssociativeArray();
	field_idx := AssociativeArray();
	for i in [1..#cusps] do
	    K := cusps[i]`field;
	    PK := DefiningPolynomial(K);
	    is_defined, pts := IsDefined(cusp_coords, PK);
	    if not is_defined then
		cusp_coords[PK] := Points(cusp_scheme, K);
		field_idx[PK] := 1;
	    end if;
	    cusps[i]`coords := cusp_coords[PK][field_idx[PK]];
	    field_idx[PK] +:= 1;
	end for;
	return X, j, model_type, cusps, rec<BareGenus|genus:=0>;
    end if;
    codomain := LMFDBReadRelativeJCodomain(label);
    if #codomain gt 0 then
        X, j, F0, M := RelativeJMap(label, codomain);
        model_type := 0;
    else
        X, j, model_type, F0, M := AbsoluteJMap(label);
        j := [Numerator(j), Denominator(j)];
    end if;
    cusps := CuspOrbits(level, gens);
    // We only need one representative of each orbit
    cusps := [orb[1] : orb in cusps];
    for i in [1..#cusps] do
	CuspUpdateCoordinates(~cusps[i], X, F0);
    end for;
    return X, j, model_type, cusps, M;
end intrinsic;

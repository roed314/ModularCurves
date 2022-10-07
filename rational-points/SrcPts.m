//pts - the points on some curve we found
//g - the dimension of ambient space of that curve (number of variables)
//MaxDeg - maximal degree of a field of definition of a point we are interested in

AnalyzePts := function(pts, g, MaxDeg)
	for pt in pts do
		FldDef := RationalsAsNumberField();
		deg := 1;

		for j in [1..g] do
			K := NumberField(MinimalPolynomial(pt[j]));
				
			if Degree(K) le 2 and deg eq 1 then
				FldDef := Compositum(FldDef, NumberField(MinimalPolynomial(pt[j])));
			else
				deg := -1;
				if Degree(K) ge Degree(FldDef) then
					FldDef := K;
				end if;
			end if;			
		end for;

		if Degree(FldDef) ge MaxDeg + 1 then
			continue;
		end if;
			
		if deg eq -1 then
			"Found point of degree (at least)", Degree(FldDef), ".";
			"It is defined over (maybe an extension of) a field given with defining polynomial:", DefiningPolynomial(FldDef);
			"--------------------------------------";
		else
			if Degree(FldDef) eq 2 then
				crit := 0;
				pol := MinimalPolynomial(pt[1]);
				
				for j in [1..g] do
					K := NumberField(MinimalPolynomial(pt[j]));
					if Degree(K) eq 2 then
						crit := j;
						pol := MinimalPolynomial(pt[j]);
						break;
					end if;
				end for;
				"Found point of degree exactly 2.";

				"";
				pt[crit], "is a zero of", pol;
				"";

				"Coordinates:", pt;
				"--------------------------------------";				
			else
				"Found point of degree exactly", Degree(FldDef), ".";
				"It is defined over a field given with defining polynomial:", DefiningPolynomial(FldDef);
				"Coordinates:", pt;
				"--------------------------------------";
			end if;
		end if;
	end for;
	return 1;
end function;


//we get some points on X
//X - some curve given by homogenous equations
//bd - bound for the absolute value of hyperplane coefficients
//MaxDeg - maximal degree of a field of definition of a point we are interested in
//SpecFld - whether we are looking for points over specific field
//F - the field over which we are searching for points

SearchPts := function(X, bd : MaxDeg := 10000, SpecFld := false, F := Rationals())
	CR<[x]> := CoordinateRing(AmbientSpace(X));
	NoVars := Dimension(AmbientSpace(X));

	"--------------------------------------";
	"FIRST GETTING POINTS WITH AT LEAST ONE ZERO COORDINATE...";
	"-------------------------------------";

	for i in [1..NoVars] do
		I := ideal<CR | x[i]>;
		Z := Scheme(X, I);

		if SpecFld eq false then
			pts := PointsOverSplittingField(Z);
			_ := AnalyzePts(pts, NoVars, MaxDeg);
		else
			pts := Points(ChangeRing(Z, F));
			_ := AnalyzePts(pts, NoVars, Degree(F));
		end if;
	end for;


	dim := Min(Degree(F) + 1, NoVars);
	
	if SpecFld eq false then
		dim := Min(MaxDeg + 1, NoVars);
	end if;
	
	C := CartesianPower([-bd..bd], dim);
	
	"--------------------------------------";
	"NOW POINTS WITH NON-ZERO COORDINATES...";
	"--------------------------------------";

	for a in C do
		b := [a[i] : i in [1..dim]];

		for i in [dim + 1..NoVars] do
			b := Append(b, 0);
		end for;

		if GCD(b) eq 1 then
			"Current linear coefficients: ", b;

			f := &+[b[i]*x[i] : i in [1..NoVars]];

			I := ideal<CR | f>;
			Z := Scheme(X, I);

			if SpecFld eq false then
				pts := PointsOverSplittingField(Z);
				_ := AnalyzePts(pts, NoVars, MaxDeg);
			else
				pts := Points(ChangeRing(Z, F));
				_ := AnalyzePts(pts, NoVars, Degree(F));
			end if;
		end if; 
	end for;

	return 1;
end function;

/*
load "X0p_NiceModel.m";

N := 163;

C := CuspForms(N);
"Dimension of CuspForms(N) is: ", Dimension(C);

ALN := AtkinLehnerOperator(C, N);
NN := Nullspace(Matrix(ALN - 1));

"Dimesion of eigenspace lambda = 1 for wN is: ", Dimension(NN);

NNc := Nullspace(Matrix(ALN + 1));

"Dimesion of eigenspace lambda = -1 for wN is: ", Dimension(NNc);
"";

BN := [&+[(Integers()!(2*Eltseq(Basis(NN)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NN)]];
BNc := [&+[(Integers()!(2*Eltseq(Basis(NNc)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(NNc)]];

XN := modformeqns(BNc cat BN, N, 500, 1);
"Nice model for X0(N) is:";
XN;
"";

_ := SearchPts(XN, 5: SpecFld := true, F := QuadraticField(-19));*/
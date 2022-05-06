

intrinsic FindddPolarizizedCurve(f::ModSym : prec:=80, ncoeffs:=10000, D:=[-10..10]) -> BoolElt, SeqEnum
{
    Finds smallest (d,d) polarization (if there is one) of the modular abelian surface associated to f
    Returns period matrix for the d-isogenous abelian variety which is principally polarized
}
	P := PeriodMatrix(f : prec:=prec, ncoeffs:=ncoeffs); 
	polarizations := SomePolarizations(P : D);  
	Zpol:= Matrix(Integers(), polarizations[1]);
	E1, F1:= FrobeniusFormAlternating(Zpol);
	for pol in polarizations do //find the (1,d) polarization with the smallest d
		Zpol:= Matrix(Integers(), pol);
		E, F:= FrobeniusFormAlternating(Zpol);
		if E[1][3]/E[2][4] gt E1[1][3]/E1[2][4] or (E[1][3]/E[2][4] eq E1[1][3]/E1[2][4] and  E[1][3] lt E1[1][3]) then //pick the smaller polarization
			E1 := E;
			F1 := F;
		end if;
	end for;
	Dscalar := Matrix([[1,0,0,0], [0,E1[1][3]/E1[2][4],0,0],[0,0,1,0],[0,0,0,1]]);
	CC := BaseRing(P);
	Dscalar* F1 * E1 * Transpose(Dscalar* F1); // this is the polarization we want, should we also return it?
	Pnew := P *Transpose(ChangeRing(Dscalar*F1, CC) );
	return Pnew;
end intrinsic;


//some other code that used to be useful, to check the above
newpols := SomePolarizations(Pnew : D); 

//at this point we can just reconstruct the curve
QQ := RationalsExtra(Precision(CC));
C := ReconstructCurve(Pnew, QQ);

//or we could also construct the polarization directly
Zpol:= Matrix(Integers(), newpols[1]);
smallestddpol, smallestF:= FrobeniusFormAlternating(Zpol);
for pol in newpols do //find the (d,d) polarization with the smallest d
	Zpol:= Matrix(Integers(), pol);
	E2, F2:= FrobeniusFormAlternating(Zpol);
	if E2[1][3]/E2[2][4] eq 1 then
		if smallestddpol[1][3] gt E2[1][3] then //pick the smaller polarization
			smallestddpol := E2;
			smallestF := F2;
		end if;
	end if;
end for;

Pfinal := Pnew *Transpose(ChangeRing(F2, CC) ); //this is the period matrix we actually want
C := ReconstructCurve(Pfinal, QQ); //but in reality we get the same curve




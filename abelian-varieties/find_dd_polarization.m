AttachSpec("spec");
f:= MakeNewformModSym(85, [<2,[-3,0,1]>]); //85.2.a.c
prec := 80;
ncoeffs:= 10000;
P := PeriodMatrix(f : prec:=prec, ncoeffs:=ncoeffs); 
polarizations := SomePolarizations(P : D:=[-20..20]);  
Zpol:= Matrix(Integers(), polarizations[1]);
pol0, F1:= FrobeniusFormAlternating(Zpol);
for pol in polarizations do //find the (1,d) polarization with the smallest d
	Zpol:= Matrix(Integers(), pol);
	E, F:= FrobeniusFormAlternating(Zpol);
	simplPol := F*pol*Transpose(F);
	if simplPol[1][3]/simplPol[2][4] gt pol0[1][3]/pol0[2][4] or (simplPol[1][3]/simplPol[2][4] eq pol0[1][3]/pol0[2][4] and  pol0[1][3] gt E[1][3]) then //pick the smaller polarization
		pol0 := E;
		F1 := F;
	end if;
end for;

Dscalar := Matrix([[1,0,0,0], [0,pol0[1][3]/pol0[2][4],0,0],[0,0,1,0],[0,0,0,1]]);
CC := BaseRing(P);
Dscalar* F1 * pol0 * Transpose(Dscalar* F1); // this is the polarization we want
Pnew := P *Transpose(ChangeRing(Dscalar*F1, CC) );
newpols := SomePolarizations(Pnew : D:=[-10..10]); 

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




AttachSpec("spec");
f:= MakeNewformModSym(85, [<2,[-3,0,1]>]);
prec := 80;
ncoeffs:= 10000;
P := PeriodMatrix(f : prec:=prec, ncoeffs:=ncoeffs); 
polarizations := SomePolarizations(P : D:=[-20,20]);   
pol0 := polarizations[1];
E, F := FrobeniusFormAlternating(Matrix(Integers(), pol0));
Dscalar := Matrix([[1,0,0,0], [0,E[1][3]/E[2][4],0,0],[0,0,1,0],[0,0,0,1]]);
CC := BaseRing(P);
Dscalar* F * pol0 * Transpose(Dscalar* F); // this is the polarization we want
Pnew := P *Transpose(ChangeRing(Dscalar*F, CC) );
newpols := SomePolarizations(Pnew : D:=[-10..10]); 

smallestddpol := -1;
smallestF:= -1;
for pol in newpols do //find the (d,d) polarization with the smallest d
	Zpol:= Matrix(Integers(), pol);
	E2, F2:= FrobeniusFormAlternating(Zpol);
	if E2[1][3]/E2[2][4] eq 1 then
		if smallestddpol eq -1 then //unassigned, assign to E2
			smallestddpol := E2;
			smallestF:= F2;
		elif smallestddpol[1][3] gt E2[1][3] then //pick the smaller polarization
			smallestddpol := E2;
			smallestF := F2;
		end if;
	end if;
end for;

Pfinal := P *Transpose(ChangeRing(F2, CC) );


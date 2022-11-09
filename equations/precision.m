import "OpenImage/main/ModularCurves.m" : FindModularForms, 
       FindCuspForms, FindRelations;

intrinsic RequiredPrecision(M::Rec) -> RngIntElt
{Precision required to get a model from David Zywina's code.}
  M := FindModularForms(2,M,1);
  prec := Integers()!(M`N * Maximum([1/M`widths[i] : i in [1..#M`cusps]]));
  done := false;
  while (not done) do
      repeat 
	  prec +:= 1;
	  found := false;
	  g := M`genus;
	  // for now, doing that naively
	  while (not found) do
	      M:=FindModularForms(2,M,prec);
	      M:=FindCuspForms(M);
	      F:=M`F0; 
	      assert #F eq g; 
	      
	      Pol<[x]>:=PolynomialRing(Rationals(),g);
	      PP:=ProjectiveSpace(Rationals(),g-1);
	      
	      I2:=FindRelations(F,2);
	      found := #I2 in {(g-1)*(g-2) div 2,((g-2)*(g-3)) div 2};
	      prec +:= 1;
	  end while;
	  
	  Q0:=Scheme(PP,I2);   
	  dimQ0:=Dimension(Q0);
      until dimQ0 ge 1;
      done := true;
      if  #I2 eq (g-1)*(g-2) div 2 then
	  if dimQ0 gt 1 then
	      done := false;
	  end if;
	  Q0:=Curve(PP,I2);
	  if not (IsIrreducible(Q0) and IsReduced(Q0)) then
	      done := false;
	  else
	      if Genus(Q0) ne 0 then
		  done := false;
	      end if;
	  end if;	  
      end if;
      if g eq 3 then
        I4:=FindRelations(F,4); 
        if #I4 gt 1 then
	    done := false;
	end if;
      end if;
  end while;
  return prec;
end intrinsic;	  
	  

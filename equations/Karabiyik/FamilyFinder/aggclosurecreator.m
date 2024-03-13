



//Based on Andrew Sutherland's intrinsic (which is faster than what I was using). 
function FiniteLift(A,N,M) 
    assert IsDivisibleBy(M, N);
    if N eq M then return A; end if;
    GL2 := GL(2,Integers(M));
    M2 := MatrixRing(Integers(),2);
    m := &*[a[1]^a[2]: a in Factorization(M)| N mod a[1] eq 0];
    return GL2!CRT([M2!A, Identity(M2)], [m, M div m]);
end function;




//This is the code for, given a subgroup G of GL_2(Zhat) containing identity and having full determinant, finding the family it lies in. 
//We first compute its agreeable closure calG', using this we find the family F(calG,B) such that calG' is conjugate to calG.  
function FamilyFinderNew(G, T)   
 /*
    Input:
	    G       : a subgroup of GL2(Zhat) full det, -I in G
	    T       : G meet SL2
    Output:  
        A family that G lies in. 
            
    Note: Assumes that the families.

 */

    N:=#BaseRing(G);
    M:=#BaseRing(T);
    g:=GL2Genus(T);
    T_level:=sl2Level(T);
    T:=ChangeRing(T,Integers(T_level));
    X:=AssociativeArray();
    G_level:=gl2Level(G);
    G:=gl2Lift(G,LCM([G_level,6]));
    T:=sl2Lift(T,LCM([T_level,6]));
    callevel:=1;
    for p in PrimeDivisors(#BaseRing(T)) do
        callevel:=callevel*p^(Maximum(Valuation(#BaseRing(T),p),Valuation(#BaseRing(G),p)));
    end for;
    calG:=ChangeRing(G,Integers(callevel));
    if not ContainsScalars(calG) then calG:=AdjoinScalars(calG); end if;
    calG_level:=gl2Level(calG);
    calG:=ChangeRing(calG,Integers(calG_level));
    T:=ChangeRing(T,Integers(T_level));
    G:=ChangeRing(G,Integers(N));
    Y:=AssociativeArray();
    for k in Keys(FAM) do
       
       
       //time0:=Realtime();
        if FAM[k]`B_level eq T_level and IsConjugate(GL(2,Integers(T_level)),T,FAM[k]`B) and g eq FAM[k]`genus and FAM[k]`calG_level eq calG_level then
            
             A,b:=IsConjugate(GL(2,Integers(calG_level)),calG,FAM[k]`calG);
            if A then 
                Y[k]:=<k,b>;
                //print(k);
            end if;
        end if;
        //print(Realtime(time0));
    end for;
    
    o:=1;
    for t in Keys(Y) do
        b:=FiniteLift(Y[t][2],calG_level,N);
        Tcong:=Conjugate(sl2Lift(T,N),b);
        if ChangeRing(Tcong,Integers(T_level)) eq FAM[t]`B then;
            o:=t;
        end if;
        
    end for;

    b:=FiniteLift(Y[o][2],calG_level,N);
    Gcong:=Conjugate(G,b);
    assert Gcong subset gl2Lift(FAM[o]`calG,N);
    assert IsNormal(gl2Lift(FAM[o]`calG,N),Gcong);
    Tcong:=Conjugate(sl2Lift(T,N),b);
    assert Tcong eq sl2Lift(FAM[o]`B,N);


    
return o,FAM[o],Gcong,gl2Lift(FAM[o]`calG,N),Tcong;

end function;




//This should be completely fine at this point.
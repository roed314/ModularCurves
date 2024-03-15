// Code in this file contributed by Eray Karabiyik

intrinsic Twist(M::Rec, xi::GrpHom, K::FldNum) -> Seq[RngMPolElt], AlgMatElt, RngIntElt
{
    Input:
      - M: a modular curve in the sense of Zywina.
      - xi: Gal(K/Q)-> GL(M`genus,K) 1-cocycle. This is a cocycle that extends from the Aut(M) (usually via AutomorphismOfModularForms function of Zywina).
      - K: the number field through which K factors

    Output:
      - a sequence "psi" of homogeneous polynomials in Q[x_1,..,x_#M`F0], defining the twisted curve.
}
    //For now we are working over Q.
    //Assuming H90 and Z's FindOpenImage are loaded.
    I:=M`psi;
    g:=M`genus;
    GAL,iota,sigma:=AutomorphismGroup(K);
    s:=#M`F0;
    //Transpose matrix because of Galois action used.
    MAT:=Transpose(H90(s,K,Rationals(),GAL,sigma,xi));
    Pol<[x]>:=PolynomialRing(K,s);
    PP:=ProjectiveSpace(K,s-1);
    //Applying the matrix to the polynomials already computed
    Itw:=[];
    for i in [1..#I] do
        Append(~Itw,Pol!I[i]^MAT);
    end for;


    //Get the coefficent vectors of polynomials in Itw to do Galois descent.
    mon2:=MonomialsOfDegree(Pol,2);
    mon3:=MonomialsOfDegree(Pol,3);
    mon4:=MonomialsOfDegree(Pol,4);
    mon:=mon2 join mon3 join mon4;


    coef2:=[];
    for f in Itw do
        Append(~coef2,[MonomialCoefficient(f,m): m in mon2]);
    end for;

    coef3:=[];
    for f in Itw do
        Append(~coef3,[MonomialCoefficient(f,m): m in mon3]);
    end for;


    coef4:=[];
    for f in Itw do
        Append(~coef4,[MonomialCoefficient(f,m): m in mon4]);
    end for;


    //We now do Galois descent separately for quadrics, cubics and quartics.


    UU2 := VectorSpace(K,#mon2);
    VV2:=sub<UU2| coef2>;
    // use this dimension

    I2G:=[];

    if not Dimension(VV2) eq 0 then
        coeff2:=[];
        for j in [1..#coef2] do //This is so that the trace map is never zero. However I am not sure if I am sure to get the correct dimension. over Q[x]?
            coeff2[j]:=[];
            for k in [1..#coef2[j]] do
                if coef2[j][k] ne 0 then
                    x:=coef2[j][k];
                    break k;
                end if;
            end for;
            for k in [1..#coef2[j]] do
                coeff2[j][k]:=coef2[j][k]/x;
            end for;
        end for;

        //Starting Galois descent now
        U2 := VectorSpace(K,#mon2);
        V2:=sub<U2| coeff2>;

        S2:={};

        i:=1;
        while i lt #coeff2+1 do

            v:=coeff2[i];
            tr:=&+[ Matrix(K,#mon2,1,[sigma(g)(v[i]): i in [1..#mon2]]) : g in GAL] / #GAL;
            tr:=V2!Transpose(tr);
            if Dimension(sub<V2|S2 join {tr}>) gt Dimension(sub<V2|S2>) then
                S2:=S2 join {tr};

            end if;
            i:=i+1;
        end while;

        I2G:=[];

        for v in S2 do
            f:=0;
            for i in [1..#mon2] do
                f:=f+v[i]*mon2[i];
            end for;
            Append(~I2G,f);
        end for;
    end if;



    UU3 := VectorSpace(K,#mon3);
    VV3:=sub<UU3| coef3>;
    // use this dimension

    I3G:=[];

    if not Dimension(VV3) eq 0 then
        coeff3:=[];
        for j in [1..#coef3] do //This is so that the trace map is never zero. However I am not sure if I am sure to get the correct dimension. over Q[x]?
            coeff3[j]:=[];
            for k in [1..#coef3[j]] do
                if coef3[j][k] ne 0 then
                    x:=coef3[j][k];
                    break k;
                end if;
            end for;
            for k in [1..#coef3[j]] do
                coeff3[j][k]:=coef3[j][k]/x;
            end for;
        end for;

        //Starting Galois descent now
        U3 := VectorSpace(K,#mon3);
        V3:=sub<U3| coeff3>;

        S3:={};

        i:=1;
        while i lt #coeff3+1 do
            v:=coeff3[i];
            tr:=&+[ Matrix(K,#mon3,1,[sigma(g)(v[i]): i in [1..#mon3]]) : g in GAL] / #GAL;
            tr:=V3!Transpose(tr);
            if Dimension(sub<V3|S3 join {tr}>) gt Dimension(sub<V3|S3>) then
                S3:=S3 join {tr};
            end if;
            i:=i+1;
        end while;

        I3G:=[];

        for v in S3 do
            f:=0;
            for i in [1..#mon3] do
                f:=f+v[i]*mon3[i];
            end for;
            Append(~I3G,f);
        end for;
        if not Dimension(VV2) eq 0 and not Dimension(VV2) eq 0 then
            V:=VectorSpace(Rationals(),#mon3);
            W:=sub<V| [V![MonomialCoefficient(x[i]*f,m): m in mon3] : i in [1..s], f in I2G]>;
            V3:=sub<V| [V![MonomialCoefficient(f,m): m in mon3] : f in I3G]>;
            J:=[];
            i:=1;
            while Dimension(W) lt Dimension(V3) do
                v:=V![MonomialCoefficient(I3G[i],m): m in mon3];
                if v notin W then
                    W:=sub<V|Generators(W) join {v}>;
                    J:=J cat [I3G[i]];
                end if;
                i:=i+1;
            end while;
        end if;
    end if;



    UU4 := VectorSpace(K,#mon4);
    VV4:=sub<UU4| coef4>;
    // use this dimension

    I4G:=[];

    if not Dimension(VV4) eq 0 then
        coeff4:=[];
        for j in [1..#coef4] do //This is so that the trace map is never zero. However I am not sure if I am sure to get the correct dimension. over Q[x]?
            coeff4[j]:=[];
            for k in [1..#coef4[j]] do
                if coef4[j][k] ne 0 then
                    x:=coef4[j][k];
                    break k;
                end if;
            end for;
            for k in [1..#coef4[j]] do
                coeff4[j][k]:=coef4[j][k]/x;
            end for;
        end for;

        //Starting Galois descent now
        U4 := VectorSpace(K,#mon4);
        V4:=sub<U4| coeff4>;

        S4:={};

        i:=1;
        while i lt #coeff4+1 do
            v:=coeff4[i];
            tr:=&+[ Matrix(K,#mon4,1,[sigma(g)(v[i]): i in [1..#mon4]]) : g in GAL] / #GAL;
            tr:=V4!Transpose(tr);
            if Dimension(sub<V4|S4 join {tr}>) gt Dimension(sub<V4|S4>) then
                S4:=S4 join {tr};
            end if;
            i:=i+1;
        end while;

        I4G:=[];

        for v in S4 do
            f:=0;
            for i in [1..#mon4] do
                f:=f+v[i]*mon4[i];
            end for;
            Append(~I4G,f);
        end for;
    end if;

    return I2G cat I3G cat I4G, MAT,s;

end intrinsic;

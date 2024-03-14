
function GroupToCocycle(calG,G,H,T,M,AOfMF)
    /*
        Input:  calG: This is an open subgroup of GL2(Zhat), containing negative identity with full determinant.
                G: A representative in the family F(calG,G)=F(calG,B) for some B arising from our calculations. Check Zywina-Explicit Open Image-Chapter 14 for details.
                H: A group in the family F(calG,G). This will be the group we are trying to compute the modular curve of.
                T: SL2 intersection of H
                M: Modular curve of G.
                Note that G and H are switched here, notationwise
        Output:
                xi: Gal(K/Q)-> GL(#M`F0,K) 1-cocycle arising from the map H-> calG/G
    */
    //Arranging the levels
    N1:=#BaseRing(calG);
    N2:=#BaseRing(G);
    calGAut:=gl2Lift(calG,LCM([N1,N2]));
    N3:=#BaseRing(H);
    N4:=#BaseRing(T);
    N:=LCM([N1,N2,N3,N4]);
    calG:=gl2Lift(calG,N);
    G:=gl2Lift(G,N);
    H:=gl2Lift(H,N);
    T:=sl2Lift(T,N);

    UN,iotaN:=UnitGroup(Integers(N));
    SL2:=SL(2,Integers(N));
    H1:=T;
    //Forming the quotient calG/G. We have to make it into an abelian group so that the kernels actually work.
    quocalG,quomapG:= quo<calG|G>;
    quocalGG,quomapGG:=AbelianGroup(quocalG);
    //Defining the necessary map like inclusions and so on.
    phi:=hom<H->calG| [H.i : i in [1..Ngens(H)]]>;

    //Transversals are like representatives from the cosets. Very useful for many things.
    K:=Transversal(H,H1);
    xi:=map<{iotaN(d): d in UN}-> Parent([1]) | [<Determinant(t),[Integers()!a:a in Eltseq(t)]>: t in K]>;

    //Abelian work. gammadd here is an homomorphism whose kernel will be useful.
    gammad:=map<{iotaN(d): d in UN}-> quocalGG | [<Determinant(t),quomapGG(quomapG(phi(xi(Determinant(t)))))>: t in K]>; //This gamma for now gives what? it gives in the quotient as  permutations

    gammadd:=hom<UN-> quocalGG | [gammad(iotaN(UN.i)): i in [1..Ngens(UN)]]>;// This is a homomorphism

    //These are only with quocalG. Migt be useful. map gamma gives matrices which can be useful to calculate the ambient automorphism matrices.
    //gammad1:=map<{iotaN(d): d in UN}-> quocalG | [<Determinant(t),quomapG(phi(xi(Determinant(t))))>: t in K]>; //This gamma for now gives what? it gives in the quotient as  permutations
    //gammadd1:=hom<UN-> quocalG | [gammad1(iotaN(UN.i)): i in [1..Ngens(UN)]]>;// This is a homomorphism
    //gamma:=map<UN-> calG | [ <d,gammadd1(d) @@ quomapG>: d in UN]>;//this gives the matrices so that i can put the images into autofmodcurves

    //Now we have some of the maps we needed. We will put all these in nice forms.
    KN<a>:=CyclotomicField(N);
    GAL,iota,sigma:=AutomorphismGroup(KN);

    genlist:=[];
    gallist:=[];
    for i in [1..Ngens(UN)] do
        Append(~genlist,UN.i);
        _:=exists(g0){g0: g0 in GAL | sigma(g0)(a) eq a^(Integers()!iotaN(UN.i)) };
        Append(~gallist,g0);
    end for;

    galiso:=hom<UN->GAL | [gallist[i]: i in [1..Ngens(UN)]]>;
    galisoa:=Inverse(galiso);
    xi1:=hom<GAL-> quocalGG | [gammadd(galisoa(GAL.i)): i in [1..Ngens(GAL)]]>;//This is the cocycleish

    //Now fine tuning stuff.
    Ker:=Kernel(xi1);
    Kfield:=FixedField(KN,Ker);
    GAL1,iota1,sigma1:=AutomorphismGroup(Kfield);

    quogal,qmapgal:= quo<GAL|Ker>;
    bool,isomap:=IsIsomorphic(GAL1,quogal);

    xi2:=hom<GAL1-> calG | [<d,(gammadd(galisoa(isomap(d) @@ qmapgal)) @@ quomapGG)@@ quomapG>: d in GAL1]>;
    //This takes from the field of definition and gives matrices that can be put into autofmodularforms.

    //xi:=map<GAL1-> MatrixRing(Kfield,#M`F0) | [<d,AutomorphismOfModularForms(M,M`F0,xi2(d))>: d in GAL1]>;

    aut1:=hom<calGAut ->GL(#M`F0,Kfield) | [AOfMF[i]:i in [1..Ngens(calGAut)]]>;
    aut:=lift_hom(aut1,N);

    xi:=hom<GAL1-> GL(#M`F0,Kfield) | [<d,aut(xi2(d))>: d in GAL1]>;



    //xi:=hom<GAL1-> GL(#M`F0,Kfield) | [<d,AutomorphismOfModularForms(M,M`F0,xi2(d))>: d in GAL1]>;



    return xi,Kfield,GAL1,sigma1;


end function;



// Code in this file contributed by Eray Karabiyik

/*
//We load all of our families. The file size will be much lower.
load "../FamilyData/familycreatecodewithanarrayfosubgroup.m";
I:=Open("../FamilyData/Genus0Families.dat", "r");
FAM:=AssociativeArray();
a:=1;
repeat
    b,y:=ReadObjectCheck(I);
    if b then
        FAM[a]:=y;
    end if;
    a:=a+1;
until not b;


I:=Open("../FamilyData/Genus1Families.dat", "r");
repeat
    b,y:=ReadObjectCheck(I);
    if b then
        FAM[a]:=y;
    end if;
    a:=a+1;
until not b;
*/

I:=Open("/homes/ek693/Main/NewFamiliesWithAuts1.dat", "r");
FAM:=AssociativeArray();
a:=1;
repeat
    b,y:=ReadObjectCheck(I);
    if b then
        FAM[a]:=y;
    end if;
    a:=a+1;
until not b;



intrinsic FindModelNew(G::GrpMat, T::GrpMat) -> Seq[RngMPolElt], AlgMatElt
{
    Input:
    - G is a subgroup of GL2(Zhat). It is given by a subgroup of GL2(Z/NZ)
      where N is a multiple of the level of G.
    - T is the intersection of G with SL2(Z/NZ)

    Output:
    - homogeneous polynomials in Q[x_1,..x_n] defining the curve X_G mentioned above.
      n depends on the model of the family representative used to twist G from.
    - a matrix describing the twist from the family representative to G.
}

    //We first start with finding the family in our database that contains G.
    print("Finding the family...");
    k,famG,Gcong,calGlift,Tcong:=FamilyFinderNew(G,T);
    N:=#BaseRing(G);
    printf "The family key in the database is %o\n",k;
    //The following piece of code can be used if the modular curve is not already precomputed.
    /*
    if not assigned famG`M then
        print("No modular curve record found in the family. Computing it...");
        M:=FindModelOfXG(CreateModularCurveRec0(famG`H),10 : G0:=famG`calG);
        printf "Computed";
    else
        M:=famG`M;
    end if;
    */
    //Now we conjugate G so that it lies in fam_G`calG. Gcong computed above is already the conjugated version.
    AOfMF:=famG`AOfMF;
    M:=famG`M;
    G:=Gcong;
    T:=Tcong;
    //Computing the cocycle related to H and G. See the paper for details. (Paper is not out yet so look at the file)
    printf "Computing the cocycle\n";
    xi,K:=GroupToCocycle(famG`calG,famG`H,G,T,M,AOfMF);
    //Now the twist
    printf "Twisting the curve...\n";
    psi,MAT:=Twist(M,xi,K, famG`calG);

    return psi,MAT;
end intrinsic;

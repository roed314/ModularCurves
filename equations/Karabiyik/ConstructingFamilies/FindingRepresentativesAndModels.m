// We will probably not be using this file


load "../OpenImage/main/FindOpenImage.m";
load "../OpenImage/SZ-data/RationalFunctions.m";
load "../OpenImage/SZ-data/GL2Invariants.m";
load "../OpenImage/SZ-data/g0groups.m";
load "../FamilyData/familycreatecodewithanarrayfosubgroup.m";
load "../RepresentativeFinder/special.m";

I:=Open("../ConstructingFamilies/Families.dat", "r");
FAM:=AssociativeArray();
a:=1;
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		FAM[a]:=y;
	end if;
    a:=a+1;
until not b;

"Making groups simple";

for k in Keys(FAM) do
    if FAM[k]`calG_level eq 1 or FAM[k]`B_level eq 1 then continue; end if;
    time0:=Realtime();
    FAM[k]`calG:=ChangeRing(FAM[k]`calG,Integers(FAM[k]`calG_level));
    FAM[k]`B:=ChangeRing(FAM[k]`B,Integers(FAM[k]`B_level));
    print(k);
    print(Realtime(time0));
end for;

"Finding Representatives";
for k in Keys(FAM) do
    print(k);
    time0:=Realtime();
    T:=FindSpecialSubgroup(FAM[k]`calG,FAM[k]`B);
    if gl2DetIndex(T) eq 1 then
        if gl2Level(T) eq 1 then continue k; end if;
        T:=ChangeRing(T,Integers(gl2Level(T)));
        FAM[k]`H:=T;
    end if;
    print(Realtime(time0));
end for;

"Saving to file";

I:=Open("../ConstructingFamilies/FamiliesWithRepresentatives.dat", "w");
for k in Keys(FAM) do
    x:=FAM[k];
    WriteObject(I, x);
end for;

//Note that current FindModelOfXG and FindCanonicalModel are adjusted so that it works for our purposes (mostly about prec, but there are issues with canonical models cut out by quadrics and cubics at the same time)
"Computing modular curves for representatives";
for k in Keys(FAM) do
    if FAM[k]`calG_level eq 1 or FAM[k]`B_level eq 1 then continue; end if;
    time0:=Realtime();
    print(k);
    if assigned FAM[k]`H then
        FAM[k]`M:=FindModelOfXG(CreateModularCurveRec0(FAM[k]`H),10: G0:=FAM[k]`calG, simplify_cubic:=false);
        print(k);
        calG:=FAM[k]`calG;
        H:=FAM[k]`H;
        M:=FAM[k]`M;
        calG:=gl2Lift(calG,LCM([#BaseRing(calG),#BaseRing(H)]));
        for i in [1..Ngens(calG)] do
            FAM[k]`AOfMF[i]:=AutomorphismOfModularForms(M,M`F0,calG.i);
        end for;
        print(Realtime(time0));
    end if;
end for;

/*
"Computing Automorphisms of Modular Forms";

for k in Keys(FAM) do;
    if assigned FAM[k]`M then
        time0:=Realtime();
        print(k);
        calG:=FAM[k]`calG;
        H:=FAM[k]`H;
        M:=FAM[k]`M;
        calG:=gl2Lift(calG,LCM([#BaseRing(calG),#BaseRing(H)]));
        for i in [1..Ngens(calG)] do
            FAM[k]`AOfMF[i]:=AutomorphismOfModularForms(M,M`F0,calG.i);
        end for;
        print(Realtime(time0));
    end if;
end for;
*/


//After this is done we should be able to delete the q-expansions from FAM[k]`M.


"Saving to file";

I:=Open("../ConstructingFamilies/FamiliesWithModels.dat", "w");
for k in Keys(FAM) do
    x:=FAM[k];
    WriteObject(I, x);
end for;



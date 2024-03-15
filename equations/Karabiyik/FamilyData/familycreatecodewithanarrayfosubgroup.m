
//This a record for the families we will use. I think most entries are clear.
FamilyRec := recformat<
    calG_level, B_level, calG_index, B_index, genus, sl2level, level, k, prec, commutator_index :RngIntElt,
    calG_gens, B_gens, subgroupsofH :SeqEnum,
    works: BoolElt,
    calG,B,H, commutator_sub :GrpMat,
    onelementpossibly: BoolElt,
    M, AOfMF
    >;


//Creates a family once we already have calG and B.

intrinsic CreateFamilyRecSubgroup(calG::GrpMat, B::GrpMat  : compute_comm:=false, compute_calgmeetsl2:=false) -> Rec
{
    Input:
	    calG    : an agreeable subgroup
	    B       : an open subgroup of SL2(Zhat) such that [calG,calG] subseteq B subseteq SL2 meet calG
    Output:
        A record of type "FamilyRec" with the following entries computed:
            calG, B, calG_level, B_level, calG_gens, B_gens
 }

    F := rec<FamilyRec | calG:= calG ,B:=B >;
    calG_level:=gl2Level(calG);
    B_level:=sl2Level(B);
    //calG_index:=Index(GL(2,Integers(calG_level)),ChangeRing(calG,Integers(calG_level)));
    //B_index:=Index(SL(2,Integers(B_level)),ChangeRing(B,Integers(B_level)));
    genus:=GL2Genus(B);

    if compute_comm eq true then
        comm_level,gens,i_comm:=FindCommutatorSubgroup(calG);
        commutator_sub:=sub<SL(2,Integers(comm_level))|gens>;
        F`commutator_sub:=commutator_sub;
    end if;


    calG_gens:=[Eltseq(g): g in Generators(calG)];
    B_gens:=[Eltseq(g): g in Generators(B)];

    F`calG_level:=calG_level;
    F`B_level:=B_level;
    F`genus:=genus;
    F`calG_gens:=calG_gens;
    F`B_gens:=B_gens;
    F`AOfMF:=AssociativeArray();

    return F;
end intrinsic;

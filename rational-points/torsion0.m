//this is the simplest function for the upper bound- it takes a curve X and a list of primes of good reduction and gives a group such that the torsion is isomorphic to a subgroup of this group

function torsion_UB0(X,lst)
    trs:=[];
    for i:=1 to #lst do 
        p:=lst[i];
        trs:=trs cat [Invariants(TorsionSubgroup(ClassGroup(ChangeRing(X,GF(p)))))];
    end for;
    lnt:=Min([#a : a in trs]);
    res:=[];
    for i:=1 to lnt do 
        x:=[trs[j,#trs[j]-lnt+i]: j in [1..#lst]];
        res:= res cat [GCD(x)];
    end for;
    return res;
end function;
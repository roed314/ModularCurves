// Magma code to support the calculations in the paper Quadratic.Points on Non-Split Cartan Modular Curves.

// This code carries out the computations of Section 5.5 to test saturation.

function FindIntegerCoprimeToIndex(C, l, r, gens : pprimes := [2,3,5,7,11,13,17,19])
    Zlr:=AbelianGroup([l : i in [1..r]]);            
    IntKl := Zlr;                         
    for p in pprimes do
        try                        
            Cp,redp:=ChangeRing(C,GF(p));
            CpGrp,phi,psi:=ClassGroup(Cp);
        catch e 
            continue;
        end try;        
        /*Z:=FreeAbelianGroup(1);
        degr:=hom<CpGrp->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CpGrp)]>;  
        JFp:=Kernel(degr); // Jacobian mod p as an abelian group*/
        JFp := TorsionSubgroup(CpGrp);
        JFpmodl,pi:=quo<JFp | l*JFp>;   

        pil:=hom<Zlr->JFpmodl | [pi(psi(redp(pt))) : pt in gens]>; 
        Kl:=Kernel(pil);
        printf "Calculations completed for p = %o.\n", p;
        IntKl meet:= Kl;
        if #IntKl eq 1 then 
            return true; // the index is not divisible by l
        end if;
    end for;
    return false; // the index might be divisible by l
end function;

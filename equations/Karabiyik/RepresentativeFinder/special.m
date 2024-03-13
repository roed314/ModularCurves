//Code by David Zywina
function FindSpecialSubgroup(G,W)
    /*  Input:
            - G an open subgroup of GL(2,Zhat), given as a group in GL(2,Z/NZ), that contains
                all the scalar matrices.
            - W an open subgroup of SL(2,Zhat) that is contained in G and contains [G,G];
                it is given as a subgroup of SL(2,Z/MZ)
    
        Output:
            This function find an open subgroup B of G such that B intersected with SL(2,Zhat) 
            is W and such that the index [det(G):det(B)] is minimal.

            Let m be the lcm of N and M.  
            When m is odd, B will be a group given modulo m.
            When m is odd, B will be a group given modulo m times some power of 2.
    */

    N:=LCM(#BaseRing(G),#BaseRing(W));
    if IsEven(N) then N:=LCM(N,8); end if;

    UN,iotaN:=UnitGroup(Integers(N));
    G1:=gl2Lift(G,N); 
    W1:=sl2Lift(W,N);

    // We work with 2-Sylow subgroups to work out the 2-adic part
    G1_2:=SylowSubgroup(G1,2);
    W1_2:=W1 meet G1_2; // a 2-sylow subgroup of W1
    Q1,phi1:=quo<G1_2|W1_2>;
    Q,phi2:=AbelianGroup(Q1);
    detQ:=hom<Q->UN | [ Determinant((Q.i @@ phi2) @@ phi1) @@ iotaN : i in [1..Ngens(Q)]] >;
    K:=Kernel(detQ);
    U:=detQ(Q);
    m:=2^Valuation(N,2);
    Um,iotam:=UnitGroup(Integers(m));
    redm:=hom<UN->Um | [ (Integers(m)!iotaN(UN.i))@@ iotam : i in [1..Ngens(UN)] ]>;            
    S:=(sub<Um|[(-1)@@iotam]> @@ redm) meet U;  //2-torsion subgroup

    C,phiC:=quo<U|S>;
    assert IsCyclic(C);
    if #C ne 1 then
        c:=AbelianBasis(C)[1];
        u0:=c@@phiC;
        e:=Minimum({Order(u0+s) : s in S });
        u:=Rep({u0+s: s in S | Order(u0+s) eq e});

        if e gt Order(c) then
            G1:=gl2Lift(G,N*2);  
            W1:=sl2Lift(W,N*2);    
            return FindSpecialSubgroup(G1,W1);
        end if;
    
        g0:=u @@ detQ;

        done:=false;
        for k in K do
            if Order(g0+k) eq Order(u) then
                done:=true;
                g:=g0+k;
                break k;
            end if;
        end for;

        if not done then
            G1:=gl2Lift(G,N*2); 
            W1:=sl2Lift(W,N*2);    
            return FindSpecialSubgroup(G1,W1);
        end if;

        g:=(g @@ phi2) @@ phi1;
        gens1:=[g];
    else
        gens1:=[];
    end if;

    V:={u: u in S | exists{g: g in Q | detQ(g) eq u and Order(u) eq Order(g)} };
    subgroups_S:=[H`subgroup: H in Subgroups(S)];
    ord:=[#H: H in subgroups_S]; 
    ParallelSort(~ord,~subgroups_S);
    subgroups_S:=Reverse(subgroups_S);    // The groups should be ordered by cardinality

    ord:=[#H: H in subgroups_S]; 
    assert Reverse(ord) eq Sort(ord);

    for H in subgroups_S do
        if {g: g in H} subset V then
            S0:=H;
            break H;
        end if;
    end for;
    
    basis_S0,I:=AbelianBasis(S0);
    C:=[];
    for u in basis_S0 do
        C:=C cat [ Rep({g: g in Q | detQ(g) eq u and Order(u) eq Order(g)}) ];
    end for;
    gens2:=[(c @@ phi2) @@ phi1: c in C];
    gens2:=[GL(2,Integers(N))!c: c in gens2];
    
    // Odd part.
    basis,I :=PrimaryAbelianBasis(UN);
    basis:=[basis[i]: i in [1..#I] | IsOdd(I[i])];
    gens3:=[];
    for b0 in basis do
        b:=Integers(N)!iotaN(b0);
        gens3:=gens3 cat [GL(2,Integers(N))![b,0,0,b]];
    end for;
        
    gens4:=[g: g in Generators(W1)];

    B:=sub<GL(2,Integers(N))| gens4 cat gens3 cat gens2 cat gens1>;
    //time b:=W1 eq B meet SL(2,Integers(N));  // check
    return B;
end function;


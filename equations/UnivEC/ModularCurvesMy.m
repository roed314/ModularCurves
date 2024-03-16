// This is a modification of David Zywina's "ModularCurves.m".
// The parameter mult is now part of ModularCurveRec.
// When a space of modular forms is computed, the lower bounds on order of vanishing at each
// cusp is now stored. 

// This contains our basic functions for working with modular forms and modular curves.
// Assumes that "GL2GroupTheory.m" has been loaded already.     



// A record of type "ModularCurveRec" encodes information about the curve X_G where G is a subgroup of GL(2,Z/NZ) with 
// full determinant and N>1.   
// The curve X_G is defined over Q and has function field F_N^G.    It is smooth, projective and geometrically irreducible.

ModularCurveRec := recformat<
    N, index, degree, genus, v2, v3, vinf, sl2level, level, k, dimMk, dimSk, prec, commutator_index :RngIntElt,                     
    gens, cusps, widths, regular, F, F0, f, trdet, pts, key, exceptional_jinvariants, Gc_decomp, high_genus_model, 
        cyclic_invariants, cyclic_models, cyclic_generators, cover_with_same_commutator_subgroup, psi :SeqEnum,   
    has_point, has_infinitely_many_points, has_nonCM_point, is_agreeable, is_entangled, extraneous, is_serre_type_model: BoolElt,                                                              
    G, H, Hc, Gc :GrpMat,    
    Hc_gen, mult: SeqEnum,                      
    C:Crv, 
    map_to_jline, pi: List,
    sturm: FldRatElt >;	 

/*                            
 DESCRIPTION OF ENTRIES:
    _______________________________________________________
    N: a positive integer 
    G: a subgroup of GL(2,Z/NZ);  we will often view it as an open subgroup of GL(2,Zhat) by taking its inverse mod N.
    gens: a sequence of generators of G
    H: the intersection of G with SL(2,Z/NZ)            
    level: level of G (note: we almost always work with the case N=level)
    sl2level: level of \pm H
    tr_det: set of pairs (tr(g),det(g)) in (Z/NZ)^2 as we vary over all g in G
    _______________________________________________________

    Let X_Gamma:=Gamma\H^* be the smooth compact Riemann surface, where Gamma=Gamma_G is the congruence subgroup of SL_2(Z)
    consisting of matrices whose image modulo N lie in G.  We can identify the complex points X_G(C) with X_Gamma.

    genus: genus of X_G
    v2: number of elliptic points of order 2 for X_G
    v3: number of elliptic points of order 3 for X_G
    vinf: number of cusps of X_G
    degree: index of \pm Gamma in SL(2,ZZ); equivalently, the degree of the natural map  X_Gamma \to X_{SL(2,Z)} (or the j-map X_G\to P^1)
    
    cusps: a sequence of matrices A in SL(2,Z) so that A*infty represent the cusps of X_Gamma.
           Note:  We actually give A modulo N; the corresponding cusp of X_Gamma is unaffected by the choice of lift to SL(2,Z).
    regular: a sequence of booleans (ordered the same as "cusps") indicating whether the corresponding cusp is regular
    widths: sequence consisting of the widths of the cusps (ordered the same as "cusps")
    
    index: index of G in GL(2,Z/NZ); when G contains -I and has full determinant, this agrees with "degree" as above.
    _______________________________________________________
    
    k: an integer > 1
    dimMk: dimension of M_k(Gamma) over C;  same as dimension of M_{k,G}:=M_k(Gamma(N),Q(zeta_N))^G over Q when G has full determinant
    dimSk: dimension of S_k(Gamma) over C
    sturm:  a rational number occurring in our version of Sturm's bound (for k even, this is the quantity B_{k,G} in the paper).
    
    prec: a positive integer used to encode how many terms of each q-expansion we compute
    F: a sequence giving a basis of the Q-vector space M_{k,G} when computed

       Each F[i] is a modular form; it is given as a sequence of q-expansions at the cusps (with respect to the matrices in "cusps").
       Each q-expansion is a power series in the variable qN:=q^(1/N) with coefficients in Q(zetaN); 
       all q-expansions will be given up to at least O(qN^prec).

    F0: same as above, but for the Q-subspace of M_{k,G} given by prescribed vanishing conditions at the cusps (for example, cusp forms).
    _______________________________________________________
    
    has_point: boolean that, if assigned, is "true" if and only X_G has a Q-point.
    has_nonCM_point: boolean that, if assigned, is "true" if and only X_G has a nonCM Q-point.
    has_infinitely_many_points: boolean that, if assigned, is "true" if and only X_G(Q) is infinite.
    is_agreeable: boolean that is "true" when the inverse image of Gin GL(2,Zhat) is an agreeable group (see paper).
    is_entangled: boolean that is "true" if the inverse image of G in GL(2,Zhat) is not the product of its l-adic projections.
    _______________________________________________________
    
    ** We use the following when X_G has genus at most 1 and a known rational point **

    C:  a nice model for X_G, which is either P^1 or an elliptic curve over Q.
    f:  When X_G has genus 0, f is a modular function satisfying Q(X_G)=Q(f); it is given as a sequence of q-expansions 
            at the cusps (with respect to the matrices in "cusps").
        When X_G has genus 1, f=[x,y] with x and y modular functions satisfying Q(X_G)=Q(x,y) and also satisfying the Weierstrass
            equation given by C; they are given as a sequence of q-expansions at the cusps (with respect to the matrices in "cusps").
    pi: Assuming X_G is not the j-line, a pair describing the natural morphism from X_G to X_B, where B is an open subgroup of 
        GL(2,Zhat) containing G; in our constructions, there will be no subgroups strictly between G and B.
            - pi[1] will be a label for the modular curve X_B (in the array of modular forms we construct)
            - pi[2] will be a sequence of homogeneous polynomials describing the morphism 
              (with respect to the models given by the entries C and f)              
    map_to_jline: natural morphism from X_G to the j-line  (with respect to the model of X_G given by C and f).  It is given as the single entry
            of a list with type MapSch (this is done so we can save the records using WriteObject)  

    _______________________________________________________
    
    In the following, view G as an open subroup of GL(2,Zhat).

    Hc: a group representing the commutator subgroup [G,G] in SL(2,Zhat)
    commutator_index: index of [G,G] in SL(2,Zhat)
    cover_with_same_commutator_subgroup:  in the array of modular curves we compute, this is a label of a modular curve
        X_B so that G is conjugate to a subgroup of B with the commutator subgroups [G,G] and [B,B] agreeing.  We
        choose B, from our array, with minimal index in GL(2,Zhat).
    extraneous: boolean that is "true" when "cover_with_same_commutator_subgroup" is not the label of the curve X_G itself.
    Hc_gen: a sequence consisting of matrices in SL(2,Z) (given as length four sequences); they topologically generated Hc
        as an open subgroup of SL(2,Zhat).

    The following are only constructed when "extraneous" is false.

    Gc : a choice of open subgroup of G with full determinant such that Hc=[G,G] is the intersection of Gc and SL(2,Zhat);
         Gc is a normal subgroup of G and G/Gc is finite and abelian.

        There are groups G_1,..,G_s betwen Gc and G that induce an isomorphism between G/Gc and the product
                    G/G_1 x ... x G/G_s.
        We can choose G_i so that the groups G/G_i are nontrivial and cyclic of prime power order q_i. 

    Gc_decomp: the sequence [G_1,..,G_s]
    cyclic_invariants: [q_1,...,q_s]
    cyclic_generators: a sequence [g_1,..,g_s] so that g_i is an element of G that generates G/G_i.
    cyclic_models: A sequence of length s.  We now describe cyclic_models[i]:
        As discussed in the paper, there is a certain cover Y->X_G that has Galois group G/G_i.    
        We construct a, possibly singular, model of Y that consists of equations of the form
                F_1(x_1,...x_m)= c_1, ....,  F_r(x_1,...x_m)= c_r,
        where the F_j are a sequence of homomogeneous polynomials depending only on q_i (they are given in the 
        file "cyclic_invariant_polynomials.m") and the c_j are in Q(X_G).
        We take cyclic_models[i] to be the sequence [c_1,..,c_r] where each c_j is given in terms of model C for X_G.
    _______________________________________________________            
    Some entries that are occasionally used:
    pts:  when the modular curve X_G has only finitely many rational points, we may want to keep track of some of the
            known rational points with respect to a computed model
    exceptional_jinvariants: when the modular curve X_G has only finitely many rational points, we may want to keep 
            track of the j-invariants of known rational nonCM points.
    psi:  when we compute a model for X_G in some projective space P^n, we use this to record the defining equations.
    _______________________________________________________
    
    key: when part of an array of modular curves, this is the lable/key for the given curve.
    _______________________________________________________

    ** We use the following when X_G has genus at least 2 **
    
    pi:  We will find an open subgroup B of GL(2,Zhat) that contains G for which X_B has genus at most 1 and has a 
            rational point. In our array of modular curves we construct, X_B will have label pi[1].
    high_genus_model:  This is a squence that encodes the minimal polynomial P of h over Q(X_B), where h is some 
            modular function for which Q(X_G)=Q(X_B)(f).  The polynomial P, with an explicit description of Q(X_G), 
            gives a singular model of X_G.
            See the code for how this is encoded, in particular:
    is_serre_type_model: describes how the polynomial P for "high_genus_model" is encoded.

*/
  	     
		     
intrinsic CreateModularCurveRec(N::RngIntElt, gens::SetEnum  : use_minimal_level:=true) -> Rec
 {
    Input:
	    N       : a postitive integer
	    gens    : a set of generators for a subgroup G of GL(2,Z/NZ)
    Output:  
        A record of type "ModularCurveRec" with the following entries computed: 
            N, gens, G, H, genus, v2, v3, vinf, sl2level, level, index, degree,  cusps, widths, regular, is_entangled, trdet. 
            
    Note: when N=1 only some of these entries are computed; Magma does not like matrices with entries in Z/(1).

    When "use_minimal_level" is true, we replace N with the level of G
 }


    if N ne 1 then
        level:=gl2Level( sub<GL(2,Integers(N))|gens> );    
    end if;
    if (N eq 1) or (level eq 1 and use_minimal_level) then        
        X:=rec<ModularCurveRec |  N:=1, gens:=[], genus:=0, v2:=1, v3:=1, sl2level:=1, level:=1, index:=1, degree:=1, vinf:=1, is_entangled:=false >;  
        return X;
    end if;
    if use_minimal_level then N:=level; end if;

    G:=sub<GL(2,Integers(N))|gens>;
    SL2:=SL(2,Integers(N));
    H:=SL2 meet G;

    is_entangled:= #G ne &*[ #ChangeRing(G,Integers(p^Valuation(N,p))) : p in PrimeDivisors(N) ];

    // To compute many of our quantities, there is no harm in adjoining -I to H.
    H0:=sub<SL2|Generators(H) join {SL2![-1,0,0,-1]}>;  
    sl2level:=sl2Level(H0);

    X:=rec<ModularCurveRec |  N:=N, gens:=gens, G:=G, H:=H, sl2level:=sl2level, level:=level, is_entangled:=is_entangled >;

    // We first find a set of representatives T of the cosets H0 \ SL2.
    // We construct the map  f: SL2 -> T  for which f(A) and A lie in the same coset.

    T,phi:=RightTransversal(SL2, H0);  
    psi:=map<T->[1..#T] | {<T[i],i>: i in [1..#T]} >;
    f:=phi*psi;  
    
    X`degree:=#T;  // The index of H0 in SL2.
    X`index:=Index(GL(2,Integers(N)),G); 

    // Compute the cusps and their widths
    B:=SL2![1,1,0,1];
    sigma:=Sym(#T)![f(t*B): t in T];   // permutation that describes how B acts on the set H0\SL2 via right multiplication  
    C:=CycleDecomposition(sigma);
    cusps0:=[Rep(c): c in C];
    cusps :=[T[i]: i in cusps0];  
    X`cusps:=cusps;   

    vinf:=#cusps; // number of cusps
    X`vinf:=vinf;

    X`widths:=[#c: c in C];  // Widths for group H0
    X`regular:= [ cusps[i]*(SL2![1,X`widths[i],0,1])*cusps[i]^(-1) in H : i in [1..vinf] ];
    for i in [1..vinf] do
        if X`regular[i] eq false then
            X`widths[i]:=2*X`widths[i];  // Want extra factor of 2 at irregular cusps
        end if;
    end for;    

    // Compute number of elliptic points of order 2
    B:=SL2![0,1,-1,0];
    C:=CycleDecomposition(Sym(#T)![f(t*B): t in T]);
    X`v2:=#[c: c in C | #c eq 1];

    // Compute number of elliptic points of order 3
    B:=SL2![0,-1,1,1];
    C:=CycleDecomposition(Sym(#T)![f(t*B): t in T]);
    X`v3:=#[c: c in C | #c eq 1];

    // Genus of X_H.   See Prop 1.40 of Shimura, "Introduction to the arithmetic theory of automorphic functions".
    X`genus:=Integers()!( 1 + X`degree/12 - X`v2/4 - X`v3/3 - vinf/2 );   
    
    X`trdet:= { [Trace(C[3]),Determinant(C[3])] : C in ConjugacyClasses(G) };

    return X;
end intrinsic;

intrinsic CreateModularCurveRec0(G::GrpMat : use_minimal_level:=true)  -> Rec
{Same as function "CreateModularCurveRec" except now the group is given directly}
    N:=#BaseRing(G);
    gens:=[Eltseq(a): a in Generators(G)];  

    return CreateModularCurveRec(N,gens : use_minimal_level:=use_minimal_level);    
end intrinsic;

intrinsic GL2Genus(G::GrpMat) -> RngIntElt
{Given a subgroup G of GL(2,Z/NZ) with N>1 return the genus of the modular curve X_G}
    M:=CreateModularCurveRec0(G);
    return M`genus;
end intrinsic;

intrinsic FindCuspPair(M::Rec,A::GrpMatElt) -> SeqEnum[RngIntElt], RngIntElt
{Consider a modular curve M=X_G given by a subgroup G of GL_2(Z/NZ).  
       Let H be the intersection of G with SL(2,Z/NZ).    

       Input:   a matrix A in SL(2,Z/NZ).
       Output:  a pair of integers [i,j] and an e in (1,-1) such that A and e*cusps[i]*[1,1;0,1]^j lie in the same coset H\SL(2,Z/NZ),
                    where cusps[i] is the fixed matrix describing the i-th cusp of M.   When G contains -I, we always return e=1.       
}

    // We search by brute force
    N:=M`N;  SL2:=SL(2,Integers(N));  H:=M`H;  cusps:=M`cusps;    
    B:=SL2![1,1,0,1];  A:=SL2!A;
    j:=0;  
    repeat 
        for i in [1..#cusps] do
            if cusps[i]*B^j*A^(-1) in H then
                return [i,j],1;
            elif -cusps[i]*B^j*A^(-1) in H then
                return [i,j],-1;
            end if;
        end for;
        j:=j+1;
    until false;
end intrinsic;

intrinsic EisensteinFormsWeight1(N::RngIntElt, prec::RngIntElt) -> SeqEnum
 {
    Input:
       N:    an integer > 2,
       prec: a positive integer.
    Output:
       An array E indexed by pairs [a,b] with a and b in Z/NZ.  
       The term of E indexed by [a,b] is 2N times the q-expansion of the Eisenstein series E_a,b^1 up to O(qN^(prec));
       it is given as a power series in qN:=q^(1/N) with coefficients in the cyclotomic field Q(zeta_N).

       For the definition of the Eisenstein series see section 2 of "Fourier expansion at cusps" by Brunault and Neururer.
       Remark: the extra factor of 2N ensures that all the coefficients are integral.
 }
    ZN:=Integers(N); 
    M:=RSpace(ZN,2); 
    K<z>:=CyclotomicField(N);
    OK:=RingOfIntegers(K); 
    zeta:=OK!z;
    R<qN>:=PowerSeriesRing(OK);
        
    E:=AssociativeArray(); 
    for alpha in M do       
        a:=alpha[1]; aa:=Integers()!a;
        b:=alpha[2]; bb:=Integers()!b;              
        e:=O(qN^(prec));
        for n in [1..(prec-1)] do
        for m in [1..(prec-1) div n] do
            if ZN!m eq a then 
                e:= e + zeta^( bb*n) * qN^(m*n);
            end if;
            if ZN!m eq -a then
                e:= e - zeta^(-bb*n) * qN^(m*n);                
            end if;
        end for;
        end for;
        e:=2*N*e;  // scale by factor of 2N
        // Add appropriate constant term.
        if a eq 0 and b ne 0 then  e:=e + OK!( N*(1+zeta^(bb))/(1-zeta^(bb)) ); end if;
        if a ne 0 then e:=e + N-2*aa; end if;
        E[M![a,b]]:=e;  
    end for;
    return E;
end intrinsic;

intrinsic ConvertModularFormExpansions(M::Rec, M0::Rec, gamma::SeqEnum[RngIntElt], F::SeqEnum : wt:=0) -> SeqEnum
 {
    Input:
        M, M0   : modular curves corresponding to X_G and X_G0, respectively, where G0 is a subgroup of GL(2,Z/N0) with full determinant.                  
        gamma   : a matrix in GL(2,Z/N0)        
        F       : a (weakly) modular form on X_G0; it is a sequence consisting of its q-expansion at the cusps of X_G0 (using M0`cusps).  
                  We assume the coefficients of the expansions are in Q(zeta_N0).                   
        wt      : the weight of F (though we only use the value of wt modulo 2).
    We assume that F*gamma is in fact a modular form on X_G.   

	Output: the modular form F*gamma of X_G given as a sequence of q-expansions at the cusps M`cusps.
    
    Note:   If the wrong "wt" is given, the resulting output might be -F*gamma instead.
 }
    N:=M`N;   
    N0:=M0`N; 

    if N0 ne 1 then
        gamma:=GL(2,Integers(N0))!gamma;  // We need only consider gamma modulo N0; we coerce if needed.   

        // By multiplying by a suitable element of G0, can always choose gamma in SL(2,Z/N0).
        d:=Determinant(gamma)^(-1);
        _:=exists(g0){g0: g0 in M0`G | Determinant(g0) eq d};
        gamma:=g0*gamma;
        gamma:=SL(2,Integers(N0))!gamma;
    end if;

    KN0<z0>:=CyclotomicField(N0);
    R0<qN0>:=LaurentSeriesRing(KN0);

    // The follow code finds a cyclotomic field containing the coefficients of the q-expansions of F.
    // In our applications, it will always produce KN0=Q(zeta_N0). 
    N1:=N0;
    for f in F do
        flag,N1_:=IsRootOfUnity(  BaseRing(Parent(f)).1  );
        assert flag;
        N1:=LCM([N1,N1_]);
    end for;
    for d in Sort(Divisors(N1 div N0)) do
            N1_:=N0*d;
            KN0<z1>:=CyclotomicField(N1_);
            if &and[&and[a in KN0: a in Coefficients(f)]: f in F] then
                R0<qN0>:=LaurentSeriesRing(KN0);
                break d; 
            end if;
    end for;
    
    if M`N eq 1 then M`cusps:=[ SL(2,Integers(N0))![1,0,0,1] ]; end if;  // set cusp in the j-line special case

    F_:=[];
    z:=z1^(N1_ div N0);  // N0-th root of unity
    for e in [1..#M`cusps] do
        if N0 ne 1 then                
            A0:=SL(2,Integers(N0))!LiftMatrix(M`cusps[e],1);
            A:=gamma * A0;
            a,sgn:=FindCuspPair(M0,A);
            i:=a[1]; j:=a[2];
        else
		    i:=1; j:=0; sgn:=1;
	    end if;
        f:= R0!F[i];              
        f:=sgn^wt * Evaluate( f, z^j*qN0 );
	    F_:=F_ cat [f];      
    end for;

    // F_ is the desired sequence of q-expansions, but they have coefficients in Q(zeta_N0)
    // and have variable q_N0:=q^(1/N0).   We now express them in terms of N and not N0.
    
    KN<z>:=CyclotomicField(N);
    R1<qN0>:=LaurentSeriesRing(KN);
    F_:=[R1!f : f in F_];

    R2<qN>:=LaurentSeriesRing(KN);
    Fnew:=[];
    for f in F_ do
        c,s,i:=Coefficients(f); assert i eq 1;
        f1:=&+( [c[i+1]*qN^((N*(s+i)) div N0): i in [0..#c-1]] cat [O(qN^(Floor( N/N0*AbsolutePrecision(f)) ))] );
        Fnew:=Fnew cat [f1];
    end for;

    return Fnew;
end intrinsic;

intrinsic SimplifyModularFormBasis(M::Rec,F::SeqEnum) -> SeqEnum
{  Input:
            M:  modular curve corresponding to X_G where G is a subgroup of GL(2,Z/N) with full determinant. 
            F:  a sequence of Q-linearly indepdendent modular forms in M_k,G for some k>1

        Output:
            A sequence consiting of another basis of the Q-span of F.   We apply a saturation and the 
            LLL algorithm to try to find a basis with "nicer looking" q-expansions.
}
    K<z>:=CyclotomicField(M`N);
    R<qN>:=LaurentSeriesRing(K);
    F:=[[R!g: g in f] : f in F];  // coerce

    // strip coefficients of modular forms and put in a matrix C
    C:=[ [] : f in F];
    for j in [1..M`vinf] do
        h:=[ f[j] : f in F];               
        while &or[IsWeaklyZero(f): f in h] eq false do
            v:=Minimum([Valuation(f):f in h]);
            for i in [1..#F] do
                c:=K!Coefficient(h[i],v);
                C[i]:=C[i] cat Eltseq(c);
                h[i]:=h[i]-c*qN^v;
            end for;
        end while;
    end for;
    C:=Matrix(C);

    // scale so that C has integer entries
    d:=LCM({Denominator(C[i,j]) : i in [1..Nrows(C)], j in [1..Ncols(C)]});
    C:=d*C;
    C:=ChangeRing(Matrix(C),Integers());

    CC:=LLL(Saturation(C));
    B:=Solution(ChangeRing(C,Rationals()),ChangeRing(CC,Rationals())); 
    B:=B * LCM([Denominator(B[i,j]): i in [1..Nrows(B)], j in [1..Ncols(B)]]); // scale to integer entries
    
    FF:=[ [ &+[b[i]*F[i][j]: i in [1..#F]]  :  j in [1..M`vinf] ]  :  b in Rows(B)];        

    return FF;
end intrinsic;

intrinsic FindModularForms(k::RngIntElt, M::Rec, prec::RngIntElt) -> Rec 
 {
    Input   k:      an integer > 1,
            M:      a record M type "ModularCurveRec" (for example produced as output of CreateModularCurveRec) associated to a group G 
                    of GL(2,Z/NZ) for some N>1.
            prec:   a positive integer value; all q-expansions will be computed at least up to O(qN^prec).
    Output:
            This function computes a basis for the Q-vector space of modular forms M_k,G=M_k(Gamma(N),Q(zeta_N))^G.   More precisely,
            M is returned with the following entries computed (see the description of the record ModularCurveRec for details):
                k, dimMk, dimSk, sturm, prec, F
    Remark: This function was designed to work well (and tested) in the case where det(G)=(Z/NZ)^*.  Further optimizations are certainly possible in other cases.    
 } 
    M`k:=k; 
    N:=M`N;
    M`mult := [ 0 : i in [1..M`vinf]];
    error if N eq 1, "FindModularForms not implemented when N=1.";  // This case can be easily handled by Magma's current functions since we have only one cusp
 
    GL2:=GL(2,Integers(N));
    SL2:=SL(2,Integers(N));    
    G:=M`G;
    H:=M`H;

    // Our method for producing modular forms requires N>2.  
    // In these excluded cases, we lift G to a group in GL(2,Z/4Z) and then do the computation.
    // There are better ways to do this (and when N=1, we should use built in Magma functions!)
    if N le 2 then          
        if N eq 1 then
            G_:=GL(2,Integers(4));
        else
            G_:=gl2Lift(M`G,4);
        end if;
        M0:=CreateModularCurveRec0(G_: use_minimal_level:=false); 
        M0:=FindModularForms(k,M0,(4 div N)*prec);
        
        M`F:=[ConvertModularFormExpansions(M, M0, [1,0,0,1], f : wt:=k) : f in M0`F];
        M`k:=k;
        M`dimMk:=M0`dimMk; 
        M`dimSk:=M0`dimSk;
        M`prec:=prec; 
        M`sturm:=M0`sturm;        
        return M;
    end if;
    
    //cusps and widths
    cusps:=M`cusps;
    widths:=M`widths;
    vinf:=M`vinf;

    // We first compute the dimensions of M_k(Gamma_G) and S_k(Gamma_G) over C.
    if k eq 2 then
        d:=M`genus+vinf-1;  // Shimura Theorem 2.23
        d0:=M`genus;
    elif IsEven(k) then
        d:=(k-1)*(M`genus-1) + (k/2)*vinf + M`v2*Floor(k/4) + M`v3*Floor(k/3);
        d0:=(k-1)*(M`genus-1) + (k/2-1)*vinf + M`v2*Floor(k/4) + M`v3*Floor(k/3);
    elif SL2![-1,0,0,-1] in H then
        d:=0; d0:=0;
    else
        u:=#{i: i in [1..#M`regular]| M`regular[i]};  u_:=#M`regular-u;
        d:=(k-1)*(M`genus-1)+(k/2)*u +(k-1)/2*u_ + M`v2*Floor(k/4) + M`v3*Floor(k/3);
        d0:=(k-1)*(M`genus-1)+((k-2)/2)*u +(k-1)/2*u_ + M`v2*Floor(k/4) + M`v3*Floor(k/3);
    end if;
    M`dimMk:=d; 
    M`dimSk:=d0;

    // We now compute a "Sturm bound".  
    if IsEven(k) then
        M`sturm:=k/2*(2*M`genus-2)+M`v2*Floor(k/4)+M`v3*Floor(k/3)+ k/2*vinf;
    else
        M`sturm:=k/2*(2*M`genus-2)+M`v2*Floor(k/2)/2+M`v3*Floor(2*k/3)/2+ k/2*vinf;  
    end if;
    
    // When M_{k,G} = 0, there is nothing to compute.
    if M`dimMk eq 0 then      
        M`F:=[]; M`prec:=1;
        return M;
    end if;

    // We will compute q-expansions at the cusps up to O(qN^(Prec)), with Prec chosen large enough to distinguish elements of M_k(Gamma_G).    
    b0:=N*(M`sturm)/M`degree; 
    Prec :=Ceiling(b0);  if Prec eq b0 then Prec:=Prec+1; end if;
    Prec:=Maximum(Prec,prec);   // make precision larger if desired by user parameter "prec".
    M`prec:=Prec;

    // N-th cyclotomic field Q(zeta_N) and its ring of integers Z[zeta_N]
    KN<z>:=CyclotomicField(N);   
    OK:=RingOfIntegers(KN);   
    zeta:=OK!z;

    R<qN>:=PowerSeriesRing(OK);

    U_,f_:=UnitGroup(Integers(N));  
    f_:=Inverse(f_);   
    detG:=#sub<U_|{f_(Integers(N)!Determinant(g)): g in Generators(G)}>;
    degL := EulerPhi(N) div detG;   
    d:= degL * M`dimMk;   //The dimension of M_{k,G} as a Q-vector space.  Equals M`dimMk when det(G)=(Z/N)^*.

    /*
        We finally start constructing modular forms!

        Consider an element a=(a_1,...,a_k) in (Z/NZ)^(2k) = ((Z/NZ)^2)^k and an integer j. 
 
        To a and j, we construct a modular form f_{a, j} in M_{k,G}:=M_k(Gamma(N),Q(zetaN))^G as follows:
            sum the functions  
                        zeta_N^(j*det(g)) * E[a_1*g]*...*E[a_k*g], 
            where g varies over elements of G.  When computing them, it is useful to first compute the sum over elements of a 
            fixed H-coset.   Such modular forms will in fact span M_k(Gamma(N),Q(zeta_N))^G.   
            We also want all a_i to be nonzero since otherwise the function obtained will be 0.
   
        We will compute modular forms f_{a,j} until they span M_{k,G}; they will be encoded by a matrix "B".
    */    

    // Compute Eisenstein series of weight 1 and level N.     
    E:=EisensteinFormsWeight1(N, Prec);   

    // Coset representatives of G/H and their determinants.
    R:=Transversal(G,H);    
    detR:=[Integers()!Determinant(A): A in R]; 

    ConjH:=[Conjugate(H, A) :  A in cusps];     // Groups A^(-1)*H*A with A running over matrices in cusps.
    if SL2![-1,0,0,-1] in H then e:=-1; else e:=1; end if;
    U:=[sub<SL2| [[e,0,0,e], [1,M`widths[i],0,1]]> : i in [1..#cusps]];   // U[i] is a subgroup of ConjH[i]
    RR:=[ [a^(-1): a in Transversal(ConjH[i],U[i])] : i in [1..#cusps] ];  // RR[i] is a set of representatives of the cosets ConjH[i]/U[i].

    MM:=RSpace(Integers(),EulerPhi(N)*Prec*#cusps);   
    W:=sub<MM| MM!0>;  // module that will encode the modular forms found so far
    r:=0;  // Number of linearly independent modular forms found so far.    
    B:=[];  // Will be matrix whose entries encode the coefficients of modular form in our basis.
    S:={};  // The set of a's we have already tried

    while r lt d do   // Repeat until we found a basis of M_{k,G}.

        // Choose a random "a"
        a:=random{a: a in RSpace(Integers(N),2*k) | a notin S and &and[ a[2*i-1] ne 0 or a[2*i] ne 0 : i in [1..k] ] };            
        S:=S join {a};
        a:=[ RSpace(Integers(N),2)![a[2*i-1],a[2*i]] : i in [1..k] ];
                
        f_inner:=[];
        for i in [1..#cusps] do
            f0:=[];
            for g in R do
                f:=&+[ &*[E[a[e]*g*cusps[i]*h]:e in [1..k]] : h in RR[i]  ];
                e:=N div M`widths[i]; 
                f:=#U[i] * &+[Coefficient(f,e*j)*qN^(e*j) : j in [0..(Prec-1) div e]] + O(qN^Prec);
                f0:= f0 cat [f];
            end for;
            f_inner:=f_inner cat [f0];        
        end for;
    
        if not &and[ IsWeaklyZero(f) : f in &cat f_inner] then            
            for j in [0..Index(G,H)-1] do
                ff:=[ &+[zeta^(detR[e]*j) * f_inner[i][e]: e in [1..#R] ]  : i in [1..#cusps] ];
                m:=MM! &cat[ &cat[ Eltseq(Coefficient(ff[e],i)): i in [0..Prec-1]] : e in [1..#cusps] ];

                W_:=sub<MM|Basis(W) cat [m]>;
                r_:=Rank(W_);
                if r_ gt r then  // We found a new modular form!
                    B:=B cat [m];
                    W:=W_;  
                    r:=r_;                                                
                end if;

                if r eq d then break j; end if;  
            end for;
        end if;

    end while;
    assert r eq d;  // Check! We should have found enough modular forms.
  
    // Construct a simpler basis by taking saturation and using the LLL algorithm.
    B:=Matrix(B);    
    B:=LLL(Saturation(B));      

    // Give the matrix B, we now convert its rows into modular forms given by the q-expansions at all the cusps.
    RR<qN>:=PowerSeriesRing(KN);
    FF:=[];
    for b0 in Rows(B) do
        b:=Eltseq(b0); 
        ff:=[];
        for e in [1..#cusps] do
            f:= O(qN^Prec);
            for i in [0..Prec-1] do
                f:= f + &+[b[j]*zeta^(j-1): j in [1..EulerPhi(N)] ] * qN^i;
                b:=[b[i]: i in [EulerPhi(N)+1..#b]];
            end for;
            ff:=ff cat [f];
        end for;
        FF:=FF cat [ff];
    end for;
    FF:=[[RR!f:f in ff]: ff in FF];
    
    // We can slightly improve the precision of our modular forms by taking weights into account.    
    FF0:=[];
    for f in FF do
        f0:=[];
        for j in [1..#M`cusps] do
            e:=AbsolutePrecision(f[j]);
            e1:=N div M`widths[j];
            e2:=Ceiling(e/e1)*e1;
            f0:=f0 cat [ChangePrecision(f[j], e2)];
        end for;
        FF0:=FF0 cat [f0];
    end for;
    FF:=FF0;
    
    M`F:=FF;
    return M;
end intrinsic;

intrinsic FindModularFormsWithVanishingConditions(M::Rec,mult::SeqEnum[RngIntElt]) -> Rec
 { Input:  
        M    : a record of type "ModularCurveRec" with a Q-basis M`F of M_k,G already computed.
        mult : is a sequence of nonnegative integers of the same length as cusps:=M`cusps

    Let V be the Q-subspace of M_k,G consisting of modular forms so that the vanishing of f at 
    the cusp  cusps[i]*infty is at least mult[i] for all i.   

    Output: return the record M with the entry M`F0 a basis of the Q-vector space V
            (with the same conventions/precision as the basis M`F of M_k,G)
 } 
    N:=M`N;
    cusps:=M`cusps;
    widths:=M`widths;
    M`mult := mult;

     
    error if &or[m lt 0: m in mult], "Multiplicities need to be positive."; 
    if &and[m eq 0: m in mult] or #M`F eq 0 then M`F0:=M`F; return M; end if;  // nothing to compute

    // We now check that enough terms of the q-expansions are computed to impose the vanishing.
    error if  &or[ mult[i]/widths[i] ge M`prec/N : i in [1..#mult] ],  "Need more terms of q-expansion to impose vanishing conditions.";

    // We now construct a Q-basis FF of V.
    C:=[];
    for f in M`F do        
        c:=&cat[ &cat[Eltseq( Coefficient(f[i],j*(N div widths[i])) ) : j in [0..mult[i]-1]] : i in [1..#cusps] ];
        C:=C cat [c];
    end for;
    C:=ChangeRing(Matrix(C),Integers());
    B:=Basis(Kernel(C));
    if #B eq 0 then M`F0:=[];  return M; end if;  // if V=0, we are done.
    d:=#M`F;
    FF:=[];
    for b in B do
        FF:= FF cat [ [&+[b[j]*M`F[j][i]: j in [1..d]]: i in [1..#cusps]] ];
    end for;

    //  The following tries to make the basis look nicer using the LLL algorithm.
    b0:=N*(M`sturm)/M`degree;
    Prec:=Ceiling(b0); if Prec eq b0 then Prec:=Prec+1; end if;
    Prec:= Minimum(Prec,M`prec);
    m:=[ Floor(widths[i]*(Prec-1)/N) : i in [1..#cusps] ];
    C:=[];
    for f in FF do        
        c:=&cat[ &cat[Eltseq( Coefficient(f[i],j*(N div widths[i])) ) : j in [0..m[i]]] : i in [1..#cusps] ];
        C:=C cat [c];
    end for;
    C:=ChangeRing(Matrix(C),Integers());
    CC:=LLL(Saturation(C));
    B:=Solution(ChangeRing(C,Rationals()),ChangeRing(CC,Rationals())); 
    B:=B * LCM([Denominator(B[i,j]): i in [1..Nrows(B)], j in [1..Ncols(B)]]); // scale to integer entries

    FF:=[ [ &+[b[i]*FF[i][e]: i in [1..Ncols(B)]]  :  e in [1..#cusps] ]  :  b in Rows(B)];

    M`F0:=FF;
    return M;
end intrinsic;

intrinsic FindCuspForms(M::rec) -> rec 
{Applies "FindModularFormsWithVanishingConditions" with mult:=[1,1,...,1].}
    return FindModularFormsWithVanishingConditions(M,[1: i in [1..#M`cusps]]);
end intrinsic;

intrinsic EvaluateAtMonomialsOfDegree(F::SeqEnum, d::RngIntElt) -> SeqEnum
{  Input 
            F : a sequence of n>0 elements in some ring
            d : a positive integer.
        Output:
            An array A such that for nonnegative integers e_1,..,e_n that sum to d,
            A[[e_1,..,e_d]] is the product of F[i]^(e_i).

        This function could be greatly improved but it is better than the most naive implementation.
}
    assert #F ne 0;
    A:=AssociativeArray();
    B:=AssociativeArray();
    B[[]]:= Parent(F[1])!1;
    for i in [1..#F] do
        // Compute F[i]^j with j from 0 to d
        v:=[Parent(F[i])!1];  for j in [1..d] do v := v cat [v[#v]*F[i]]; end for; 
        B0:=AssociativeArray();
        for k in Keys(B) do
            d0:=&+(k cat [0]);
            if i lt #F then
                for j in [0..(d-d0)] do
                    B0[k cat [j]]:= B[k] * v[j+1];
                end for;
            end if;
            if i eq #F then
                A[k cat [d-d0]]:= B[k] * v[d-d0+1];
            end if;
        end for;
        B:=B0;
    end for;
    return A;
end intrinsic;

intrinsic FindRelations(F::SeqEnum, d::RngIntElt) -> SeqEnum
{
    Input:   
        F:  a finite sequence of modular forms  (each modular form is given as a sequence of q-expansions 
            corresponding to the different cusps of the underlying modular curve). 
            We further assume all the q-expansions have coefficients in some Z[zeta_N].
        d:  a positive integer

    We have F=[f_1,..,f_n].  Let V be the Q-vector space consisting of homomogeneous polynomials P in Q[x_1,..,x_n]
    of degree d such that P(f_1,..,f_n)=0.

    Output: a Q-basis of V.

    (Warning: if not enough terms of the q-expansions are given, then V may be larger than expected.)
}

    if #F eq 0 then return []; end if;
    n:=#F;    
    v:=#F[1];// number of cusps!
    Pol<[x]>:=PolynomialRing(Rationals(),n);
    
    A:=EvaluateAtMonomialsOfDegree([f[1]: f in F],d);
    
    mon:=Sort([a: a in Keys(A) | &+a eq d]); // same for any i
    B:=[ [] : j in [1..#mon] ];

    for i in [1..v] do
        A:=EvaluateAtMonomialsOfDegree([f[i]: f in F],d);
        mon:=Sort([a: a in Keys(A) | &+a eq d]); 
        m:=Minimum([AbsolutePrecision(f[i]): f in F]);
        C:=[A[a]: a in mon];
        for j in [1..#mon] do
            B[j]:=B[j] cat &cat[Eltseq(Coefficient(C[j],n)): n in [1..m-1]];
        end for;            
    end for;
    B:=ChangeRing(Matrix(B),Integers());
    L:=Kernel(B); 

    L:=Matrix(Basis(L)); 
    L:=LLL(Saturation(L));  // Use LLL algorithm to find a nicer looking basis

    mon:=[ &*[x[i]^a[i]:i in [1..n]] : a in mon ];
    psi:=[ &+[L[i,j]*mon[j]: j in [1..#mon]] : i in [1..Nrows(L)] ];
    return psi;
end intrinsic;

intrinsic FindCanonicalModel(M::Rec, prec::RngIntElt) -> BoolElt, SeqEnum, SeqEnum
{  Input:       
                M: a record M type "ModularCurveRec" (for example produced as output of CreateModularCurveRec) that 
                   corresponds to a modular curve X_G with genus g at least 3.
                prec: a positive integer

        The integer "prec" is used in the computation of modular forms.  A larger value will result in more terms of the q-expansion
        being computed.        

        Output:            
                - a boolean "flag"
                - a sequence "psi" of homogeneous polynomials in Q[x_1,..,x_g].
                - a sequence F of g modular forms that give a Q-basis for the subspace of cusps forms in M_k,G.
                
            The sequence F defines the canonical map X_G -> P^(g-1)_Q; the image is a curve C which is defined by the equations psi.
            If the boolean "flag" is true, then the canonical map is an embedding and the output is correct.
            If the boolean "flag" is false, then the canonical map is probably not an embedding (i.e., X_G is probably hyperelliptic);
            the output will be correct assuming "prec" is large enough but the function does not prove this.
}  
    g:=M`genus;
    error if g lt 3, "Curve must have genus at least 3";

    // Compute modular forms of weight 2 if needed. 
    if (not assigned M`k or M`k ne 2) or M`prec lt prec then
        M:=FindModularForms(2,M,prec);
    end if;

    // Now compute cusps forms of weight 2.
    M:=FindCuspForms(M);
    F:=M`F0; 
    assert #F eq g; 

    Pol<[x]>:=PolynomialRing(Rationals(),g);
    PP:=ProjectiveSpace(Rationals(),g-1);

    I2:=FindRelations(F,2);
    I2:=[Pol!P: P in I2];
    error if #I2 notin {(g-1)*(g-2) div 2,((g-2)*(g-3)) div 2}, "Incorrect number of quadratic relations; need more terms in q-expansion";
    Q0:=Scheme(PP,I2);   
    dimQ0:=Dimension(Q0);
    error if dimQ0 lt 1, "Incorrect quadratic relations; need more terms in q-expansion";

    if  #I2 eq (g-1)*(g-2) div 2 then 
        // Curve is probably hyperelliptic; if so, Q0 is a curve of genus 0 (we now check this)
        error if dimQ0 gt 1, "Incorrect quadratic relations; need more terms in q-expansion";
        Q0:=Curve(PP,I2);
        error if Genus(Q0) ne 0, "Incorrect quadratic relations; need more terms in q-expansion";        
        return false, I2, F; 
    end if;

    if dimQ0 eq 1 then
        // canonical curve is probably not hyperelliptic and is cut out by quadratic polynomials.
        return true, I2, F;
    end if;

    if g eq 3 then
        I4:=FindRelations(F,4); 
        error if #I4 gt 1, "Too many relations; need more terms in q-expansion";
        f:=I4[1];
        
        // We have a model of X_G as a plane quartic with integer coefficients given by f=0.
        // We can use a built in Magma function to choose a nicer f.

        PZ<[x]>:=PolynomialRing(Integers(),#F);
        f,A:=MinimizeReducePlaneQuartic(PZ!f);       
        A:=ChangeRing(A,Rationals())^(-1);
        F:=[ [&+[A[e,j]*F[j][i]: j in [1..3]]: i in [1..#M`cusps]] : e in [1..3] ];
        return true, [f], F; 
    end if;

    // We are now in the case where X_G has genus at least 4 and is trigonal or isomorphic to a plane quintic (g=6). 

    mon3:=[m: m in MonomialsOfWeightedDegree(Pol,3)];
    V:=VectorSpace(Rationals(),#mon3);

    W:=sub<V| [V![MonomialCoefficient(x[i]*f,m): m in mon3] : i in [1..g], f in I2]>;
    assert Dimension(W) eq ((g-3)*(g^2+6*g-10) div 6) - (g-3);

    I3:=FindRelations(F,3); 
    I3:=[Pol!P: P in I3];

    Q0:=Scheme(PP,I2 cat I3);   
    dimQ0:=Dimension(Q0);
    error if dimQ0 lt 1, "Incorrect cubic relations; need more terms in q-expansion";

    V3:=sub<V| [V![MonomialCoefficient(f,m): m in mon3] : f in I3]>;
    J:=[];
    i:=1;
    while Dimension(W) lt Dimension(V3) do
        v:=V![MonomialCoefficient(I3[i],m): m in mon3];
        if v notin W then 
            W:=sub<V|Generators(W) join {v}>; 
            J:=J cat [I3[i]];
        end if;
        i:=i+1;
    end while;
    psi:=I2 cat J;

    return true, psi, F; 
end intrinsic;

intrinsic FindModelOfXG(M::Rec, prec::RngIntElt : compute_all:=true, G0:=1) -> Rec
{  Input:       
                M:      a record of type "ModularCurveRec" (for example produced as output of CreateModularCurveRec) that 
                        corresponds to a modular curve X_G.    We assume G has full determinant and contains -I.
                prec:   a nonnegative integer.   The integer "prec" is used in the computation of modular forms.  A larger value will result in more terms of the 
                        q-expansion being computed.  
        Output: 
                M is returned with the follow entries computed:        
                    F0:  a sequence of n modular forms, in M_k,G for some even k, so that the morphism 
                         X_G -> P^(n-1) described by F0 is defined over Q and gives an isomorphism between 
                         X_G and a smooth projective curve X in P^(n-1)_Q.
                    psi: homogeneous polynomials in Q[x_1,..x_n] defining the curve X mentioned above.
                    
                If X_G has genus 0 or X_G has genus 1 and n le 5, we also compute
                    has_point:  true if and only if X_G has a Q-point.
                    has_infinitely_many_points:  true if and only if X_G has infinitely many Q-points

                If X_G has genus 0 and has a Q-point, we also compute
                    f:  a generators of the function field of X_G, i.e., Q(X_G)=Q(f); it is given by q-expansions 
                        at the cusps
                    C:  the curve P^1_Q (note that f defines an isomorphism between X_G and C)

                If X_G has genus 1, n le 5, and X_G has a Q-point, we also compute
                    f=[x,y]:  we have Q(X_G)=Q(x,y), where x and y satisfy a Weierstrass equation; they
                              are given by q-expansions at the cusps.
                    C:  an elliptic curve over Q given by the Weierstrass equation that x and y satisfy.

                When X_G has genus at most 1 and we have found a point, we also compute
                    phiC:  a sequence of polynomials that defines an isomorphism X->C      

        If desired, the parameter G0 can be set to be a subgroup of GL(2,Z/N) so that G=M`G is a normal subgroup.  We then
        choose F0 so that the Q-vector space they span is acted on by G0.   This makes it easy to compute the automorphisms
        of our curve coming from G0/G.
}

    // The j-line can be dealt with directly
    if M`degree eq 1 then
        M`has_point:=true;
        M`has_infinitely_many_points:=true;
        P1<x,y>:=Curve(ProjectiveSpace(Rationals(),1));
        M`C:=P1;
        R<q>:=LaurentSeriesRing(Rationals());
        M`f:=[jInvariant(q+O(q^Maximum(prec,120)))];  
        return M;
    end if;

    // If the genus is at least 3, we first try to compute the image of the canonical map.  This will give a model
    // of the curve X_G if it is not hyperelliptic.
    if M`genus ge 3 then
        flag, psi, F:= FindCanonicalModel(M, prec);
        if flag then
            M`k:=2;
            M`F0:=F;
            M`psi:=psi;  
            M`has_infinitely_many_points:=false;  // by Faltings
            M`mult := [ 1 : i in [1..M`vinf]];
            return M;
        end if;
    end if;

    //  We increase our even weight k until Riemann-Roch guarantees an embedding of XG using M_{k,G}.
    k:=0;
    repeat
        k:=k+2;
        degD:= (k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps;
    until degD ge 2*M`genus+1;
    print "Using weight ",k," with precision ",prec;

    // Compute modular forms of weight k.
    M:=FindModularForms(k,M,prec);  
    cusps:=M`cusps;

    N:=M`N;
    GL2:=GL(2,Integers(N)); 
    SL2:=SL(2,Integers(N)); 
    G:=M`G;

    if Type(G0) ne GrpMat then
        G0:=G;  // If not set by user ahead of time
    else
        N0:=gl2Level(G0); 
        assert N mod N0 eq 0;
        G0:=ChangeRing(G0,Integers(N0));
        G0:=gl2Lift(G0,N);
        assert G subset G0;
        assert IsNormal(G0,G);
    end if;

    // Since k is even, we may assume that G and G0 contains -I (this should be assumed anyway)
    if GL2![-1,0,0,-1] notin G  then  G :=sub<GL2|Generators(G)  join {GL2![-1,0,0,-1]}>;  end if;
    if GL2![-1,0,0,-1] notin G0 then  G0:=sub<GL2|Generators(G0) join {GL2![-1,0,0,-1]}>;  end if;

    
    // Computes the action of (Z/NZ)^* on the cusps of X_G.  This corresponds to the action of Gal(Q(zeta_N)/Q) on the cusps.
    U,pi:=UnitGroup(Integers(N));
    s:={};
    for u in Generators(U) do
        d:=Integers(N)!pi(u);
        b:=GL2![1,0,0,d];
        flag:=exists(g){g: g in G | Determinant(g) eq d};
        error if not flag, "Group G should have full determinant.";
        sigma:=[FindCuspPair(M,SL2!(g^(-1)*GL2!cusps[i]*b))[1]: i in [1..#M`cusps]];
        s:=s join {sigma};
    end for;
    // Let H and H0 be the intersection of G and G0, respectively, with SL(2,Z/N).  We now computes the action of H0/H on the cusps of X_G.
    H0:=G0 meet SL(2,Integers(N));
    Q,iotaQ:=quo<H0|M`H>;
    for g_ in Generators(Q) do
        g:= g_ @@ iotaQ;
        sigma:=[FindCuspPair(M,SL2!(g^(-1)*SL2!cusps[i]))[1]: i in [1..#M`cusps]];
        s:=s join {sigma};
    end for;

    S:=sub<SymmetricGroup(#M`cusps)|s>;
    ind:=[[i:i in O]: O in Orbits(S)];  // orbits of cusps under the actions of G0 and Gal_Q.

    // We now compute a sequence "mult" of nonnegative integers that give the vanishing conditions 
    // we want to impose at the cusps.  It is chosen so the integers depend only on the Galois orbit of the cusps
    // and so that the degree of the the corresponding sheaf is at least 2*genus+1.   We try to choose our
    // integers so that the degree is minimal and so that we do not have to compute too many terms of the
    // q-expansions.

    lhs:=[[#ind[i]: i in [1..#ind]]];
    rhs:=[[degD - (2*M`genus+1)]];
    rel:=[[-1]];
    v0:=[0: i in [1..#ind]];
    for i in [1..#ind] do
        m:=Minimum([ Floor( M`prec*M`widths[j]/N ) : j in ind[i]]);
        if m*N eq Minimum([ M`prec*M`widths[j] : j in ind[i]]) then m:=m-1; end if;
        v:=v0; v[i]:=1;
        lhs:=lhs cat [v];
        rhs:=rhs cat [[m]];
        rel:=rel cat [[-1]];
    end for;
    lhs:=Matrix(lhs);   
    rhs:=Matrix(rhs); 
    rel:=Matrix(rel); 
    obj:=Matrix([[#ind[i]: i in [1..#ind]]]);
    a:=MaximalSolution(lhs,rel,rhs,obj); 
    mult:=[ a[1][ [j: j in [1..#ind] | i in ind[j]][1] ] : i in [1..#cusps] ];  
    
    // We now impose vanishing conditions;  M`F0 will give the basis of modular forms that satisfy the conditions.
    M:=FindModularFormsWithVanishingConditions(M,mult);    
    F:=M`F0;
    
    // Our model will lie in the following projective space.    
    PP:=ProjectiveSpace(Rationals(),#F-1);
    Pol<[x]>:=PolynomialRing(Rationals(),#F);

    // We now find a model.    We first look at quadratic relations.
    psi2:=[Pol!f: f in FindRelations(F,2)];
    X0:=Scheme(PP,psi2);
    dim0:=Dimension(X0);

    if dim0 lt 1 then 
        // Too many equations for model; need more terms of q-expansions to rule out more polynomials
        return FindModelOfXG(M, prec+15 :  compute_all:=compute_all, G0:=G0);  // try again with more precision!
    end if;

    deg:= degD - &+mult;
    assert deg ge 2*M`genus+1;

    if deg ge 2*M`genus+2 then 
        // In this case, we know our curve will be cut out by quadratics.
        psi:=psi2;
        X:=Curve(X0);
    else
        // Need to also consider cubic relations.
        psi3:=[Pol!f: f in FindRelations(F,3)];
        X1:=Scheme(PP,psi3);
        dim1:=Dimension(X1);

        // Too many equations for model; need more terms of q-expansions to rule out more polynomials.
        if dim1 lt 1 then 
            return FindModelOfXG(M, prec+20 :  compute_all:=compute_all, G0:=G0);  // try again with more precision!
        end if;

        assert dim1 eq 1;
        if dim0 eq 1 and IsIrreducible(X0) then 
            psi:=psi2; 
            X:=Curve(X0); 
        else 
            psi:=psi3; 
            X:=Curve(X1); 
        end if;
    end if;

    M`F0:=F;
    M`psi:=psi;

    if M`genus ge 2 then
        M`has_infinitely_many_points:=false; //By Faltings
        return M;
    end if;

    // GENUS 0
    // When the curve has genus 0, we can check whether it is isomorphic to P^1_Q.
    if M`genus eq 0 then
        C1,f1:= Conic(X);        
        b,p1:=HasRationalPoint(C1);
        M`has_point:=b;
        M`has_infinitely_many_points:=b;

        if M`has_point then
            // The modular curve is isomorphic to P^1_Q
            P1<x,y>:=Curve(ProjectiveSpace(Rationals(),1));
            f2:=Parametrization(C1,P1);    // f2: P1->C1
            phi:=Expand(f2*Inverse(f1));   // isomorphism P1->X 

            W:=DefiningEquations(Inverse(phi));
            W:=[Pol!w: w in W];
		
            // We compute a hauptmodul, i.e., a function f that generates the function field of the modular curve over Q.
            ff:=[];
            for j in [1..#M`cusps] do 
		        a:=[f[j]: f in F];
	        	hh:=[Evaluate(w,a): w in W];
                if IsWeaklyZero(hh[2]) then                
                    return FindModelOfXG(M, prec+10 : compute_all:=compute_all, G0:=G0);  // start over with more precision
                end if;
		        h:=hh[1]/hh[2];
	        	ff:=ff cat [h];                
	        end for;
            M`f:=ff; 
            M`C:=P1;    

            //M`phiC:=W;        
        end if;
        return M;
    end if;

    // GENUS 1
    // When the curve has genus 1, we can try to check whether it has rational points or not,
    if M`genus eq 1 then
            
        pts:=PointSearch(X,1000);  // look for points of low height first
        if #pts ne 0 then
            _,i:=Minimum([HeightOnAmbient(P): P in pts]);
            P0:=pts[i];
            M`has_point:=true;
        end if;

        if not assigned M`has_point then
            n:=#F;
            if n ge 6 then 
                // Magma can only recongnize genus one curves of degree at most 5.
                return M;
            end if;
            assert Degree(X) eq n and n le 5; 

            // When n is at most 5, Magma has functionality to work with the model of our genus 1 modular curve.
            C:=GenusOneModel(X); 
            if not IsLocallySoluble(C) then
                M`has_point:=false;
                M`has_infinitely_many_points:=false;
                return M;
            end if;

		    C1,E,maptoE:=nCovering(C); 
            // This is a degree n^2 cover C->E and E is isomorphic to the Jacobian of C; 
            // it is a twist of multiplication by n map E->E.
            // In particular, if C has a rational point, then the image of C(Q) in E will be a coset of nE(Q).

		    A,f:=MordellWeilGroup(E);
		    r:=TorsionFreeRank(A);

		    if r eq 0 then
			    // C has finitely many points which we can find
		        pts:={};
    		    for a in A do 
    			    preimage := Pullback(maptoE, f(a));
        		    pts:=pts join {p: p in Points(preimage)};
		        end for;
                M`has_point:=#pts ge 1;
	        else
			    // Curve has either infinitely many points or no points.
		        Q,iota:=quo<A|{n*a: a in Generators(A)}>;
		        pts:={};
		        for q in Q do
				    P:=f(q @@ iota);
			        preimage := Pullback(maptoE, P);
			        pts:=pts join {p: p in Points(preimage)};
			        if #pts ge 1 then break q; end if;
		        end for;                    
        	    M`has_point:=#pts ge 1;
		    end if;

            if M`has_point eq false then return M; end if;

            assert #pts ne 0;
            pts:=[P:P in pts];            
            _,i:=Minimum([HeightOnAmbient(P): P in pts]);


            p0:=Eltseq(pts[i]);         
            p0:=[Rationals()!a: a in p0];
            P0:=X!p0;        
        end if;

        // Our genus 1 curve X has a Q-point P0.
        E0,pi0:=EllipticCurve(X,P0);
        E,pi1:=MinimalModel(E0);
        pi:=Expand(pi0*pi1);  // Isomorphism X->E sending P0 to 0.
        W:=DefiningEquations(pi);
        Pol<[x]>:=PolynomialRing(Rationals(),#F);
        W:=[Pol!a: a in W];

        c:=[  [Evaluate(pol,[f[j]:f in F]) : j in [1..#M`cusps]] : pol in W];
        if &or [IsWeaklyZero(c[3][j]) : j in [1..#M`cusps]] then
            return FindModelOfXG(M, prec+20 : compute_all:=compute_all, G0:=G0);  // try again with more precision
        end if;
        x:=[c[1][j]/c[3][j]: j in [1..#M`cusps]];
        y:=[c[2][j]/c[3][j]: j in [1..#M`cusps]];
 
        M`f:=[x,y];
        M`C:=E;

        M`has_infinitely_many_points:=Rank(E) ge 1;
        
        r:=Rank(Parent(W[1]));
        Pol<[x]>:=PolynomialRing(Rationals(),r);
        //M`phiC:=[Pol!a: a in W];
    end if;

    return M;  
end intrinsic;

/* 
   The follow sequence consists of all pairs [N,i] where N and i are the level and index, respectively, of 
   all congruence subgroups of PSL_2(Z) of genus 0 or 1.  This follows from the work of Cummin and Pauli; 
   Using their code, type: load "csg1-lev48.dat"; {[a`level,a`index]: a in L};
 */
low_genus:={[1, 1], [2, 2], [2, 3], [2, 6], [3, 3], [3, 4], [3, 6], [3, 12], [4, 4], [4, 6], [4, 6], [4, 8], [4, 12], 
            [4, 12], [4, 24], [5, 5], [5, 6],  [5, 10], [5, 12], [5, 15], [5, 20], [5, 30], [5, 60], [6, 6], [6, 6], 
            [6, 8], [6, 9], [6, 12], [6, 12], [6, 18], [6, 18], [6, 24], [6, 24], [6, 36], [6, 36], [7, 7], [7, 8], 
            [7, 14], [7, 21], [7, 24], [7, 28], [7, 42], [8, 8], [8, 12], [8, 12], [8, 12], [8, 16], [8, 16], [8, 24], 
            [8, 24], [8, 24], [8, 24], [8, 24], [8, 24], [8, 32], [8, 48], [8, 48], [8, 48], [9, 9], [9, 12], [9, 12], 
            [9, 18], [9, 18], [9, 27], [9, 27], [9, 36], [9, 36], [9, 36], [10, 10], [10, 12], [10, 18], [10, 20], 
            [10, 30], [10, 36], [10, 36], [11, 11], [12, 12], [12, 16], [12, 18], [12, 18], [12, 24], [12, 24], 
            [12, 36], [12, 36], [12, 48], [12, 48], [13, 14], [13, 28], [13, 42], [14, 14], [14, 16], [14, 48], 
            [15, 15], [15, 18], [15, 36], [16, 16], [16, 24], [16, 24], [16, 24], [16, 24], [16, 32], [16, 48], 
            [16, 48], [18, 18], [18, 24], [18, 24], [18, 36], [18, 36], [20, 36], [21, 21], [24, 36], [24, 48], 
            [25, 30], [25, 60], [26, 28], [27, 36], [28, 32], [30, 36], [32, 48], [36, 48], [48, 72], [6, 6], [6, 12], 
            [6, 18], [6, 24], [6, 36], [6, 72], [7, 42], [7, 56], [7, 84], [8, 12], [8, 24], [8, 24], [8, 24], [8, 32],
            [8, 48], [8, 48], [8, 48], [8, 48], [8, 64], [8, 96], [9, 12], [9, 18], [9, 36], [9, 36], 
            [9, 54], [9, 54], [9, 81], [9, 108], [10, 12], [10, 15], [10, 20], [10, 24], [10, 30], [10, 30], [10, 36], 
            [10, 40], [10, 45], [10, 60], [10, 72], [11, 12], [11, 55], [11, 55], [11, 60], [12, 16], [12, 18], 
            [12, 18], [12, 24], [12, 24], [12, 24], [12, 24], [12, 24], [12, 32], [12, 36], [12, 36], [12, 36], 
            [12, 36], [12, 36], [12, 48], [12, 48], [12, 48], [12, 64], [12, 72], [12, 72], [12, 72], [12, 96], 
            [14, 14], [14, 21], [14, 24], [14, 28], [14, 42], [14, 42], [14, 56], [14, 72], [15, 15], [15, 20], 
            [15, 24], [15, 30], [15, 36], [15, 45], [15, 48], [15, 72], [15, 96], [16, 24], [16, 24], 
            [16, 24], [16, 24], [16, 48], [16, 48], [16, 48], [16, 48], [16, 48], [16, 48], [16, 48], [16, 48], 
            [16, 96], [17, 18], [17, 36], [17, 72], [18, 18], [18, 18], [18, 24], [18, 24], [18, 27], [18, 36], 
            [18, 36], [18, 54], [18, 54], [18, 72], [18, 72], [19, 20], [19, 60], [20, 20], [20, 24], [20, 24], 
            [20, 36], [20, 36], [20, 40], [20, 48], [20, 72], [20, 72], [20, 72], [21, 24], [21, 32], [21, 42], 
            [21, 42], [21, 63], [21, 64], [22, 22], [24, 24], [24, 24], [24, 36], [24, 36], [24, 36], [24, 48], 
            [24, 48], [24, 72], [24, 72], [24, 96], [26, 28], [26, 56], [27, 36], [27, 36], [27, 108], [28, 28], 
            [30, 30], [30, 30], [30, 36], [30, 72], [32, 48], [32, 48], [32, 48], [32, 48], [32, 96], [33, 33], 
            [36, 36], [36, 48], [36, 72], [39, 42], [40, 72], [42, 42], [42, 42], [49, 56], [52, 56]
};

intrinsic HasLowGenus(G::GrpMat: sl2level:=0, index:=0) -> BoolElt
{
        Input:   G be a subgroup of GL(2,Z/MZ) for some M>1 that contains -I.
        Output:  return "true" if the modular curve X_G has genus at most 1 and "false" otherwise.

        Let Gamma be the congruence subgroup of SL(2,Z) consisting of matrices whose image mod N lies in  G.
        The level "sl2level" of Gamma and the "index" of Gamma in SL(2,Z) can be specified by the user if already known.
}

    if sl2level eq 1 or index eq 1 then return true; end if; // j-line case
    if sl2level ne 0 and index ne 0 then
        // In some cases the pair [N,index] is enough to rule out low genus.
        if [sl2level,index] notin low_genus then return false; end if;
    else
        SL2:=SL(2,BaseRing(G));
        GL2:=SL(2,BaseRing(G));
        if GL2![-1,0,0,-1] notin G then G:=sub<GL2|Generators(G) join {GL2![-1,0,0,-1]}>; end if;
        H:=G meet SL2;  

        sl2level:=sl2Level(H);
        if sl2level eq 1 then return true; end if;
        H:=ChangeRing(H,Integers(sl2level));
        index:=Index(SL(2,Integers(sl2level)),H);
        // In some cases the pair [N,index] is enough to rule out low genus.
        if [sl2level,index] notin low_genus then 
            return false; 
        end if;
    end if;

    // Now compute the genus directly.
    M:=CreateModularCurveRec(#BaseRing(G), [Eltseq(g): g in Generators(G)]);  
	return M`genus le 1; 
end intrinsic;

intrinsic FindRelationRational(M::Rec, j::.) -> .
{ Input:
                M:  a record of type "ModularCurveRec" (for example produced as output of CreateModularCurveRec) that 
                    corresponds to a modular curve X_G.  
                    We assume that X_G is an genus 0 curve isomorphic to P^1_Q and that Q(X_G)=Q(f), where f:=M`f is given by q-expansions at the cusps of M.

                j:  An element of Q(X_G).   We assume that all the poles of j occur at cusps or that that the values it
                    takes at cusps are distinct from the values it takes at noncuspidal points.
    Output:
                The rational function phi in Q(t) so that phi(f)=j.
}

    vinf:=M`vinf; 
    assert vinf eq #j;
    if &and[Valuation(j[i]) ge 0: i in [1..vinf]] then  
        // case where j does not have a pole at any cusp
        c:=Coefficient(j[1],0);

        // easiest case is that j is constant!
        if &and[ IsWeaklyZero(j[i]-c): i in [1..vinf]] then
            return c; 
        end if;

        // otherwise use assumption on j to force all poles to be at cusps
        j:=[1/(j[i]-c): i in [1..vinf] ];  
        return 1/FindRelationRational(M,j)+c;
    end if;
    f:=M`f;
    K:=Compositum(BaseRing(Parent(f[1])),BaseRing(Parent(j[1])));
    F<t>:=FunctionField(K);
    phi:=F!0;
    j0:=j;
    for i in [1..vinf] do
        if Valuation(f[i]) lt 0 then
            u:=[f[k]: k in [1..vinf]];
            phi1:=t;
        else
            u:=[1/(f[k]-Coefficient(f[i],0)) : k in [1..vinf]];       
            phi1:=1/(t-Coefficient(f[i],0));
        end if;
        e:=-Valuation(u[i]);
        while Valuation(j[i]) le 0 do
            m:=(-Valuation(j[i])) div e;
            c:= LeadingCoefficient(j[i])/LeadingCoefficient(u[i])^m;
            j:=[j[k]-c*u[k]^m: k in [1..vinf]];
            phi:=phi+c*phi1^m;
        end while;
    end for;
    return phi;
end intrinsic;

intrinsic FindRelationElliptic(M::Rec,f::.) -> .
{ Input:
                M:  a record M type "ModularCurveRec" (for example produced as output of CreateModularCurveRec) that 
                    corresponds to a modular curve X_G.  
                    We assume that X_G is an elliptic curve and that M`f=[x,y], where Q(X_G)=Q(x,y) and the meromorphic 
                    functions x and y on X_G satisfy a Weierstrass equation over Q given by the elliptic curve E:=M`C 
                    [ x and y are given by q-expansions at the cusps and in special cases will be produced by
                    the function "FindModelOfXG"].
                f:  An element of Q(X_G).   We assume that all the poles of f occur at cusps or that that the values it
                    takes at cusps are distinct from the values it takes at noncuspidal points.
    Output:
            A rational function phi in Q(E)=Q(x,y) so that phi(x,y)=f.
}  

    E:=M`C;  
    x0:=M`f[1];   
    y0:=M`f[2];
    vinf:=M`vinf; 

    // If f has no pole at all cusps, we introduce one and start again.
    if &and[Valuation(f[j]) ge 0: j in [1..vinf]] then
        _,i0:=Maximum(M`widths);
        c:=Coefficient(f[i0],0);

        // easiest case is that f is constant!
        if &and[ IsWeaklyZero(f[j]-c): j in [1..vinf]] then
            return c;   
        end if;

        // otherwise use assumption on j to force only poles at cusps        
        f:=[1/(f[j]-c): j in [1..vinf] ];
        u:=FindRelationElliptic(M,f);
        return 1/u+Parent(u)!c;
    end if;

    K:=Compositum(BaseRing(Parent(x0[1])),BaseRing(Parent(f[1])));
    R<q>:=LaurentSeriesRing(K);
    EK:=ChangeRing(E,K);
    F<x,y>:=FunctionField(EK);
    EF:=ChangeRing(E,F);

    // We first find the K-points on E corresponding to the cusps of X_G.
    p:=[];
    for j in [1..vinf] do
        v:=Minimum({Valuation(x0[j]),Valuation(y0[j]),0});
        c:=[q^(-v)*R!x0[j],q^(-v)*R!y0[j], q^(-v)];
        p:=p cat [EK![Coefficient(a,0):a in c]];
    end for;

    // We focus on the i-th cusp which has largest width
    _,i:=Maximum(M`widths);
    
    // Rational function on E corresponding to subtracting by p[i].
    h:=EF![x,y,1]-EF!p[i];    assert h[3] eq 1;
    
    // Construct x1 and y1 that have poles of order 2 and 3, respectively, at i-th cusp.  No other poles.
    x1:= [ Evaluate(Numerator(h[1]),[x0[j],y0[j]])/Evaluate(Denominator(h[1]),[x0[j],y0[j]])  : j in [1..vinf]];
    y1:= [ Evaluate(Numerator(h[2]),[x0[j],y0[j]])/Evaluate(Denominator(h[2]),[x0[j],y0[j]])  : j in [1..vinf]];
    e:=(-Valuation(x1[i])) div 2;
    assert Valuation(x1[i]) eq -2*e and Valuation(y1[i]) eq -3*e;

    L<t>:=FunctionField(F);
    phi:=t;

    while &or[Valuation(f[j]) lt 0 : j in [1..vinf]] or Valuation(f[i]) le 0 do   

        // If we find a pole at any cusp besides the i-th cusp, we multiply f by x1-c for some c, so that
        //   the order of the pole is reduced (and the pole at the i-th cusp is increased)
        J:=[j: j in [1..vinf] | j ne i and Valuation(f[j]) lt 0];
        if #J ne 0 then
            j0:=J[1];
            c:=Coefficient(x1[j0],0);
            f:=[(x1[j]-c)*f[j]: j in [1..vinf]];
            phi0:=1/(h[1]-c)*t;
            phi:=Evaluate(phi,phi0);
        end if;

        // We now subtract from f polynomials in x1 and y1 so that at the i-th cusp we either have a pole of
        // order 1 or a zero.
        while Valuation(f[i]) le 0 and Valuation(f[i]) ne -e do   
            m:=(-Valuation(f[i])) div e;
            if IsEven(m) then                
                u:= x1[i]^(m div 2);
                c:=LeadingCoefficient(f[i])/LeadingCoefficient(u);
                f[i]:=f[i]-c*u;  
                phi0:=t + c*h[1]^(m div 2);
                phi:=Evaluate(phi,phi0);
            else
                u:=x1[i]^((m-3) div 2)*y1[i];  
                c:=LeadingCoefficient(f[i])/LeadingCoefficient(u);
                f[i]:=f[i]-c*u;  
                phi0:=t + c*h[1]^((m-3) div 2)*h[2];
                phi:=Evaluate(phi,phi0);
            end if;
        end while;

    end while;

    phi:=F!Evaluate(phi,0);

    // coerce to be defined over rationals if possible
    phi0:=ProjectiveRationalFunction(phi); 
    c:=Coefficients(Numerator(phi0)) cat Coefficients(Denominator(phi0));
    if &and [a in Rationals(): a in c] then
        L<x,y>:=FunctionField(M`C);
        Pol:=PolynomialRing(Rationals(),3);
        return Evaluate(Pol!Numerator(phi0),[x,y,1])/Evaluate(Pol!Denominator(phi0),[x,y,1]);
    end if;

    return phi;
end intrinsic;

intrinsic FindMorphismBetweenModularCurves(M::Rec, M0::Rec, g::GrpMatElt) -> SeqEnum
{  
    Input:
        M, M0 : records of type "ModularCurveRec" (for example produced as output of CreateModularCurveRec) that 
                corresponds to modular curves X_G and X_G0, respectively.  We assume that X_G and X_G0 are either
                isomorphic to P^1_Q or an elliptic curve and that models M`C and M0`C have been computed 
                (say by the function "FindModelOfXG" or "FindSerreTypeModel").
                We further assume that G0 is a subgroup of GL(2,Z/NZ) and that G is a subgroup of GL(2,Z/nZ) for some n dividing N.

        g     : matrix in GL(2,Z/NZ).   After lifting G to a subgroup of GL(2,Z/NZ), we assume that g^(-1)*G*g is a subgroup of G0.   

        We obtain a homomorphism of function fields
                Q(X_G0) -> Q(X_(g*G0*g^(-1))) -> Q(X_G)
        where the first is the action on meromorphic functions given by g^(-1) and the second is an inclusion.
    Output:
        A sequence of polynomials that gives the morphism M`C->M0`C corresponding to the field homomorphism Q(X_G0) -> Q(X_G).
}

    g:=GL(2,Integers(M`N))!g;

    assert M`has_point and assigned M`f;  
    assert M0`has_point and assigned M0`f;
    assert M`genus le 1 and M0`genus le 1;

    if M0`genus eq 0 then
        h:=ConvertModularFormExpansions(M, M0, g^(-1), M0`f); 
        if M`genus eq 0 then
            J:=FindRelationRational(M,h);
            F<t>:=FunctionField(Rationals());
            J:=F!J;
            R<x,y>:=PolynomialRing(Rationals(),2);
            JJ:=Evaluate(J,x/y);
            return [R!Numerator(JJ),R!Denominator(JJ)];
        elif M`genus eq 1 then
            phi:=FindRelationElliptic(M,h);
            phi:=ProjectiveRationalFunction(phi); 
            R<x,y,z>:=PolynomialRing(Rationals(),3);
            return [R!Numerator(phi),R!Denominator(phi)];
        end if;
    end if;

    // We now are in the setting where M0`genus and M`genus equal 1.
    // We make use of the cusps which are defined over a cyclomic field and are easy to work with
    // since we have q-expansions at them.

    E0:=M0`C; 
    x0:=M0`f[1]; 
    y0:=M0`f[2];

    K0:=BaseRing(Parent(x0[1]));
    R0<q>:=LaurentSeriesRing(K0);
    E0_:=ChangeRing(E0,K0);
    L<X,Y>:=FunctionField(E0_);
    E0L:=ChangeRing(E0_,L);

    // Focus on the i0-th cusp
    _,i0:=Maximum(M0`widths);
    v:=Minimum({Valuation(x0[i0]),Valuation(y0[i0]),0});
    P0:=[q^(-v)*R0!x0[i0],q^(-v)*R0!y0[i0], q^(-v)];
    P0:=[Coefficient(a,0): a in P0];
    
    h0:=E0L![X,Y,1]-E0L!P0;    assert h0[3] eq 1;
    x1:=[Evaluate(Numerator(h0[1]),[x0[j],y0[j]])/Evaluate(Denominator(h0[1]),[x0[j],y0[j]]) :  j in [1..#M0`cusps]];
    y1:=[Evaluate(Numerator(h0[2]),[x0[j],y0[j]])/Evaluate(Denominator(h0[2]),[x0[j],y0[j]]) :  j in [1..#M0`cusps]];
    // x1 and y1 have there only poles at the i0-th cusp and they have order 2 and 3, respectively.

    // checks
    h1:=ProjectiveRationalFunction(h0[1]);
    h2:=ProjectiveRationalFunction(h0[2]);
    assert &and [IsWeaklyZero(Evaluate(h1,[x0[j],y0[j],1]) - x1[j]): j in [1..#M0`cusps]];
    assert &and [IsWeaklyZero(Evaluate(h2,[x0[j],y0[j],1]) - y1[j]): j in [1..#M0`cusps]];


    x2:=ConvertModularFormExpansions(M, M0, g^(-1), x1);
    y2:=ConvertModularFormExpansions(M, M0, g^(-1), y1);
    phi1:=FindRelationElliptic(M,x2);
    phi2:=FindRelationElliptic(M,y2);
    phi1:=ProjectiveRationalFunction(phi1); 
    phi2:=ProjectiveRationalFunction(phi2); 

    assert &and [IsWeaklyZero(Evaluate(phi1,[M`f[1][j],M`f[2][j],1]) - x2[j]): j in [1..#M`cusps]];
    assert &and [IsWeaklyZero(Evaluate(phi2,[M`f[1][j],M`f[2][j],1]) - y2[j]): j in [1..#M`cusps]];

    h:=E0L![X,Y,1]+E0L!P0;    assert h[3] eq 1;

    psi_x:=Evaluate(ProjectiveRationalFunction(h[1]), [phi1,phi2,1] );
    psi_y:=Evaluate(ProjectiveRationalFunction(h[2]), [phi1,phi2,1] );

    E:=M`C;

    E_:=ChangeRing(E,K0);
    L<x,y>:=FunctionField(E_);

    psi_x:=ProjectiveRationalFunction(  Evaluate(psi_x,[x,y,1])  );
    psi_y:=ProjectiveRationalFunction(  Evaluate(psi_y,[x,y,1])  );

    R:=PolynomialRing(Rationals(),3);
    psi_x:=R!Numerator(psi_x)/R!Denominator(psi_x);
    psi_y:=R!Numerator(psi_y)/R!Denominator(psi_y);

    //Checks
    x0_:=ConvertModularFormExpansions(M, M0, g^(-1), x0);
    y0_:=ConvertModularFormExpansions(M, M0, g^(-1), y0);
    assert &and [IsWeaklyZero(Evaluate(psi_x,[M`f[1][j],M`f[2][j],1]) - x0_[j]): j in [1..#M`cusps]];
    assert &and [IsWeaklyZero(Evaluate(psi_y,[M`f[1][j],M`f[2][j],1]) - y0_[j]): j in [1..#M`cusps]];

    Q:=LCM([Denominator(psi_x),Denominator(psi_y)]);
    R<x,y,z>:=PolynomialRing(Rationals(),3);
    
    return [ R!Numerator(Q*psi_x), R!Numerator(Q*psi_y), R!Q ];
end intrinsic;

intrinsic FindRelationRationalBruteForce(M::Rec, h::.: d:=0, check:=false, wt:=0) -> .
{ Input:
                M:  a record M type "ModularCurveRec" (for example produced as output of CreateModularCurveRec) that 
                    corresponds to a modular curve X_G.  
                    We assume that X_G is an genus 0 curve isomorphic to P^1_Q and that Q(X_G)=Q(f), where f:=M`f is given by q-expansions at the cusps of M.
                h:  An element of Q(X_G), given by q-expansions at the cusps of M.
        Output:
                The rational function phi in Q(t) so that phi(f)=h.

        Warning: The function tries to find a rational function phi of degree d so that phi(f)=h holds (at least for ther terms of the q-expansions given!). 
        If no such phi of degree d exists, it will then try degree d+1, etc.

        Suppose that "check" is true and h is known to be a quotient of modular forms from M_wt,G where "wt" is an integer greater than 1.  Then the rational
        function phi is proved to be correct (or an error will occur).        
}

    assert M`genus eq 0 and assigned M`f;
    L<t>:=FunctionField(Rationals());

    if d eq 0 then
        // Check if h is constant first.
        assert exists(i){i: i in [1..#h] | AbsolutePrecision(h[i]) gt 0};
        c:=Coefficient(h[i],0);
        if &and [ IsWeaklyEqual(c,f): f in h] then
            return L!c;
        else
            return FindRelationRationalBruteForce(M,h: d:=d+1, check:=check, wt:=wt);
        end if;
    end if;

    f:=M`f;
    
    K:=Compositum(BaseRing(Parent(h[1])),BaseRing(Parent(f[1])));
    P<[a]>:=PolynomialRing(K,2*d+2);
    R<q>:=PuiseuxSeriesRing(P);

    V:=VectorSpace(K,2*d+2);
    W:=sub<V|{}>; 
    r:=0;

    for j in [1..M`vinf] do
        // compute powers of f[j];
        f_pow:=[1];
        u:=1;
        for i in [1..d] do
            u:=u*f[j];
            f_pow:=f_pow cat [u];
        end for;        
        f_pow:=[R!u: u in f_pow];
    
        s:=&+[a[i+1]*f_pow[i+1] : i in [0..d]]  - R!h[j] * &+[ a[d+2+i ]*f_pow[i+1] : i in [0..d] ];

        while IsWeaklyZero(s) eq false do

            v:=Valuation(s); 
            c:=P!Coefficient(s,v);   
            s:=s-c*q^v;

            w:= V![K!MonomialCoefficient(c,a[i]) : i in [1..2*d+2]];
            if w notin W then
                W:=sub<V|Generators(W) join {w}>;
                r:=r+1; // dimension of W
                if r eq 2*d+2 then // when W=V
                    break j;
                end if;
            end if;

        end while;

    end for;

    B:=Matrix([ Eltseq(w): w in Basis(W)]);

    if Rank(B) gt 2*d+1 then
        // There is no rational function of the given degree; try higher degree.
        return FindRelationRationalBruteForce(M,h: d:=d+1, check:=check, wt:=wt);
    end if;
    // There is no rational function of the given degree (or d is not minimal)
    error if Rank(B) lt 2*d+1, "Not enough terms of q-expansion or degree too large."; 

    v:=Basis(NullSpace(Transpose(B)))[1];
    v:=Eltseq(v);
    s:=[i: i in [1..#v] | v[i] ne 0];
    if #s ne 0 then 
        v:=[a/v[s[1]]: a in v];
    end if;

    // Need denominator to be nonzero and scalars to be rationals; otherwise increase degree and try again. 
    if #s eq 0 or &and[ a in Rationals() :  a in v] eq false or &and[v[d+2+i] eq 0: i in [0..d]] then 
        return FindRelationRationalBruteForce(M,h: d:=d+1, check:=check, wt:=wt);
    end if;

    v:=[Rationals()!a: a in v];    
    phi:=(&+[ v[i+1]*t^i : i in [0..d]])/(&+[ v[d+2+i]*t^i : i in [0..d] ]);

    if check then
        if IsEven(wt) then
            pole_upper_bound:=wt*(2*M`genus-2) + wt/2*M`vinf + 2*M`v2*Floor(wt/4) + 2*M`v3*Floor(wt/3);
        else
            pole_upper_bound:=wt*(2*M`genus-2) + wt/2*M`vinf + M`v2*Floor(wt/2) + M`v3*Floor(2*wt/3);
        end if;        
        zero_lower_bound:=0;
        for j in [1..M`vinf] do
            u:=Evaluate(phi,M`f[j])-h[j];
            assert IsWeaklyZero(u); 

            e:=M`widths[j]/M`N*Valuation(u);
            if not M`regular[j] then e:=e/2; end if;
            zero_lower_bound:=zero_lower_bound+ e;
        end for;
        assert zero_lower_bound gt pole_upper_bound;  
        // phi(f)-h has more zeros than poles, so must be 0
    end if;

    return phi;
end intrinsic;

intrinsic FindRelationEllipticBruteForce(M::Rec,h::.: d:=0, check:=false, wt:=0) -> .
{ Input:
                M:  a record M type "ModularCurveRec" (for example produced as output of CreateModularCurveRec) that 
                    corresponds to a modular curve X_G.  
                    We assume that X_G is an elliptic curve E:=M`C over Q and that Q(X_G)=Q(x,y), where M`f=[x,y] are modular functions satisfying the 
                    Weieerstrass equation for E given by q-expansions at the cusps of M.

                h:  An element of Q(X_G), given by q-expansions at the cusps of M.
        Output:
                The rational function phi in Q(x,y) so that phi(x,y)=h.

        Warning: The function tries to find phi of degree d so that phi(x,y)=h holds (at least for ther terms of the q-expansions given!). 
        If no such phi of degree d exists, it will then try degree d+1, etc.

        Suppose that "check" is true and h is known to be a quotient of modular forms from M_wt,G where "wt" is an integer greater than 1.  Then the function
        phi is proved to be correct (or an error will occur).      
}

    if d eq 0 then
        // Check if h is constant first.
        assert exists(i){i: i in [1..#h] | AbsolutePrecision(h[i]) gt 0};
        c:=Coefficient(h[i],0);
        if &and [ IsWeaklyEqual(c,f): f in h] then
            F<x,y>:=FunctionField(M`C);
            return F!c;
        else
            return FindRelationEllipticBruteForce(M,h: d:=d+1, check:=check, wt:=wt);
        end if;
    end if;

    assert M`genus eq 1 and assigned M`f;
    x0:=M`f[1];
    y0:=M`f[2];

    K:=Compositum(BaseRing(Parent(h[1])),BaseRing(Parent(x0[1])));
    P<[a]>:=PolynomialRing(K,3*d+2);
    R<q>:=PuiseuxSeriesRing(P);
 
    V:=VectorSpace(K,3*d+2);
    W:=sub<V|{}>; 
    r:=0;

    for j in [1..M`vinf] do
        // compute powers of x0[j];
        x0_pow:=[1];
        u:=1;
        for i in [1..d] do
            u:=u*x0[j];
            x0_pow:=x0_pow cat [u];
        end for;        
        x0_pow_y:=[R!(y0[j]*u): u in x0_pow];
        x0_pow:=[R!u: u in x0_pow];
    
        s:=&+[ a[i+1]*x0_pow[i+1] : i in [0..d] ] + &+[ a[d+2+i]*x0_pow_y[i+1] : i in [0..d-1] ]  - R!h[j] * &+[ a[2*d+2+i]*x0_pow[i+1] : i in [0..d] ];

        while IsWeaklyZero(s) eq false do
            v:=Valuation(s); 
            c:=P!Coefficient(s,v);   
            s:=s-c*q^v;
            w:= V![K!MonomialCoefficient(c,a[i]) : i in [1..3*d+2]];
            if w notin W then
                W:=sub<V|Generators(W) join {w}>;
                r:=r+1; // dimension of W
                if r eq 3*d+2 then // when W=V
                    break j;
                end if;
            end if;
        end while;
             
    end for;

    B:=Matrix([ Eltseq(w): w in Basis(W)]);

    if Rank(B) eq 3*d+2 then
        // There is no rational function of the given degree; try higher degree.
        return FindRelationEllipticBruteForce(M,h: d:=d+1, check:=check, wt:=wt);
    end if;
    // There is no rational function of the given degree (or d is not minimal)
    error if Rank(B) lt 3*d+1, "Not enough terms of q-expansion or degree too large."; 

    v:=Basis(NullSpace(Transpose(B)))[1];
    v:=Eltseq(v);
    s:=[i: i in [1..#v] | v[i] ne 0];
    if #s ne 0 then 
        v:=[a/v[s[1]]: a in v];
    end if;

    // Need denominator to be nonzero and scalars to be rationals.
    if #s eq 0 or &and[ a in Rationals() :  a in v] eq false or &and[v[2*d+2+i] eq 0: i in [0..d]] then 
        return FindRelationEllipticBruteForce(M,h: d:=d+1, check:=check, wt:=wt);
    end if;

    v:=[Rationals()!a: a in v];
    F<a,b>:=FunctionField(Rationals(),2);
    num:=&+[ v[i+1]*a^i : i in [0..d]] + &+[ v[d+2+i]*a^i*b : i in [0..d-1] ];
    den:=&+[ v[2*d+2+i]*a^i : i in [0..d] ];

    F<x,y>:=FunctionField(M`C);
    phi:=Evaluate(num,[x,y])/Evaluate(den,[x,y]);

    if check then
        
        if IsEven(wt) then
            pole_upper_bound:=wt*(2*M`genus-2) + wt/2*M`vinf + 2*M`v2*Floor(wt/4) + 2*M`v3*Floor(wt/3);
        else
            pole_upper_bound:=wt*(2*M`genus-2) + wt/2*M`vinf + M`v2*Floor(wt/2) + M`v3*Floor(2*wt/3);
        end if;
        zero_lower_bound:=0;
        for j in [1..M`vinf] do
            a:=[M`f[1][j], M`f[2][j]];
            u:= Evaluate(num,a)/Evaluate(den,a) - h[j];   
   
            assert IsWeaklyZero(u); 
            e:=M`widths[j]/M`N*Valuation(u);
            if not M`regular[j] then e:=e/2; end if;
            zero_lower_bound:=zero_lower_bound+ e;
        end for;

        assert zero_lower_bound gt pole_upper_bound;
        // phi(x,y)-h has more zeros than poles, so must be 0
    end if;
    
    return phi;
end intrinsic;

intrinsic FindCoverOfModularCurve(M0::Rec,M::Rec,prec::RngIntElt : simplify_serre_type:=true) -> .,.,. 
{     Input:             
            M0: a record of type "ModularCurveRec" corresponding to the modular curve X_G0, where G0:=M0`G.                                        
                We assume that X_G0 is isomorphic to either P^1 or an elliptic curve.

                If X_G0 has genus 0, we assume that Q(X_G0)=Q(f) with f:=M0`f.
                If X_G0 has genus 1, we assume that Q(X_G0)=Q(x,y) with M0`f=[x,y], where x,y satisfy the Weierstrass equation of the 
                    elliptic curve E:=M0`C.

            M:  another record corresponding to a modular curve X_B with B a subgroup of GL(2,Z/NZ) with N>1 that contains -I.  
                We assume that the level of G0 divides N and that when G0 is lifted to a subgroup of GL(2,Z/NZ), B is a proper subgroup of G0.  

                We further assume further that either 
                    - B has full determinant and B is a maximal subgroup of G0  (main case!)
                    - B and G0 have the same intersection with SL(2,Z/NZ)
            prec:  a positive integer that says how many terms of the q-expansions to compute.  

        Output:
                MAIN CASE: when B has full determinant.
                    The output consists of: a boolean flag, a polynomial P=P(u), and a modular function f in Q(X_B).

                    Fist suppose that flag is true.
                        The polynomial P(u) is in Q(X_G0)[u].  

                        The function f in Q(X_B) satisfies P(f)=0; it is given as q-expansions at the cusps as determined by the returned record for X_B.
                        Moreover, Q(X_G0)(f)=Q(X_B) and P(u) is irreducible over Q(X_G0).

                        [Observe that P gives a singular model of X_B with a natural morphism to X_G0; this is the desired cover]
                    
                    When flag is false.
                        Now P(u) is a polynomial in Q(X_G0)[u] is of the form u^2-b with b in Q(X_G0).  
                        If we replace P by u^2 - (j-1728)*b, with j the modular j-invariant, then it will satisfies the above properties.
                                                                        
                    We will always have flag equal true when "simplify_serre_type" is set to true and M0`map_to_jline is assigned.

                    Additionally: When P(u) has degree 2, we will make choices so that the degree 1 term vanishes.  
                        
                In the other case, we return the value true, the minimal polynomial P in Q[x] of a primitive element f of the extension Q(zeta_N)^det B of Q, and f. 
                
}

    B:=M`G;
    N:=M`N;

    if M0`degree ne 1 then
        G0:=gl2Lift(M0`G,N);
    else    
        G0:=GL(2,Integers(N));
    end if;
    assert B subset G0; 
    assert B ne G0;

    // Compute group det(B)
    U,iota:=UnitGroup(Integers(N));  
    iota_inv:=Inverse(iota);   
    detB:=sub<U|{iota_inv(Integers(N)!Determinant(g)): g in Generators(B)}>;

    // Boring case where B and G0, as subgroups of GL(2,Zhat), have same intersection with SL(2,Zhat).
    if #detB ne EulerPhi(N) then  
        assert Index(G0,B) eq EulerPhi(N) div #detB;
        K<z>:=CyclotomicField(N);
        L:=sub<K|[K!1]>;
        detB_:={Integers()!iota(u): u in detB};
        for i in [1..EulerPhi(N)-1] do
            a:=&+[z^(i*j): j in detB_];
            if a notin L then
                L:=sub<K|Generators(L) cat [a]>;
            end if;
            if AbsoluteDegree(L) eq Degree(K) div #detB then break i; end if;
        end for;
        _<u>:=PolynomialRing(Rationals());
        a:=PrimitiveElement(L);
        min:=MinimalPolynomial(a);
        assert Degree(min) eq Degree(K) div #detB;

        if Degree(min) eq 2 then
            d:=Rationals()!Discriminant(min);
            d:=Integers()!(Denominator(d)^2*d);
            for p in PrimeDivisors(d) do
                d:=d div p^(2* (Valuation(d,p) div 2) );
            end for;
            min:=u^2-d;
            a:=Roots(ChangeRing(min,K))[1][1];
        end if;

        R<q>:=LaurentSeriesRing(K);
        return true, min, [K!a + O(q^Maximum(prec,300)) : j in [1..M0`vinf]];
        // We are returning the third values as a constant modular function 
    end if;


    // The following looks complicated, but it just computes a boolean "serre_type" that will determine which method we 
    // use to compute our cover. 
    primes:={p: p in PrimeDivisors(N) | p notin PrimeDivisors(M0`N)};
    if #primes ne 0 then 
        p:=Minimum(primes); 
        N1:=p^Valuation(N,p); 
        N2:= N div N1;
    end if;
    serre_type:= #primes ne 0 and primes subset {2,3} and Index(G0,B) eq 2 and ChangeRing(B,Integers(N1)) eq GL(2,Integers(N1));
    if #primes ne 0 and not serre_type and N mod 2 eq 0 and Index(G0,B) eq 2 then
        p:=2;
        N1:=2^Valuation(N,2);
        N2:=N div N1;
        if N1 gt 1 and N2 gt 1 and ChangeRing(B,Integers(N2)) eq ChangeRing(G0,Integers(N2)) and ChangeRing(G0,Integers(N1)) eq GL(2,Integers(N1)) and
            Index( GL(2,Integers(N1)), ChangeRing(B,Integers(N1))) eq 2 then
            serre_type:=true;
        end if;        
    end if;


    if not serre_type then
        // MAIN CASE  
        
        // Find a positive even weight k so that M_{k,B} gives rise to a projective embedding of X_B
        k:=0;
        repeat
            k:=k+2;
            degD:= (k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps;
            // Riemann-Roch condition
        until degD ge 2*M`genus+1;


        time M:=FindModularForms(k,M,prec);  // Compute modular forms of weight k (We are computing more than we need here!)
        F:=M`F;  

        // Find a function h in Q(X_B) but not in Q(X_G0), and find its conjugates hh by B\G0.   Here we use that B is maximal in G0.
        T:=[t: t in Transversal(G0,B) ]; 
        found:=false;
        for i in [2..#F] do
            h:=[F[i][j]/F[1][j]: j in [1..M`vinf]];
            hh:=[ConvertModularFormExpansions(M, M, t, h) : t in T];
            if &or[IsWeaklyEqual(hh[e][j],hh[f][j]) : e in [1..#T], f in [1..#T], j in [1..M`vinf] | e lt f] eq false then 
                // checking if not all conjugates are the same
                found:=true;
                break i;
            end if;
        end for;
        assert found;


        // Find sequence consisting of the coefficients of the minimal polynomial of our function hh over Q(X_G0), 
        // with coefficients given by q-expansions.
        R<u>:=PolynomialRing(Parent(hh[1][1]));
        c:=[ []: d in [1..#T]];
        for j in [1..M`vinf] do
            P:=&*[(u-h[j]) : h in hh];
            for d in [1..#T] do
                c[d]:=c[d] cat [Coefficient(P,#T-d)];
            end for;
        end for;
        c:=[ ConvertModularFormExpansions(M0, M,[1,0,0,1], f) : f in c ];
        c:=[c[d]: d in [1..#T]];


        // Express minimal polynomial with coefficients in Q(t) or Q(x,y)
        if M0`genus eq 0 then
            L<t>:=FunctionField(Rationals());    
            Pol<u>:=PolynomialRing(L);
            P:=u^(#T)+ &+[ L!FindRelationRationalBruteForce(M0,c[d] : check:=true, wt:=k) * u^(#T-d) : d in [1..#T] ];   
        else
            assert M0`genus eq 1;
            c:=[FindRelationEllipticBruteForce(M0,a : check:=true, wt:=k): a in c];
            L:=Parent(c[1]);
            Pol<u>:=PolynomialRing(L);
            P:=u^(#T)+ &+[ c[d] * u^(#T-d) : d in [1..#T] ]; 
        end if;
        flag:=true;


        // When [G0:B] =2, we choose h so that the linear coefficient of its minimal polynomial over Q(X_G0) is 0.
        if #T eq 2 then
            aa:=[ hh[1][j] + hh[2][j]  : j in [1..M`vinf] ]; 
            h:=[h[j]-aa[j]/2 : j in [1..M`vinf]];
            hh:=[ConvertModularFormExpansions(M, M, t, h) : t in T];
        
            assert IsMonic(P);
            b:=Coefficient(P,1);
            u:=Parent(P).1;
            P:=Evaluate(P,u-b/2);
            assert Coefficient(P,1) eq 0;
        end if;
        

    else
        // The alternate "Serre type" case

        G1,phi1:=ChangeRing(G0,Integers(N1));  assert G1 eq GL(2,Integers(N1));        
        G2,phi2:=ChangeRing(G0,Integers(N2));  
        // N1 and N2 are relative prime with product N.
        // We can view G0 as a subgroup of G1 x G2 that projects surjectively onto G1 and G2
        
        H1:=phi1(Kernel(phi2) meet B);
        H2:=phi2(Kernel(phi1) meet B);

        
        assert H1 subset G1 and H2 subset G2;
        assert Index(G1,H1) le 2 and Index(G2,H2) le 2;
        
        // Idea:  Since each Hi has index at most 2 in Gi, we will have a modular functions fi in Q(X_Hi) 
        // and Pi in Q(X_G0) such that fi^2=Pi and Q(X_Hi)=Q(X_G0)(fi).
        // The desired cover will then be of the form  y^2 = P1*P2
            
        // First H2
        if Index(G2,H2) eq 1 then
            P2:=1;
            f2:=[1: j in [1..M`vinf]]; 
        else
            N2:=gl2Level(H2);                   
            H2:=ChangeRing(H2,Integers(N2));            
            if N2 mod M0`N ne 0 then
                N2:=LCM([N2,M0`N]);
                H2:=gl2Lift(H2,N2);
            end if;
            
            M2:=CreateModularCurveRec0(H2);
            flag2,P2,f2:= FindCoverOfModularCurve(M0,M2,prec); 
            assert flag2;
            assert Coefficient(P2,1) eq 0;     
            P2:=-Evaluate(P2,0);
            f2:=ConvertModularFormExpansions(M, M2, [1,0,0,1], f2);
        end if;


        // Now H1
        N1:=gl2Level(H1);
        H1:=ChangeRing(H1,Integers(N1));
        if p eq 2 then
            assert 8 mod N1 eq 0;
            H1:=gl2Lift(H1,8);  
            N1:=8;
        else
            assert p eq 3 and N1 eq 3;
        end if;
        // H1=GL(2,Z/8Z) or GL(2,Z/3Z)

        if H1 meet SL(2,Integers(N1)) eq SL(2,Integers(N1)) then
            // Taking determinants, we have an index 1 or 2 subgroup of (Z/8Z)^* or (Z/3)^*;
            // it gives rise to an extension Q(sqrt(d))/Q of degree at most 2.    
            // The following just case by case gives d.
            S:= {Integers()!Determinant(h): h in H1};
            if p eq 2 then
                if   S eq {1,3,5,7} then d:=1; 
                elif S eq {1,5}     then d:=-1;
                elif S eq {1,3}     then d:=-2;
                elif S eq {1,7}     then d:=2;
                else assert false; end if;
            else    
                if   S eq {1,2} then  d:=1;
                elif S eq {1}   then  d:=-3;
                else assert false; end if;
            end if;
            K<z>:=CyclotomicField(N);
            _<x>:=PolynomialRing(K);
            a:=Roots(x^2-d)[1][1];
            P1:=d;
            
            // Combine the H1 and H2 cases together
            Pol<u>:=PolynomialRing(Parent(P2));
            P:=u^2 - P1*P2;  
            h:=[a*c: c in f2];  
            flag:=true;             
        else
            assert p eq 2;
            // H1 is now an index 2 subgroup of GL(2,Z/8Z) with full determinant
            // In this case, we have Q(X_H1)=Q(f), where f^2=d*(j-1728) for a unique integer d in {1,-1,2,-2}.
            // We find d by checking case by case.
            S:= {Integers()!Determinant(h): h in H1 | Order( ChangeRing(h,Integers(2)) ) in {1,3}};
            if   S eq {1,3,5,7} then d:=1; 
            elif S eq {1,5}     then d:=-1;
            elif S eq {1,3}     then d:=-2;
            elif S eq {1,7}     then d:=2;
            else assert false; end if;
            
            K<z>:=CyclotomicField(N);
            _<x>:=PolynomialRing(K);
            a:=Roots(x^2-d)[1][1];
            h:=[a*c: c in f2];  // a square root of d times f2 from the H2 case
            
            M_temp:=CreateModularCurveRec(2,[[1,1,1,0]]);
            _<q>:=LaurentSeriesRing(Rationals(),Maximum(2000,prec)); 
            v:=[(jInvariant(q^2 + O(q^(Maximum(200,prec))))-1728)^(1/2)]; 
            v:=ConvertModularFormExpansions(M, M_temp, [1,0,0,1], v); // a modular function with v^2=j-1728
            h:=[ h[j]*v[j] : j in [1..M`vinf]];

            if  not assigned M0`map_to_jline or simplify_serre_type eq false then
                if M0`genus eq 0 then
                    L<t>:=FunctionField(Rationals());
                else
                    L<x,y>:=FunctionField(M0`C);
                end if;
                Pol<u>:=PolynomialRing(L);
                return false, u^2-L!(d*P2), h;  // case where flag is false
            elif M0`genus eq 1 then
                L<x,y>:=FunctionField(M0`C);
                J:=M0`map_to_jline[1];
                J:=J([x,y,1]);
                J:=L!(J[1]/J[2]);
                Pol<u>:=PolynomialRing(L);
                P:= u^2-d*(J-1728)*L!P2; 
                flag:=true;
            else
                L<t>:=FunctionField(Rationals());
                J:=M0`map_to_jline[1];
                J:=J([t,1]);
                J:=L!(J[1]/J[2]);
                Pol<u>:=PolynomialRing(L);
                P:= u^2-d*(J-1728)*L!P2; 
                flag:=true;
            end if;

        end if;
    end if;

    //--------------------------------------------------

    // When the base curve X_G0 is P^1_Q we can try to make our model nicer.
    if flag and M0`genus eq 0 then
        R<t>:=PolynomialRing(Integers());
        L:=FieldOfFractions(R);
        Pol<u>:=PolynomialRing(L);
        Q:=Pol!P;
        d:=Degree(Q);
        assert IsMonic(Q);

        f:=ConvertModularFormExpansions(M, M0, [1,0,0,1], M0`f);
        LL<t>:=FunctionField(Rationals());
        phi:=LL!1;

        for i in [0..d-1] do
            c:=Denominator(Coefficient(Q,i));            
            FF:=Factorization(c);                
            for ff in FF do
                pi:=ff[1];
                e:= Ceiling(Valuation(c,pi)/(d-i));
                Q:=Pol!((pi^e)^d*Evaluate(Q,u/pi^e));
                phi:=phi * LL!pi^e;
            end for;            
        end for;

        Pol<u>:=PolynomialRing(R);
        Q:=Pol!Q;
        for ff in Factorization(Coefficient(Q,0)) do
            pi:=ff[1];        
            e:=Floor(Minimum([Valuation( Coefficient(Q,i) ,pi)/(d-i) : i in [0..d-1]]));
            Q:=Pol!( Evaluate(Q,u*pi^e)/(pi^e)^d );        
            phi:=phi/LL!pi^e;
        end for;

        v:=[Evaluate(phi,f[j]): j in [1..M`vinf]];
        h:=[h[j]*v[j]: j in [1..M`vinf]];
        P:=Q;

    end if;
    
    return flag, P, h;
end intrinsic;

intrinsic PointsViaLifting(psi::SeqEnum,p::RngIntElt,m::RngIntElt) -> SetEnum
{ Input:
            psi: a sequence of homogeneous polynomials in Z[x_1,...,x_r]
            p  : a prime
            m  : an integer at least one    
        Output:
            The set of points C(Z/p^m), where C is the subscheme of P^(r-1)_Q defined by psi.
}    
    r:=Rank(Parent(psi[1]));
    PolZ<[x]>:=PolynomialRing(Integers(),r);
    psi:=[PolZ!f: f in psi];

    PP:=ProjectiveSpace(GF(p),r-1);
    C:=Scheme(PP,psi);
    S:={Eltseq(P): P in Points(C)};   // points mod p
    S:={[Integers()!a: a in P]: P in S};

    e:=1;
    while e lt m do
        PP:=ProjectiveSpace(Integers(p^(e+1)),r-1);
        Snew:={};        
        for P in S do
            // For each point in C(Z/p^e), we find all possible lifts to C(Z/p^(e+1)).
            A:=[]; b:=[];
            Pol<[a]>:=PolynomialRing(Integers(),r);
            for f in psi do
                pol:=Evaluate(f,[P[i]+p^e*a[i]: i in [1..r]]);
                A:=A cat [[MonomialCoefficient(pol,a[i]) div p^e : i in [1..r]]];
                b:=b cat [ -MonomialCoefficient(pol,1) div p^e ];
            end for;
            A:=ChangeRing(Matrix(A),GF(p));
            b:=ChangeRing(Vector(b),GF(p));
            flag,v,W:=IsConsistent(Transpose(A),b);
            if flag then 
                T:={Eltseq(v+w): w in W};
                T:={[Integers()!a: a in w] : w in T};
                T:={ [P[i]+p^e*w[i]: i in [1..r]] : w in T};
                T:={PP!w: w in T}; 
                Snew:=Snew join T;
            end if;
        end for;
        S:={Eltseq(P): P in Snew};
        S:={[Integers()!a: a in P]: P in S};
        e:=e+1;
    end while;

    S:={[Integers(p^m)!a: a in P] : P in S};
    return S;
end intrinsic;

intrinsic FindSerreTypeModel(M0::Rec, M::Rec, prec::RngIntElt) -> Rec
{
        Input:
                M0, M:  records of type "ModularCurveRec" corresponding to modular curve X_G0 and X_G, respectively, where
                        G0:=M0`G and G:=M`G.  We assume that X_G0 is isomorphic to P^1_Q (in particular, M0`C and M0`f are defined).

                        We assume that G is a subgroup of GL(2,Z/N) with full determinant.  We also assume that 
                        N is even and not a power of 2, and that N is the level of G.

                        Let m be the largest odd number dividing N.  We assume that G0 is the image of G modulo m.
                        When G0 is lifted mod N, we assume that G gives an index 2 subgroup of G0.
                                            
                prec:   a postive integer used to specify how many terms of q-expansions to compute            

        Output:                
                We find an explicit hyperelliptic curve C0 defined over Q that gives a model of X_G.   
                We return the record M corresponding to the modular curve X_G with the following entries updated:

                    psi:   a sequence consisting of the equation for the hyperelliptic curve C0
                    F0:    a triple of elements in Q(X_G) that satisfy our equation for C0; it gives an explicit isomorphism X_G->C0
                    
                If X_G has genus 0 or X_G has genus 1, we also compute
                    has_point:  true if and only if X_G has a Q-point.
                    has_infinitely_many_points:  true if and only if X_G has infinitely many Q-points

                If X_G is genus 0 and has a Q-point, we also compute
                    f:  a generators of the function field of X_G, i.e., Q(X_G)=Q(f); it is given by q-expansions 
                        at the cusps
                    C:  the curve P^1_Q (note that f defines an isomorphism between X_G and C)

                If X_G is genus 1 and X_G has a Q-point, we also compute
                    f=[x,y]:  we have Q(X_G)=Q(x,y), where x and y satisfy a Weierstrass equation; they
                              are given by q-expansions at the cusps.
                    C:  an elliptic curve over Q given by the Weierstrass equation that x and y satisfy.

                When X_G has genus at most 1 and we have found a point, we also compute
                    phiC:  a sequence of polynomials that defines an isomorphism C0->C                                    
}
    assert M0`genus eq 0;

    flag, P, h := FindCoverOfModularCurve(M0,M,prec);    
    assert flag;
    P:=-Evaluate(P,0);  // will be polynomial in Z[x];  our covering given by y^2 = P(x).
    
    // We thus have a hyperelliptic model of X_G
    C0:=HyperellipticCurve(P);

    R<x,y,z>:=PolynomialRing(Rationals(),3);
    M`psi:=[R!DefiningEquation(C0)];

    f:=ConvertModularFormExpansions(M, M0, [1,0,0,1], M0`f); 
    F:=[ f, h, [1:j in [1..M`vinf]] ];        
    M`F:=F;
    M`F0:=F;

    if Genus(C0) gt 1 then
        M`has_infinitely_many_points:=false;  // Faltings
        return M;
    end if;


    // Warning: There are some issues with Magma's implementation of hyperelliptic curves and weighted space when C0 has genus 1.
    // C0 is a curve in weighted projective space P(1,2,1).   The hyperelliptic curve C1 below is in P(1,1,2).
    // Magma's function "Points" is implemented for P(1,2,1) but not P(1,1,2)!  The following ad hoc function deals with these
    // minor incompatibilities.

    function Points0(Z)
        grading:=Gradings(Z)[1];
        if grading eq [1,2,1] then return Points(Z); end if;
        assert grading eq [1,1,2];
        PP<x,y,z> := ProjectiveSpace(Rationals(),[1,2,1]);
        Z1:=Scheme(PP, [Evaluate(f,[x,z,y]): f in DefiningPolynomials(Z)]);
        S:=Points(Z1);
        S:={Eltseq(P): P in S};
        S:={Z![P[1],P[3],P[2]]: P in S};
        return S;        
    end function;


    if M`genus eq 1 then
        C:=GenusOneModel(C0);

        if not IsLocallySoluble(C) then
            M`has_point:=false;
            M`has_infinitely_many_points:=false;
            return M;
        end if;
        
	    C1,E,maptoE:=nCovering(C); 
        n:=2;
            
        // This is a degree n^2 cover C->E and E is isomorphic to the Jacobian of C; 
        // it is a twist of multiplication by n map E->E.
        // In particular, if C has a rational point, then the image of C(Q) in E will be a coset of nE(Q).

		A,f0:=MordellWeilGroup(E);
	    r:=TorsionFreeRank(A);    
		if r eq 0 then
			// C has finitely many points which we can find
		    pts:={};
    		for a in A do 
    		    preimage := Pullback(maptoE, f0(a));       
    		    pts:=pts join {p: p in Points0(preimage)};
	        end for;
            M`has_point:=#pts ge 1;
	    else
			// Curve has either infinitely many points or no points.
		    Q,iota:=quo<A|{n*a: a in Generators(A)}>;
	        pts:={};
		    for q in Q do
			    P:=f0(q @@ iota);
		        preimage := Pullback(maptoE, P);
		        pts:=pts join {p: p in Points0(preimage)};
			    if #pts ge 1 then break q; end if;
		    end for;                    
        	M`has_point:=#pts ge 1;
		end if;

        if M`has_point eq false then
            M`has_infinitely_many_points:=false;
            return M;
        end if;

        // Our genus 1 curve C0 has a rational point P0
        pts:={Eltseq(P): P in pts};
        pts:=[C0![P[1],P[3],P[2]]: P in pts];
        _,i:=Minimum([HeightOnAmbient(P):P in pts]);
        P0:=pts[i];

        E0,pi0:=EllipticCurve(C0,P0);
        E,pi1:=MinimalModel(E0);
        pi:=Expand(pi0*pi1);  // Isomorphism C0->E sending P0 to 0.

        Pol<[x]>:=PolynomialRing(Rationals(),3);
        W:=DefiningEquations(pi);
        W:=[Pol!a: a in W];
    
        c:=[  [Evaluate(pol,[f[j]:f in F]) : j in [1..#M`cusps]] : pol in W];
        x:=[c[1][j]/c[3][j]: j in [1..#M`cusps]];  
        y:=[c[2][j]/c[3][j]: j in [1..#M`cusps]];
        // Not checking that c[3][j] not weakly zero, need to increase precision if errors arise.
 
        //M`phiC:=W;
        M`f:=[x,y];
        M`C:=E;
        M`has_infinitely_many_points:=Rank(E) ge 1;

        // check
        assert &and[ &and[IsWeaklyZero( Evaluate(f,[x[j],y[j],1]) ): j in [1..M`vinf]] : f in DefiningEquations(E)];
        return M;
    end if;
   
    // Remaining case is when X_G has genus 0
    assert M`genus eq 0;

    C1,f1:= Conic(C0);        
    b,p1:=HasRationalPoint(C1);
    M`has_point:=b;
    M`has_infinitely_many_points:=b;
    if M`has_point eq false then    
        return M;
    end if;

    // The modular curve is isomorphic to P^1_Q
    P1<x,y>:=Curve(ProjectiveSpace(Rationals(),1));
    f2:=Parametrization(C1,P1);    // f2: P1 \to C1
    phi:=Expand(f2*Inverse(f1));   // isomorphism P1->C0 

    W:=DefiningEquations(Inverse(phi));
    Pol<[x]>:=PolynomialRing(Rationals(),3);
    W:=[Pol!w: w in W];
		
    // We compute a hauptmodul, i.e., a function f that generates the function field of the modular curve over Q.
    ff:=[];
    for j in [1..#M`cusps] do 
		a:=[f[j]: f in F];
	    hh:=[Evaluate(w,a): w in W];
        h:=hh[1]/hh[2];   // Warning:  Not checking if hh[2] is not weakly zero; need to increase precision if issues arise.
	    ff:=ff cat [h];                
	end for;
    M`f:=ff; 
    M`C:=P1;    
    //M`phiC:=W;        
        
    return M;
end intrinsic ;

intrinsic MapTojLine(X::SeqEnum,k::.) -> .
{
        Input:  Let X be an associative array of modular curves that, except for the j-line, map down to a smaller degree modular curve.
                Let k be a key of X corresponding to a modular curve.
        Output: 
                The morphism from our explicit model X[k]`C of the modular curve with key k to the j-line P^1_Q.
}
    J:=IdentityMap(X[k]`C);
    
    while X[k]`degree ne 1 do
        b:=X[k]`pi[1];
        psi:=X[k]`pi[2];
        phi:=map< X[k]`C->X[b]`C | psi >;
        J:=J*phi;  // note: composition backwards in Magma
        k:=b;
    end while;

    return J;
end intrinsic;

intrinsic AutomorphismOfModularForms(M::Rec, F::SeqEnum, g::GrpMatElt : wt:=0) -> GrpMatElt
{  Input:
            M   :a record for a modular curve X_G with G a subgroup of GL(2,Integers(N)) with full determinant
            F   :linearly independent elements in M_k,G for some k>1
            g   :a matrix in GL(2,Z/N) that acts on the span V of F over the complex numbers
            wt  :an integer congruence modulo 2 to k.
        Output:          
            a matrix C that describes the action of g on V with respect to the basis F  (it will always have coefficients in Q(zeta_N))
            Since g acts on the right, we take C so that    F[j]*g = sum_i  C[j,i]*F[i]
}

    // By multiplying by an element of G, we may assume that g has determinant 1
    g:=GL(2,Integers(M`N))!g;
    if Determinant(g) ne 1 then
        assert exists(h){h: h in M`G | Determinant(h) eq Determinant(g)};
        g:=h^(-1)*g;
        assert Determinant(g) eq 1;
    end if;
    g:=LiftMatrix(g,1);  // lift g to matrix in SL(2,Z)

    // g takes F to Fnew
    Fnew:=[];
    for f in F do
        fnew:=ConvertModularFormExpansions(M, M, g, f : wt:=wt);
        Fnew:=Fnew cat [fnew];
    end for;

    K:=CyclotomicField(M`N);
    P<[a]>:=PolynomialRing(K,#F);
    R<q>:=PuiseuxSeriesRing(P);

    A0:=[];
    b:=[];
    r:=0;
    for j in [1..M`vinf] do

        h:=&+[a[i]*R!F[i][j]: i in [1..#F]];
        repeat
            v:=Valuation(h);
            c:=Coefficient(h,v);
            h:=h-c*q^v;

            A1:=A0 cat [ [ MonomialCoefficient(c,a[i]): i in [1..#F] ] ];
            A:=Matrix(A1);
            if Rank(A) gt r then
                A0:=A1;
                r:=Rank(A);
                b:=b cat [[K!Coefficient(f[j],v): f in Fnew]];
            end if;
        until IsWeaklyZero(h) or r eq #F;
        if r eq #F then break j; end if;
    end for;
    
    A:=Matrix(A0);
    
    C:=[];
    for i  in [1..#F] do
        b0:=Vector([c[i]: c in b]);
        flag,v,W:=IsConsistent(Transpose(A),b0);
        assert flag and Dimension(W) eq 0;
        C:=C cat [Eltseq(v)];
    end for;
    C:=Matrix(C);

    if exists{c: c in Eltseq(C) | c notin Rationals()} eq false then
        C:=ChangeRing(C,Rationals());  // coerce to rational numbers when possible
    end if;


    // checks
    for j in [1..#F] do
        assert IsWeaklyZero(Fnew[j][1] - &+[C[j,i]*F[i][1] : i in [1..#F]]);
    end for;
    C:=Transpose(C);
    

    return C;
end intrinsic;


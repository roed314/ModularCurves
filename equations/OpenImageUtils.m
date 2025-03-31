// These intrinsics were extracted from David Zywina's OpenImage repository when it was replaced by the new Modular repository, since they were still being used.

intrinsic FindCuspPair(M::Rec, A::GrpMatElt) -> SeqEnum, RngIntElt
{}
    /* Consider a modular curve M=X_G given by a subgroup G of GL_2(Z/NZ).
       Let H be the intersection of G with SL(2,Z/NZ).

       Input:   a matrix A in SL(2,Z/NZ).
       Output:  a pair of integers [i,j] and an e in {1,-1} such that A and e*cusps[i]*[1,1;0,1]^j lie in the same coset H\SL(2,Z/NZ),
                    where cusps[i] is the fixed matrix describing the i-th cusp of M.   When G contains -I, we always return e=1.
    */

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

intrinsic FindRelationElliptic(M::Rec, f::SeqEnum) -> BoolElt, Any
{}
    /* Input:
                M:  a record M type "ModularCurveRec" (for example produced as output of CreateModularCurveRec) that
                    corresponds to a modular curve X_G.
                    We assume that X_G is an elliptic curve and that M`f=[x,y], where Q(X_G)=Q(x,y) and the meromorphic
                    functions x and y on X_G satisfy a Weierstrass equation over Q given by the elliptic curve E:=M`C
                    [ x and y are given by q-expansions at the cusps and in special cases will be produced by
                    the function "FindModelOfXG"].
                f:  An element of Q(X_G).   We assume that all the poles of f occur at cusps or that that the values it
                    takes at cusps are distinct from the values it takes at noncuspidal points.
    Output:
            A boolean, whether we were successful
            A rational function phi in Q(E)=Q(x,y) so that phi(x,y)=f.
    */

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
            return true, c;
        end if;

        // otherwise use assumption on j to force only poles at cusps
        f:=[1/(f[j]-c): j in [1..vinf] ];
        success, u:=FindRelationElliptic(M,f);
	if not success then return false, _; end if;
        return true, 1/u+Parent(u)!c;
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
	else
	    if Valuation(f[i]) eq -e then
		// Need more terms in q-expansion
		return false, _;
	    end if;
        end if;

        // We now subtract from f polynomials in x1 and y1 so that at the i-th cusp we either have a pole of
        // order 1 or a zero.
        while Valuation(f[i]) le 0 and Valuation(f[i]) ne -e do
	    if IsWeaklyZero(f[i]) then
		// Need more terms in q-expansion
		return false, _;
	    end if;
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
        return true, Evaluate(Pol!Numerator(phi0),[x,y,1])/Evaluate(Pol!Denominator(phi0),[x,y,1]);
    end if;

    return true, phi;
end intrinsic;

//Code by Rakvi


function H90(n,L,K,G,sigma,xi)   

 // Input: xi: G=Gal(L/K)-> GL(n,L) 1-cocycle.   
// Output: matrix A in GL(n,L) such that xi_g = A^(-1) g(A) for all g in G. 
// Also contains a commented code to perform LLL on A obtained.

    V := VectorSpace(L,n); 
    B1:=Basis(L);  // Warning: assuming K is base field of L 
    B2:=Basis(V);  
    B:=[b*v: b in B1, v in B2]; 
    S:={}; 

 

    i:=1; 
    while Dimension(sub<V|S>) ne n do 

 

        v:=B[i]; 
        tr:=&+[ xi(g)*Matrix(L,n,1,[sigma(g)(v[i]): i in [1..n]]) : g in G] / #G; 
        tr:=V!Transpose(tr); 
        if Dimension(sub<V|S join {tr}>) gt Dimension(sub<V|S>) then 
          S:=S join {tr}; 

        end if; 
        i:=i+1; 
    end while; 
    A0:=Transpose(Matrix([ ElementToSequence(v) : v in S ])); 
    A:=A0^(-1); 

 

    // LLL of A to make the maps look nicer! If the user wants to use this feature, just uncomment the code.
    /*AQ:=[];
    for i in [1..n] do;
    for j in [1..n] do;
        AQ:= AQ cat Eltseq(A[i,j]);
    end for;
    end for;
    AQ:=Matrix(K,n,n*Degree(L),AQ);
    Latt:=LLL(AQ);

    Ared:=[];
    for i in [1..n] do;
        for j in [1..n] do;
        Ared:= Ared cat [L![Latt[i,k]: k in [(Degree(L)*(j-1)+1)..Degree(L)*j]]];
    end for;
    end for;
    Ared:=Matrix(L,n,n,Ared);*/




    // Check:

    for g in G do

        gA:=Matrix([ [sigma(g)(A[i,j]):j in [1..n]] : i in [1..n]]);

        assert A^(-1)*gA eq xi(g); 

    end for;

    
    return A;
 

end function; 
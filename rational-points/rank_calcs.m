///////////////////
/// simple_rank ///
///////////////////

// Input : A
// A is a simple modular abelian variety that appears as a factor of J_0(N)

// Ouput : Rank(A), tf
// Rank(A) and whether this is provably true.
// If the second output is false then Rank(A) will be -1000

simple_rank := function(A);
    tf := true;
    if Dimension(A) eq 0 or IsZeroAt(LSeries(A),1) eq false then
       rk := 0;
    else M := ModularSymbols(Newform(A));
         _,ord_vanishing := LSeriesLeadingCoefficient(M,1,100);
         if ord_vanishing eq 1 then
            rk := Degree(HeckeEigenvalueField(M));
         else if Dimension(A) eq 1 then   // we have an elliptic curve and we try to compute the rank directly
                 E := EllipticCurve(A);
                 rk,ell_tf := Rank(E);
                 assert ell_tf eq true;
              else rk := -1000;
                   tf := false;
              end if;
          end if;
    end if;
    return rk, tf;
end function;

////////////////////////////////////////////////////
////////////////////////////////////////////////////

///////////////////
/// rank_J0N_wd ///
///////////////////

// Input: N, d
// Ouput: Rank(J_0(N)) / w_d, tf
// Rank and whether it is provably true
// If the second output is false then Rank(J_0(N)) will be -1000

// if you want to compute the rank of J_0(N) then set d = 1


rank_J0N_wd := function(N,d);
    J := JZero(N);
    wd := AtkinLehnerOperator(J,d);
    Jwd := ConnectedKernel(1-wd);    
    dec := Decomposition(Jwd);
    rk := 0;
    tf := true;

    for A in dec do
        rkA, Atf := simple_rank(A);
        if Atf eq false then  // cannot compute rank with simple_rank
           rk := -1000;
           tf := false;
           break;
        else rk := rk + rkA;
        end if;
     end for;

     return rk, tf;
end function;
     

////////////////////////////////////////////////////
////////////////////////////////////////////////////
      
//////////////////
/// equal_rank ///
//////////////////



// Input: N, d.
// N is the level
// d is the index of the Atkin-Lehner involution

// Output: true true, false true, or false, false

// true true if the ranks of J_0(N) and J_0(N) / w_d are equal and this is provably correct
// false true if the ranks of J_0(N) and J_0(N) / w_d are not equal and this is provably correct
// false false if we cannot verify whether or not the ranks of J_0(N) and J_0(N) / w_d are equal

// This code provides an alternative way of checking the equality of ranks. 
// It is of course possible to compute the rank of J0N and the quotient using the code above and checking whether they are equal.
// This code works with the minus eigenspace of w_d, so may work even if computing the ranks separately fails 
// (but not vice-versa, if this code fails then computing the rank of J0N will also fail)

equal_rank := function(N,d);
    J := JZero(N);  
    wd := AtkinLehnerOperator(J,d);
    Jwd_min := ConnectedKernel(1+wd);  // The minus eigenspace of wd
    dec := Decomposition(Jwd_min);

    for A in dec do  // simple factors of minus part
        rkA, tfA := simple_rank(A);
        if rkA gt 0 and tfA eq true then // there is a positive rank factor in Jwd_min
           return false, true;
        elif tfA eq false then 
           return false, false;
        end if;
    end for;
    return true, true;
end function;

/*
// A few examples

rank_J0N_wd(74,1); // 2 true. So the rank of J_0(74) is 2
rank_J0N_wd(74,74); // 1 true. So the rank of J_0+(74) is 1
rank_J0N_wd(74,37); // 2 true.
rank_J0N_wd(74,2); // 1 true.

equal_rank(74,74); // false true
equal_rank(74,37); // true true
equal_rank(74,2); // false true

//////// 

rank_J0N_wd(389,1); // 13 true. So the rank of J_0(389) is 13.
rank_J0N_wd(389,389); // 11 true. So the rank of J_0+(389) is 11.
equal_rank(389,389); // false true

for A in Decomposition(JZero(389)) do
    simple_rank(A);   // ranks are 2,2,3,6,0. All true.
end for;

////////

rank_J0N_wd(13,1); // 0 true  
rank_J0N_wd(1,1); // 0 true  


//testing for variuos levels and divisors of levels:
for N:= 1 to 200 do
	S:=Divisors(N);
	for d in S do 
		if GCD(d, Integers()!(N/d)) eq 1 then
			print [N,d], equal_rank(N,d), rank_J0N_wd(N,d);
		end if;
	end for;
end for;
*/




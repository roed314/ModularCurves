lift_mat := function(a,n)
  // Given a in SL_2((Z/nZ), it lifts it to a matrix in SL_2(Z))
  // Code by Claudio Stirpe
  ZZ:=Integers();
  b:=Matrix(ZZ,2,2,[a[1,1],a[1,2],a[2,1],a[2,2]]);
  i1:=b[1,1];
  i2:=b[2,1];
  // make the first column not multiple of anything
  while not IsCoprime(i1,i2) do
    i2:=i2+n;
    if not IsCoprime(i1,i2) then
      i1:=i1+n;
    end if;
  end while;
  // use Bezout
  b:=Matrix(ZZ,2,2,[i1,b[1,2],i2,b[2,2]]);
  k1,k2,k3:=XGCD(i1,i2);
  determ:=Determinant(b);
  
  b[2,2]:=b[2,2]+(1-determ)*k2;
  b[1,2]:=b[1,2]-(1-determ)*k3;
  return b;
end function;


lift_mat_with_det := function(a,n)
  /* Given a 2x2 matrix a, to be considered modulo n, with determinant d it does the following:
    - if the entries of a, modulo n, are not coprime, returns 0
    - if the smallest positive lift of d modulo n is a divisor of n, it lifts a to a matrix with coefficients in Z and determinant gcd(n,a)
    - otherwise it returns 0
  */
  ZZ:=Integers();
  b:=Matrix(ZZ,2,2,[a[1,1],a[1,2],a[2,1],a[2,2]]); // naive lift
  // check coprimality of entries mod n
  if not(GCD([b[1,1],b[1,2],b[2,1],b[2,2], n]) eq 1) then  
    return 0;
  end if;
  // check if the goal determinant is achievable
  d_target := GCD(Determinant(b),n);
  if not ((d_target mod n) eq (Determinant(b) mod n)) then
    return 0;
  end if;
  S,U,P:=SmithForm(b);
  k1,k2,k3:=XGCD(S[1,1],S[2,2]);
  l:=d_target-Determinant(b);
  S_tilde:=Matrix(ZZ,2,2,[[S[1,1]+k3*l, -k2*l],[-k3*l,S[2,2]+k2*l]]);
  return P*S_tilde*U;
end function;



GLn_to_SLZ := function(H,n)
  // given H a subgroup of GL_2(Z/nZ), it returns the lift modulo n^2 of H\cap(SL_2(Z/nZ)), namely the inverse image of H under the map SL_2(Z/n^2Z) --> GL_2(Z/nZ)
  ZZ:=Integers();
  HSL:=H meet SpecialLinearGroup(2,Integers(n));
  SL_n2:=SpecialLinearGroup(2,Integers(n^2));
  gens := Generators(HSL);
  new_gens := []; // we first add the (lift) of generators of H \cap SL_2 and then we add the generators of the kernel SL_2(Z/n^2Z) --> SL_2(Z/nZ) 
  for x in gens do 
    Append(~new_gens, lift_mat(x,n));
  end for;
  Append(~new_gens, Matrix(ZZ,2,2,[1,n,0,1]));
  Append(~new_gens, Matrix(ZZ,2,2,[1,0,n,1]));
  Append(~new_gens, Matrix(ZZ,2,2,[1-n,n,-n,1+n]));
  return new_gens;
end function;

is_in_normalizer:=function(m,H,gens,n)
  // given a matrix m, with coefficients in Z or Q, given H a subgroup of GL_2(Z/nZ), given gens a list of matrices of SL_2(Z), it checks if m*g*m^(-1) (mod n) belongs to H for every g in gens
  ZZ:=Integers();
  G:=GeneralLinearGroup(2,Integers(n));
  GLQ:=GeneralLinearGroup(2,Rationals());
  for g in gens do
    mtest:=GLQ!(m*g)*GLQ!(m)^(-1);
    if not(mtest[1,1] in ZZ) or not(mtest[1,2] in ZZ) or not(mtest[2,1] in ZZ) or not(mtest[2,2] in ZZ) then
      return false;
    end if;
    if not (G!mtest) in H then
      return false;
    end if; 
  end for;
  return true;
end function;


check_new:=function(mm,list,H,n)
  // given m a matrix in GL_2(Q) and list a list of matrices in GL_2(Q) and H a subgroup of GL_2(Z/nZ), it checks whether m is in Gamma_H*list
  ZZ:=Integers();
  G:=GeneralLinearGroup(2,Integers(n));
  GLQ:=GeneralLinearGroup(2,Rationals());
  for m in list do
    mtest:= GLQ!mm*((GLQ!m)^(-1));
    if (mtest[1,1] in ZZ) and (mtest[1,2] in ZZ) and(mtest[2,1] in ZZ) and(mtest[2,2] in ZZ) and (Determinant(mtest) eq 1) and (G!mtest in H) then
      return false;
    end if;
  end for;
  return true;
end function;


//////////////////////////////////////////////
////////// IS H IN A BOREL MODULO P? OR MORE?
//////////////////////////////////////////////

stable_lines:=function(H,p)
  // given a subgroup H of GL_2(Z/NZ) and a prime divisor p of N, it looks for the possible lines in (F_p)^2 that are left stable by H
  Fp:=Integers(p);
  gens := Generators(H);
  gens_p:=[];
  for x in gens do 
    temp:= ChangeRing(x,Fp);//Matrix(Fp,2,2,[x[1,1],x[1,2],x[2,1],x[2,2]]);
    if not IsScalar(temp) then
      Append(~gens_p, temp);
    end if;
  end for;
  // check if H mod p only containes scalar matrices: in this case every line is invariant
  if #gens_p eq 0 then
    return "ALL";
  end if;
  // look for the lines that are stable by the first generator
  M:=gens_p[1];
  lams :=Eigenvalues(M);
  possible_lines:=[];
  for lam in lams do
    Append(~possible_lines, Eigenspace(Transpose(M),lam[1]));
  end for;
  // check whether the possible lines are stable for all H
  answer:= [**];
  for line in possible_lines do
    flag:=true;
    v:=Basis(line)[1];
    for N in gens_p do
      w:=v*Transpose(N);
      if not w in line then flag:=false; end if;
    end for;
    if flag then Append(~answer, v); end if;
  end for;
  return answer;
end function;

Borelize:=function(H,livello)
  /* Given a subgroup H in GL_2(Z/livello) it returns a list [* H', m, [<p_1, type_1>,...,<p_k, type_k>] *]
  where:
  > H' = m*H*m^(-1)  
  > H is contained in a Borel (sometimes even a Cartan) modulo p_i and H' is contained in the standard Borel or Cartan (namely upper triangular or diagonal matrices)
  > type_k is either "Borel", "Cartan" or "Scalar" and detects what happens modulo p_i
  */
  ZZ:=Integers();
  bad_ps:=[];
  bad_eigenvecs:=[];
  for p in PrimeDivisors(livello) do 
    lines:=stable_lines(H,p);
    if #lines eq 1 then
      Append(~bad_ps, <p, "Borel">);
      if lines[1][1] eq 0 then 
        Append(~bad_eigenvecs, Transpose(Matrix(ZZ,2,2,[[lines[1][1],lines[1][2]], [1,0]])));
      else
        Append(~bad_eigenvecs, Transpose(Matrix(ZZ,2,2,[[lines[1][1],lines[1][2]], [0,1]])));
      end if;
    elif #lines eq 2 then
      Append(~bad_ps, <p, "Cartan">);
      Append(~bad_eigenvecs, Transpose(Matrix(ZZ,2,2,[[lines[1][1],lines[1][2]], [lines[2][1],lines[2][2]]])));
    elif #lines eq 3 then
      Append(~bad_ps, <p, "Scalar">);
      Append(~bad_eigenvecs,  Transpose(Matrix(ZZ,2,2,[[1,0],[0,1]])));
    end if;
  end for;
  // find the matrix to conjugate by. We obtain it from the matrices we have stored using Chinese Remainder Theorem 
  m := Matrix(ZZ,2,2,[[1,0],[0,1]]);
  prod_ps:=1;
  for i in [1,2] do
  for j in [1,2] do
    prod_ps:=1;
    CRT1:=[];
    CRT2:=[];
    for k:=1 to #bad_ps do
      Append(~CRT1, bad_eigenvecs[k][i,j]);    
      Append(~CRT2, bad_ps[k][1]);   
      prod_ps:=prod_ps*bad_ps[k][1]; 
    end for;
    if not #CRT1 eq 0 then
      m[i,j]:=ChineseRemainderTheorem(CRT1,CRT2);
    end if;
  end for;
  end for;
  // adjusting the determinant and lifting to Z
  m:=ChangeRing(m,Integers(prod_ps));
  temp:=Determinant(m);
  m[1,1]:=m[1,1]/temp;  m[2,1]:=m[2,1]/temp;
  m:=lift_mat(m,prod_ps);
  // base change
  gens:= Generators(H);
  new_gens:=[];
  temp:=ChangeRing(m,Integers(livello));
  for x in gens do
    Append(~new_gens, temp^(-1)*x*temp);
  end for;
  GL:=GeneralLinearGroup(2,Integers(livello));
  HH:=sub<GL|new_gens>;
  return [* HH, m, bad_ps *];
end function;




//////////////////////////////////////////////
////////// MAIN FUNCTION
//////////////////////////////////////////////



ModularAUT:=function(H,livello) 
  /* Given a subgroup H in GL_2(Z/livello) it returns three lists of representatives in PGL_2^+(Q) with coprime integer entries of the elements of the following sets:
  > normaliz that is a list of the elements of the modular automorphism group of X_H (these are the elements obtained by the products among the elements of the two following outputs)
  > normaliz_bor that is a list of Atkin-Lehner elements of the modular automorphism group of X_H
  > lifted_HNelements that is a list of the elements of N'/H' where H' = H\cap SL_2 and N' is the normalizer of H' in SL_2
  */
  ZZ:=Integers();
  SL:=SpecialLinearGroup(2,Integers(livello));
  HSL:=H meet SL; // this is better than H

  // find normlizer in SL_2(Z), which is the same as in SL(Z/livello) 
  HN:=Normalizer(SL, HSL);
  gen_H_Z:=GLn_to_SLZ(H,livello);
  HNelements:=[];
  QHN,phi:=quo<HN|Generators(HSL)>;
  for M in QHN do
    HNelements:=Append(HNelements,M@@phi);
  end for;
  lifted_HNelements:=[];
  for M in HNelements do
    lifted_HNelements:=Append(lifted_HNelements,lift_mat(M,livello));	
  end for;

  // "Borel form" and maximal determinant of a modular automorphism
  Borel_info:=Borelize(H,livello);
  H_bor:=Borel_info[1];
  HSL_bor:=H_bor meet SL;
  gen_H_Z_bor:=GLn_to_SLZ(H_bor,livello);
  HN_bor:=Normalizer(SL, HSL_bor);
  bad_ps:=Borel_info[3];
  if #bad_ps eq 0 then 
    return lifted_HNelements;
  end if;
  cartan_ps:=[];
  scalar_ps:=[];
  borel_ps:=[];
  max_det:=1;   // the determinant can be only be divided by the primes that borelize
  for p in bad_ps do
    pp:=p[1];
    max_det:=max_det*pp^(Valuation(livello,pp));
    if p[2] eq "Cartan" then Append(~cartan_ps, pp); 
    elif p[2] eq "Scalar" then Append(~scalar_ps, pp); 
    else Append(~borel_ps, pp); 
    end if;
  end for;

  // Try all the matrices (a_ij) that maybe are in the normalizer
  normaliz_bor:= [Matrix(ZZ,2,2,[[1,0],[0,1]])];
  for d in Divisors(max_det) do // choosing determinat of (a_ij)
    Borel_part:=1; // the primes of Borel type in d must divide all a_ij, except a_12. The product of them is Borel_part 
    for p in borel_ps do 
		  if d mod p eq 0 then 
			  Borel_part:=p*Borel_part; 
			end if; 
		end for; 
    Cartan_part:=1; // the primes of Cartan type in d must divide the diagonal. The product of them is Cartan_part
    for p in cartan_ps do 
		  if d mod p eq 0 then 
			  Cartan_part:=p*Cartan_part; 
			end if; 
		end for;
    // next we choose a_11, a_21, a_22, then we "find" a_12 knowing the determinant  
    for i11:=0 to ZZ!((livello*d)/(Borel_part*Cartan_part)-1) do
      a11:=Borel_part*Cartan_part*i11;
      for i22:=0 to ZZ!((livello*d)/(Borel_part*Cartan_part)-1) do
        a22:=Borel_part*Cartan_part*i22;
        Borel_c:=1; 
				for p in borel_ps do 
				  if d mod p eq 0 then 
					  Borel_c:=Borel_c*p^(Valuation(a11*a22-d,p)); 
					end if; 
				end for;  // this will contain the part of Borel primes that are in a_21
        for i21:=0 to Ceiling((livello*d)/Borel_c-1) do 
          a21:=Borel_c*i21;
          // try to construct a_12 = (a_11*a_22-d)/a_21 modulo livello*d. 
          antidiag:=a11*a22-d; // ideally a12*a21
          if IsDivisibleBy(GCD(antidiag,livello*d),GCD(a21,livello*d)) and (GCD(i21,Borel_part) eq 1) then //first we check that, modulo livello*d, there is divisibility and that a_12 won't be divisible by Borel primes
            bad_21:=GCD(Borel_c*i21,livello*d);
            info_12:=ZZ!(livello*d/bad_21);  // we can only know a_12 modulo this guy. Next we find a_12 modulo info_12 
            if info_12 eq 1 then 
              first_a12:=0;
            else
              temp21:=ZZ!(Borel_c*i21/bad_21);
              temp_antidiag:=ZZ!(antidiag/bad_21);
              first_a12:=ZZ!(temp_antidiag*Integers(info_12)!(temp21)^-1);
            end if;
            // next choose all possible a_12 and check the matrix
            for counter_12:=0 to bad_21 do
              a12:=first_a12+counter_12*info_12;
              new_mat:= lift_mat_with_det([[a11,a21],[a12,a22]],livello*d);
              if (not new_mat eq 0) and (is_in_normalizer(new_mat,H_bor,gen_H_Z_bor,livello)) and check_new(new_mat, normaliz_bor,HN_bor,livello) then       
                Append(~normaliz_bor,new_mat);
              end if;
            end for; // possible a12
          end if; // exsistence of a12
        end for; // i21
      end for; // i22
    end for; // i11
  end for; // d
  normaliz:=[];
  basis_change:=Borel_info[2];
  for M in normaliz_bor do
    new_M := basis_change^(-1)*M*basis_change;
    for x in lifted_HNelements do
      Append(~normaliz, x*new_M );
    end for;
  end for;
  return normaliz,normaliz_bor,lifted_HNelements;
end function;





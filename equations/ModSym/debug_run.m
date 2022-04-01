AttachSpec("ModCrv.spec");
SetVerbose("ModularCurves", 1);

import "Box.m" : coeffs_by_zeta,
	       compute_ms_action,
       compute_newforms,
       create_character,
       createFieldEmbeddings,
       get_aut_extensions,
       get_gamma_fixed_space,
       get_gens,
       get_old_spaces,
       make_real_twist_orbit,
       Pdmatrix,
       precisionForCurve,
       prepare_character_representatives,
       restrict_to_character_reps;

function label2grp(label)
    level := StringToInteger(Split(label, ".")[1]);
    gens := [StringToInteger(x) : x in Split(Read("input_data/" * label), ",")];
    // Should be a list of 2x2 matrices, so number of elements divisible by 4.
    assert #gens mod 4 eq 0;
    gens := [gens[4*(i-1)+1..4*i] : i in [1..#gens div 4]];
    G := sub<GL(2, Integers(level)) | gens>;
    return GetRealConjugate(G);
end function;

function get_init_data(G)
    N := Modulus(BaseRing(G));
    PG := PSL2Subgroup(G);
    prec, max_deg := precisionForCurve(PG);
    AtkinLehner := [];
    Chars := [];
    wt := 2;
    eps := create_character(G, Chars);
    gens, Bgens, K, M, ds := get_gens(G, eps);
    MS, C, gs, Bmats, eps_gens, eps_BPd_gens :=
	compute_ms_action(G, eps, gens, Bgens, K, M, ds,
			  AtkinLehner : wt := wt);
    J := Transpose(StarInvolution(C));
    Cplus := Kernel(Transpose(J-1));
    GFS := get_gamma_fixed_space(eps_gens, gs);
    numrels := Dimension(GFS) div 2 + 2;
    prec := Maximum(prec, numrels + 1);
    Tr_mats, Tr_ims, B_mats, deg_divs,
    num_coset_reps, oldspaces_full,
    oldspaces, C_old_new := get_old_spaces(MS);
    NN, Nold, Nnew, as, nfd, nfd_old, Tpluslist, primes, prec :=
	compute_newforms(C, C_old_new, prec, N);
    field_embs, cc, Ps_Q_huge, SKpowersQ_L,
    Q_huge, Q_L, zeta_huge, zeta_K,
    Q_K_plus_to_Q_K, Q_K_to_Q_huge,
    Q_L_to_Q_huge, ds,
    Q_gcd, zeta_gcd, Q_gcd_to_Q_K,
    gcd_fields, gcd_field_embs := createFieldEmbeddings(K, NN, C, ds);
    X, char_reps, chis := prepare_character_representatives(K);
    a_idxs, as := restrict_to_character_reps(nfd, nfd_old, as, X, char_reps, K);
    gcd_fields := [* gcd_fields[i] : i in a_idxs *];
    gcd_field_embs := [* gcd_field_embs[i] : i in a_idxs *];
    Kf_to_KKs := [* field_embs[i] : i in a_idxs *];    
    Pds := get_aut_extensions(Ps_Q_huge, Q_huge);
    return as, primes, Tpluslist, Kf_to_KKs, prec,
			     GFS, Bmats, Pds, ds,
			     cc, NN, Nold,
			     oldspaces_full,
			     oldspaces,
			     C, Cplus, chis,
			     Q_huge, Q_L, zeta_huge, zeta_K,
			     SKpowersQ_L,
			     B_mats,
			     Tr_mats,
			     deg_divs,
			     num_coset_reps, J,
			     Q_K_plus_to_Q_K, Q_K_to_Q_huge, Q_L_to_Q_huge,
			     Q_gcd, zeta_gcd, Q_gcd_to_Q_K, Nnew, eps_BPd_gens,
			     gcd_fields, gcd_field_embs;
end function;

function get_twist_orbit(i, as, primes, Tpluslist,
			       Kf_to_KKs, prec,
			       GFS,
			       cc, NN, Nold,
			       oldspaces_full,
			       oldspaces,
			       C, Cplus, chis,
			       zeta_huge, zeta_K,
			       SKpowersQ_L,
			       B_mats,
			       Tr_mats,
			       deg_divs,
			       num_coset_reps,
			       Q_L_to_Q_huge,
			       Nnew)
    assert prec ge #as + 1;
    Q_K := Parent(zeta_K);
    Q_huge := Parent(zeta_huge);
    K := CyclotomicOrder(Q_K);
    FCF := [];
    twist_orbit_indices := [];
    already_visited := {};
    KK_aps := [*[Kf_to_KKs[j](aps[j]) : aps in as] : j in [1..#as[1]]*];
    fs := [];
    while (i in already_visited) do
	i +:= 1;
    end while;
    vprintf ModularCurves, 1 : "Computing twist orbit no. %o out of %o\n", i, #as[1];
    alist := [aps[i] : aps in as];
    Kf_to_KK := Kf_to_KKs[i];
    Kf := Domain(Kf_to_KK);
    KK := Codomain(Kf_to_KK);
    Q_huge_to_KK := hom<Q_huge->KK | KK!zeta_huge>;
    real_twist_orbit_ms, twist_mfs, powerlist :=
	make_real_twist_orbit(alist, primes, Kf_to_KK, Tpluslist,
			      prec, cc, NN, Nold,
			      oldspaces_full, oldspaces,
			      C, Cplus, chis,
			      Q_huge, zeta_K,
			      K, SKpowersQ_L,
			      B_mats,
			      Tr_mats,
			      deg_divs,
			      num_coset_reps,
			      Q_L_to_Q_huge, Nnew);
    twist_all_aps := [* *];
    for twist_mf in twist_mfs do
	nonzero := exists(pivot){pivot : pivot in [1..#twist_mf]
				 | twist_mf[pivot] ne 0};
	if nonzero then
	    twist_aps := [x/twist_mf[pivot] : x in twist_mf];
	else
	    twist_aps := twist_mf;
	end if;
	Append(~twist_all_aps, twist_aps);
	inlist := exists(j){j : j in [1..#as[1]] |
			    BaseRing(Universe(KK_aps[j])) eq
			    BaseRing(Universe(twist_aps)) and
			    &and[MinimalPolynomial(KK_aps[j][l]) eq
				 MinimalPolynomial(twist_aps[l]) : l in [1..Min(#as, prec-1)]]};
	if inlist then
	    Include(~already_visited, j);
	end if;
    end for;
    twist_orbit_index := [];
    FCF_orbit := [];
    fixed_space_basis := Basis(ChangeRing(GFS, Kf)
					 meet real_twist_orbit_ms);
    dim_orbit := Dimension(real_twist_orbit_ms);
    vprintf ModularCurves, 1 : "Dimension of orbit is %o\n", dim_orbit;
    return real_twist_orbit_ms, fixed_space_basis,
	   dim_orbit, twist_all_aps, powerlist, twist_mfs;
end function;
	
function get_fb(i, real_twist_orbit_ms, fixed_space_basis,
		Q_L, Q_K_to_Q_huge, Kf_to_KKs, dim_orbit,
		gcd_fields, gcd_field_embs)

    Kf_to_KK := Kf_to_KKs[i];
    Kf := Domain(Kf_to_KK);
    Q_gcd<zeta_gcd> := gcd_fields[i];
    Q_gcd_to_Kf := gcd_field_embs[i][1];
    Q_gcd_to_Q_K := gcd_field_embs[i][2];
    Q_K<zeta_K> := Domain(Q_K_to_Q_huge);
    K := CyclotomicOrder(Q_K);
    fixed_basis_cfs :=
    [Eltseq(Solution(BasisMatrix(real_twist_orbit_ms), mu))
     : mu in fixed_space_basis];
	    
    coeffs_zeta := [[coeffs_by_zeta(b, Q_gcd, Q_L, Q_gcd_to_Kf) : b in b_imgs]
		    : b_imgs in fixed_basis_cfs];
    zeta_to_Q_K := [[Vector(Kf,Eltseq(Q_gcd_to_Q_K(zeta_gcd)^i
				      *zeta_K^r))
		     : i in [0..Degree(Q_gcd)-1]]
		    : r in [0..EulerPhi(K)-1]];
    fb_imgs_tr := [[[&+[cz[l][i+1]*zeta_to_Q_K[r+1][i+1]
			: i in [0..Degree(Q_gcd)-1]]
		     : l in [1..dim_orbit]]
		    : r in [0..EulerPhi(K)-1]]
		   : cz in coeffs_zeta];
    fb_imgs_block := [Matrix([Vector(Eltseq(Transpose(Matrix(fb_img_tr[r+1]))))
			      : fb_img_tr in fb_imgs_tr])
		      : r in [0..EulerPhi(K)-1]];
    fixed_basis_block := VerticalJoin(fb_imgs_block);
    fixed_ms_space_QQ := VectorSpace(Kf,EulerPhi(K)*#fixed_space_basis);
    return fixed_basis_block, Q_gcd_to_Kf,
	   zeta_to_Q_K, fixed_basis_cfs;
end function;

function find_fixed_Bmat(k, Bmats, Pds, ds, Q_gcd_to_Kf,
			 zeta_to_Q_K, eps_BPd_gens,
			 fixed_basis_block,
			 fixed_space_basis,
			 powerlist,
			 real_twist_orbit_ms,
			 twist_all_aps, zeta_K,
			 Q_K_to_Q_huge,
			 Q_L_to_Q_huge,
			 dim_orbit, chis)
    Q_gcd := Domain(Q_gcd_to_Kf);
    Kf := Codomain(Q_gcd_to_Kf);
    Q_K := Parent(zeta_K);
    K := CyclotomicOrder(Q_K);
    Q_L := Domain(Q_L_to_Q_huge);
    Q_huge := Codomain(Q_L_to_Q_huge);
    Bmat := Bmats[k];
    Pd := Pds[k];
    d := ds[k];
    B_imgs := [mu*ChangeRing(Transpose(Bmat),Kf)
	       : mu in fixed_space_basis];
    B_imgs_cfs :=
	[Eltseq(Solution(BasisMatrix(real_twist_orbit_ms),
			 ChangeRing(mu,Kf))) : mu in B_imgs];
    
    coeffs_zeta := [[coeffs_by_zeta(b, Q_gcd, Q_L, Q_gcd_to_Kf) : b in b_imgs]
		    : b_imgs in B_imgs_cfs];
    B_imgs_tr := [[[&+[cz[l][i+1]*zeta_to_Q_K[r+1][i+1]
		       : i in [0..Degree(Q_gcd)-1]]
		    : l in [1..dim_orbit]]
		   : r in [0..EulerPhi(K)-1]]
		  : cz in coeffs_zeta];
    B_imgs_block := [Matrix([Vector(Eltseq(Transpose(Matrix(b_imgs_tr[r+1]))))
			     : b_imgs_tr in B_imgs_tr])
		     : r in [0..EulerPhi(K)-1]];
    B_imgs_block := VerticalJoin(B_imgs_block);
    
    perm_d := [Index(twist_all_aps, [Pd(x) : x in twist_ap])
	       : twist_ap in twist_all_aps];
    // Check that the Pd action does permute the basis elements
    assert Sort(perm_d) eq [1..dim_orbit];
    pd_mat := Pdmatrix(Pd,d,powerlist,chis, Q_L, Q_huge,
		       zeta_K, K, Q_L_to_Q_huge,Q_K_to_Q_huge,
		       perm_d);
    B_pd_mat := B_imgs_block * ChangeRing(pd_mat, Kf);
    B_pd_cfs := Solution(fixed_basis_block, B_pd_mat);
    I_mat := IdentityMatrix(Kf,EulerPhi(K)*#fixed_space_basis);
    fixed_B_pd := Kernel(B_pd_cfs - eps_BPd_gens[k]^(-1)*I_mat);
    return fixed_B_pd;
end function;

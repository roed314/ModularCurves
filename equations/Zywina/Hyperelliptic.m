// This is the simplest thing that only works for Q-rational cusps
function FindHyperellipticCurve(qexps, prec)
    R<q> := Universe(qexps);
    K := BaseRing(R);
    fs := [f + O(q^prec) : f in qexps];
    g := #fs;
    T, E := EchelonForm(Matrix([&cat[Eltseq(x)
				     : x in AbsEltseq(f)] : f in fs]));
    fs := [&+[E[j][i]*fs[i] : i in [1..g]] : j in [1..g]];
    x := fs[g-1] / fs[g];
    y := q * Derivative(x) / fs[g];
    mons := [x^i : i in [0..2*g+2]] cat [-y^2];
    denom := q^(-(2*g+2)*Valuation(x));
    f_mons := [denom*m + O(q^AbsolutePrecision(y)) : m in mons];
    ker := Kernel(Matrix([AbsEltseq(f : FixedLength) : f in f_mons]));
    assert Dimension(ker) eq 1;
    ker_b := Basis(ker)[1];
    ker_b /:= -ker_b[2*g+4];
    R<x> := PolynomialRing(K);
    poly := &+[ker_b[i+1]*x^i : i in [0..2*g+2]];
    X := HyperellipticCurve(-poly);
    return X, fs;
end function;

intrinsic HyperellipticCurve(X::Rec) -> Crv, RngSerPowElt, RngSerPowElt
{.}
  R<q> := Universe(X`F0[1]);
  K := BaseRing(R);
  assert exists(idx){i : i in [1..X`vinf] | Valuation(X`F0[#X`F0-1][i]) lt Valuation(X`F0[#X`F0][i])}; 
  g := X`genus;
  x := X`F0[#X`F0-1][idx] / X`F0[#X`F0][idx];
  _<q> := Parent(x);
  y := q * Derivative(x) / X`F0[#X`F0][idx];
  mons := [x^i : i in [0..2*g+2]] cat [-y^2];
  denom := q^(-(2*g+2)*Valuation(x));
  f_mons := [denom*m + O(q^AbsolutePrecision(y)) : m in mons];
  ker := Kernel(Matrix([AbsEltseq(f : FixedLength) : f in f_mons]));
  assert Dimension(ker) eq 1;
  ker_b := Basis(ker)[1];
  ker_b /:= -ker_b[2*g+4];
  R<x> := PolynomialRing(K);
  poly := &+[ker_b[i+1]*x^i : i in [0..2*g+2]];
  X := HyperellipticCurve(-poly);
  return X, x, y;
end intrinsic;

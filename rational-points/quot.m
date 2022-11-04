load "new_models.m";

N := 85;
p:=17;
bnd:=100; // bound on height




X, ws, pairs, NB, cusp := eqs_quos(N, [[p]]);
mp := pairs[1];
quot_curve := mp[1];
map_to_quot := mp[2];
quot_pts := PointSearch(quot_curve,bnd);

print quot_pts;

preimages := {@ @};


for p in quot_pts do

preimg := p @@ map_to_quot; //this should be a 0-dimensional scheme
print preimg;
preimg := BaseExtend(preimg, AlgebraicClosure(Rationals()));
pts_in := Points(preimg);
print pts_in;
for pt in pts_in do
  Include(~preimages, Eltseq(pt));
end for;
end for;
print preimages;
Magma V2.26-12    Tue Aug 30 2022 20:18:11 on euler    [Seed = 3753044178]
Type ? for help.  Type <Ctrl>-D to quit.

Loading file "X0(74).m"
Loading "new_models.m"
Loading "auxiliary.m"
Loading "Chabauty_MWSieve_new.m"
Loading "ChabautyHelp.m"
Loading "auxiliary.m"
Loading "rank_calcs.m"
Nice model for X_0(74) is: Curve over Rational Field defined by
x[1]^2 - x[5]^2 - 2*x[5]*x[7] + 8*x[6]^2 + 8*x[6]*x[7] - x[7]^2,
x[1]*x[2] + x[1]*x[4] - x[5]*x[8] - 2*x[6]*x[8] - x[7]*x[8],
x[1]*x[3] - x[6]*x[8] - 2*x[7]*x[8],
x[1]*x[5] - x[1]*x[7] - x[2]*x[8] - 2*x[3]*x[8] + x[4]*x[8],
x[1]*x[6] - x[3]*x[8] - 2*x[4]*x[8],
x[1]*x[8] - x[2]*x[5] + 2*x[3]*x[5] - 2*x[3]*x[7] + 2*x[4]*x[5] + 4*x[4]*x[6] - 
3*x[4]*x[7],
148*x[2]^2 - 123*x[5]^2 - 100*x[5]*x[6] + 190*x[5]*x[7] - 40*x[6]^2 + 
192*x[6]*x[7] + 81*x[7]^2 - 25*x[8]^2,
74*x[2]*x[3] - 5*x[5]^2 - 54*x[5]*x[6] - 38*x[5]*x[7] + 8*x[6]^2 + 80*x[6]*x[7] 
+ 43*x[7]^2 + 5*x[8]^2,
148*x[2]*x[4] + 5*x[5]^2 - 20*x[5]*x[6] - 110*x[5]*x[7] - 8*x[6]^2 - 
80*x[6]*x[7] - 43*x[7]^2 - 5*x[8]^2,
x[2]*x[6] - x[3]*x[5],
x[2]*x[7] - x[4]*x[5] + 2*x[4]*x[7],
37*x[3]^2 + x[5]^2 - 4*x[5]*x[6] - 22*x[5]*x[7] - 9*x[6]^2 - 16*x[6]*x[7] + 
21*x[7]^2 - x[8]^2,
74*x[3]*x[4] - x[5]^2 + 4*x[5]*x[6] + 22*x[5]*x[7] - 28*x[6]^2 - 58*x[6]*x[7] - 
21*x[7]^2 + x[8]^2,
2*x[3]*x[6] + x[3]*x[7] - 2*x[4]*x[5] - x[4]*x[6] + 2*x[4]*x[7],
148*x[4]^2 + x[5]^2 - 4*x[5]*x[6] + 126*x[5]*x[7] - 120*x[6]^2 - 16*x[6]*x[7] + 
21*x[7]^2 - x[8]^2

w_37 on X_0(74) is given by: Mapping from: Crv: XN to Crv: XN
with equations : 
x[1]
-x[2]
-x[3]
-x[4]
x[5]
x[6]
x[7]
-x[8]
and inverse
x[1]
-x[2]
-x[3]
-x[4]
x[5]
x[6]
x[7]
-x[8]
Genus of X_0(74) is 8
We have found these points on X_0(74):
[
Place at (1 : 1 : 0 : 0 : 1 : 0 : 0 : 1),
Place at (-1 : -1 : 0 : 0 : 1 : 0 : 0 : 1),
Place at (1 : -1 : 0 : 0 : -1 : 0 : 0 : 1),
Place at (-1 : 1 : 0 : 0 : -1 : 0 : 0 : 1)
]
(-1 : 0 : 0 : -1/7*r7 : -2/7*r7 : 2/7*r7 : -1/7*r7 : 1)
(1 : 0 : 0 : -1/7*r7 : 2/7*r7 : -2/7*r7 : 1/7*r7 : 1)
We have found 12 points on X_0(74)^2(Q).
Genus of X_0(74)/w37 is 4.
p = 3 (1/10): Getting deg 1 places on Xp...
Getting deg 2 places on Xp...
Combining them into divisors...
There are  30  of them!
out of 27: ...........................The number of possible cosets unknown points can land in is 13.
p = 5 (2/10): Getting deg 1 places on Xp...
Getting deg 2 places on Xp...
Combining them into divisors...
There are  84  of them!
out of 13: .............The number of possible cosets unknown points can land in is 1.

For unknown Q in X_0(74)^2(Q) we have (1 - w_37)[Q - bp] is in a coset of 
Abelian Group of order 1 represented by an element of [
0
].
It follows that if there is an unknown Q in X_0(74)^2(Q), then (1 - w_37)[Q - 
bp] == 0.
This implies that [Q - bp] is fixed by w_37
Then Q ~ w_37(Q), which implies that Q = w_37(Q) because X_0(74) is not 
hyperelliptic.
Then either Q is a pullback, or it is fixed by w_37 pointwise.
If P = (X_i) is fixed by w_37,
either the coordinates at indices 2, 3, 4, 8 are 0 or the other 4 coordinates 
are 0

We find all such P by imposing these conditions and finding points on the 
scheme:
Scheme over Rational Field defined by
x[1]^2,
x[1]*x[2],
x[2]^2 - 25/148*x[8]^2,
x[1]*x[3],
x[2]*x[3] + 5/74*x[8]^2,
x[3]^2 - 1/37*x[8]^2,
x[1]*x[4],
x[2]*x[4] - 5/148*x[8]^2,
x[3]*x[4] + 1/74*x[8]^2,
x[4]^2 - 1/148*x[8]^2,
x[1]*x[5] - x[1]*x[7],
x[2]*x[5],
x[3]*x[5],
x[4]*x[5],
x[5]^2,
x[1]*x[6],
x[2]*x[6],
x[3]*x[6],
x[4]*x[6],
x[5]*x[6],
x[6]^2,
x[2]*x[7],
x[3]*x[7],
x[4]*x[7],
x[5]*x[7],
x[6]*x[7],
x[7]^2,
x[1]*x[8],
x[2]*x[8] - 5*x[4]*x[8],
x[3]*x[8] + 2*x[4]*x[8],
x[5]*x[8],
x[6]*x[8],
x[7]*x[8]

All such P are:
{@ (0 : 5*r1 : -2*r1 : r1 : 0 : 0 : 0 : 1), (0 : 5*r2 : -2*r2 : r2 : 0 : 0 : 0 :
1) @}
The degrees of these points are [ 2, 2 ] (or > 2).
Apart from pullbacks of rational points on X_0(74)/w37, we have these quadratic 
points on X_0(74):(-1 : 0 : 0 : -1/7*r7 : -2/7*r7 : 2/7*r7 : -1/7*r7 : 1)
(1 : 0 : 0 : -1/7*r7 : 2/7*r7 : -2/7*r7 : 1/7*r7 : 1)
{@ (0 : 5*r1 : -2*r1 : r1 : 0 : 0 : 0 : 1), (0 : 5*r2 : -2*r2 : r2 : 0 : 0 : 0 :
1) @}

Total time: 471.060 seconds, Total memory usage: 192.25MB

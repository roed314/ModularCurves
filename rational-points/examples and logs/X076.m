// rank 0
N := 76;
//n := Integers() ! (N/2);

load "quadPts.m";

SetDebugOnError(true);

time quadPts(N, 7 : additionalBadPrimes := [3]);
//time quadPts(N, n, 20 : additionalBadPrimes := [2,3,5]);
